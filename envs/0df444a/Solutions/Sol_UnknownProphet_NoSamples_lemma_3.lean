-- Prove2me | solution 1 for UnknownProphet.NoSamples.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:47:50.442764+00:00
-- url     : https://prove2.me/submissions/7a53f21a-bfef-42d8-be4c-d13c5001eaf8

import Mathlib
set_option autoImplicit false

theorem ramsey_aux {α : Type*} (c : ℕ) : ∀ d : ℕ, ∀ (W : Set α), W.Infinite →
    ∀ χ : Finset α → Fin c, ∃ U : Set α, U ⊆ W ∧ U.Infinite ∧
      ∃ col : Fin c, ∀ A : Finset α, (A : Set α) ⊆ U → A.card = d → χ A = col := by
  classical
  intro d
  induction d with
  | zero =>
    intro W hW χ
    refine ⟨W, subset_rfl, hW, χ ∅, ?_⟩
    intro A _ hA
    rw [Finset.card_eq_zero] at hA
    rw [hA]
  | succ d ih =>
    intro W0 hW0 χ
    have step : ∀ T : {W : Set α // W.Infinite}, ∃ a : α, ∃ T' : {W : Set α // W.Infinite},
        ∃ col : Fin c, a ∈ T.1 ∧ T'.1 ⊆ T.1 \ {a} ∧
          ∀ B : Finset α, (B : Set α) ⊆ T'.1 → B.card = d → χ (insert a B) = col := by
      rintro ⟨W, hW⟩
      obtain ⟨a, ha⟩ := hW.nonempty
      have hW' : (W \ {a}).Infinite := hW.diff (Set.finite_singleton a)
      obtain ⟨U, hU, hUi, col, hcol⟩ := ih (W \ {a}) hW' (fun B => χ (insert a B))
      exact ⟨a, ⟨U, hUi⟩, col, ha, hU, fun B hB hc => hcol B hB hc⟩
    choose P N C hP hN hC using step
    let S : ℕ → {W : Set α // W.Infinite} := fun n => Nat.rec ⟨W0, hW0⟩ (fun _ s => N s) n
    have hS : ∀ n, S (n+1) = N (S n) := fun n => rfl
    let a : ℕ → α := fun n => P (S n)
    let col : ℕ → Fin c := fun n => C (S n)
    have ha_mem : ∀ n, a n ∈ (S n).1 := fun n => hP (S n)
    have hmono : ∀ m n, m ≤ n → (S n).1 ⊆ (S m).1 := by
      intro m n h
      induction n, h using Nat.le_induction with
      | base => exact subset_rfl
      | succ k _ ih =>
        intro x hx
        have hx' : x ∈ (N (S k)).1 := hx
        exact ih (hN (S k) hx').1
    have hlt : ∀ m n, m < n → a n ∈ (S (m+1)).1 ∧ a n ≠ a m := by
      intro m n h
      have h1 : a n ∈ (S (m+1)).1 := hmono (m+1) n h (ha_mem n)
      refine ⟨h1, ?_⟩
      intro heq
      exact (hN (S m) h1).2 heq
    have hinj : Function.Injective a := by
      intro m n h
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact (hlt m n h').2 h.symm
      · exact (hlt n m h').2 h
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber col
    have hfib : (col ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
    refine ⟨a '' (col ⁻¹' {y}), ?_, hfib.image hinj.injOn, y, ?_⟩
    · rintro _ ⟨n, -, rfl⟩
      exact hmono 0 n (Nat.zero_le n) (ha_mem n)
    · intro T hTU hcard
      have hne : T.Nonempty := by rw [← Finset.card_pos]; omega
      obtain ⟨x0, hx0, hmin⟩ := Finset.exists_min_image T (Function.invFun a) hne
      obtain ⟨n, hn, hnx⟩ := hTU hx0
      have hn' : col n = y := hn
      have hgn : Function.invFun a x0 = n := by
        rw [← hnx]; exact Function.leftInverse_invFun hinj n
      have hBsub : ((T.erase x0 : Finset α) : Set α) ⊆ (S (n+1)).1 := by
        intro z hz
        have hz' : z ∈ T.erase x0 := hz
        rw [Finset.mem_erase] at hz'
        obtain ⟨m, hm, hmz⟩ := hTU hz'.2
        have hgm : Function.invFun a z = m := by
          rw [← hmz]; exact Function.leftInverse_invFun hinj m
        have h1 : n ≤ m := by
          have := hmin z hz'.2
          rwa [hgn, hgm] at this
        have h2 : n ≠ m := by
          rintro rfl
          exact hz'.1 (by rw [← hmz, hnx])
        subst hmz
        exact hmono (n+1) m (by omega) (ha_mem m)
      have key := hC (S n) (T.erase x0) hBsub (by rw [Finset.card_erase_of_mem hx0]; omega)
      have hins : insert (P (S n)) (T.erase x0) = T := by
        have e : P (S n) = x0 := hnx
        rw [e]; exact Finset.insert_erase hx0
      rw [hins] at key
      exact key.trans hn'

theorem solution {α : Type*} (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (W : Set α) (hW : W.Infinite) (χ : Finset α → Fin c) :
    ∃ U : Set α, U ⊆ W ∧ U.Infinite ∧
      ∃ col : Fin c, ∀ A : Finset α, (A : Set α) ⊆ U → A.card = d → χ A = col := by
  exact ramsey_aux c d W hW χ
