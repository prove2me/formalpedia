-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.agreement_lemma_or
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:38:28.854134+00:00
-- url     : https://prove2.me/submissions/72c5fd3c-f203-402e-a6fe-4f406176c572

import Mathlib
import Theorems.Thm_SymmetricPSM1041_ORLowerBound_finite_higman_length_bound
import Theorems.Thm_SymmetricPSM1041_ORLowerBound_iterated_finite_ramsey

open SymmetricPSM1041.ORLowerBound

theorem solution (k : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (Alphabet : Type*) [Fintype Alphabet], Fintype.card Alphabet = k →
      ∀ n : ℕ, N ≤ n →
      ∀ α : (S : Finset (Fin n)) → S.Nonempty → (i : Fin n) → i ∈ S → Alphabet,
      ∃ T S : Finset (Fin n), ∃ hT : T.Nonempty, ∃ hS : S.Nonempty,
        ∃ hTS : T ⊂ S, ∀ (i : Fin n) (hi : i ∈ T),
          α T hT i hi = α S hS i ((le_of_lt hTS) hi) := by
  classical
  obtain ⟨m, hm, hHigman⟩ := finite_higman_length_bound (Fin k)
  obtain ⟨N, hmN, hRamsey⟩ := iterated_finite_ramsey (Fin k) m hm
  refine ⟨N, hm.trans hmN, ?_⟩
  intro Alphabet _ hcard n hN α
  let e : Alphabet ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let inc : Fin N ↪o Fin n := Fin.castLEOrderEmb hN
  let c : (q : ℕ) → 1 ≤ q → q ≤ m →
      {S : Finset (Fin N) // S.card = q} → (Fin q → Fin k) :=
    fun q hq _ S a => e (α
      (S.1.map inc.toEmbedding)
      (by
        apply Finset.card_pos.mp
        simpa [S.2] using (show 0 < q by omega))
      (inc (S.1.orderEmbOfFin S.2 a))
      (by simp))
  obtain ⟨H, hHcard, hHom⟩ := hRamsey c
  have hword (i : Fin m) : ∃ word : Fin (i.val + 1) → Fin k,
      ∀ (S : Finset (Fin N)) (hS : S.card = i.val + 1), S ⊆ H →
        c (i.val + 1) (by omega) (by omega) ⟨S, hS⟩ = word :=
    hHom (i.val + 1) (by omega) (by omega)
  let v (i : Fin m) : Fin (i.val + 1) → Fin k := (hword i).choose
  let w (i : Fin m) : List (Fin k) := List.ofFn (v i)
  have hwlen (i : Fin m) : (w i).length = i.val + 1 := by simp [w]
  obtain ⟨i, j, hij, hsub⟩ := hHigman w hwlen
  have hsub' : ∃ p : Fin (i.val + 1) ↪o Fin (j.val + 1),
      ∀ a, v i a = v j (p a) := by
    rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq] at hsub
    obtain ⟨p₀, hp₀⟩ := hsub
    let ei : Fin (i.val + 1) ≃o Fin (w i).length := Fin.castOrderIso (hwlen i).symm
    let ej : Fin (w j).length ≃o Fin (j.val + 1) := Fin.castOrderIso (hwlen j)
    let p : Fin (i.val + 1) ↪o Fin (j.val + 1) :=
      ei.toOrderEmbedding.trans p₀ |>.trans ej.toOrderEmbedding
    refine ⟨p, ?_⟩
    intro a
    have ha := hp₀ (ei a)
    calc
      v i a = (w i).get (ei a) := by
        simp only [w, List.get_ofFn]
        congr 1
      _ = (w j).get (p₀ (ei a)) := ha
      _ = v j (p a) := by
        simp only [w, List.get_ofFn]
        congr 1
  obtain ⟨p, hp⟩ := hsub'
  have hjm : j.val + 1 ≤ m := by omega
  let eS : Fin (j.val + 1) ↪o Fin N :=
    (Fin.castLEOrderEmb hjm).trans (H.orderEmbOfFin hHcard)
  let eT : Fin (i.val + 1) ↪o Fin N := p.trans eS
  let S₀ : Finset (Fin N) := Finset.univ.map eS.toEmbedding
  let T₀ : Finset (Fin N) := Finset.univ.map eT.toEmbedding
  have hS₀card : S₀.card = j.val + 1 := by simp [S₀]
  have hT₀card : T₀.card = i.val + 1 := by simp [T₀]
  have hS₀H : S₀ ⊆ H := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
    exact (H.orderEmbOfFin_mem hHcard (Fin.castLE hjm a))
  have hT₀S₀ : T₀ ⊆ S₀ := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.mem_map.2 ⟨p a, Finset.mem_univ _, rfl⟩
  have hT₀S₀' : T₀ ⊂ S₀ := Finset.ssubset_iff_subset_ne.2 ⟨hT₀S₀, by
    intro heq
    have hc := congrArg Finset.card heq
    rw [hT₀card, hS₀card] at hc
    omega⟩
  have horderS : S₀.orderEmbOfFin hS₀card = eS :=
    (Finset.orderEmbOfFin_unique' hS₀card (f := eS)
      (fun a => Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩)).symm
  have horderT : T₀.orderEmbOfFin hT₀card = eT :=
    (Finset.orderEmbOfFin_unique' hT₀card (f := eT)
      (fun a => Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩)).symm
  have hcS : c (j.val + 1) (by omega) (by omega) ⟨S₀, hS₀card⟩ = v j :=
    (hword j).choose_spec S₀ hS₀card hS₀H
  have hcT : c (i.val + 1) (by omega) (by omega) ⟨T₀, hT₀card⟩ = v i :=
    (hword i).choose_spec T₀ hT₀card (hT₀S₀.trans hS₀H)
  let S : Finset (Fin n) := S₀.map inc.toEmbedding
  let T : Finset (Fin n) := T₀.map inc.toEmbedding
  have hTS : T ⊂ S := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
      exact Finset.mem_map.2 ⟨a, hT₀S₀ ha, rfl⟩
    intro heq
    apply hT₀S₀'.ne
    exact Finset.map_injective inc.toEmbedding heq
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hc : T.card = 0 := by simp [he]
    simp [T, hT₀card] at hc
  have hSne : S.Nonempty := hTne.mono (le_of_lt hTS)
  refine ⟨T, S, hTne, hSne, hTS, ?_⟩
  intro x hxT
  obtain ⟨y, hyT₀, rfl⟩ := Finset.mem_map.1 hxT
  obtain ⟨a, -, hay⟩ := Finset.mem_map.1 hyT₀
  subst y
  apply e.injective
  calc
    e (α T hTne (inc (eT a)) (by simp [T, T₀]))
        = c (i.val + 1) (by omega) (by omega) ⟨T₀, hT₀card⟩ a := by
            simp [c, T, horderT]
    _ = v i a := congrFun hcT a
    _ = v j (p a) := hp a
    _ = c (j.val + 1) (by omega) (by omega) ⟨S₀, hS₀card⟩ (p a) :=
      (congrFun hcS (p a)).symm
    _ = e (α S hSne (inc (eT a)) (by simp [S, S₀, eT, eS])) := by
      simp [c, S, horderS, eT]
