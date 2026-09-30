-- Prove2me | solution 1 for UnderstandingML.soa_mistake_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:30:02.034776+00:00
-- url     : https://prove2.me/submissions/ece565fa-c9bd-4e0f-90f5-ca5a8e618b84


import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section Potential

variable {X Y : Type*}

theorem versionSpace_nil (H : Set (X → Y)) : versionSpace H [] = H := by
  ext g; simp [versionSpace]

theorem versionSpace_append_singleton (H : Set (X → Y)) (hist : List (X × Y)) (e : X × Y) :
    versionSpace H (hist ++ [e]) = versionSpace H hist ∩ {g | g e.1 = e.2} := by
  ext g
  simp only [versionSpace, List.mem_append, List.mem_singleton, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨⟨hg, fun e' he' ↦ h e' (Or.inl he')⟩, h e (Or.inr rfl)⟩
  · rintro ⟨⟨hg, h⟩, he⟩
    refine ⟨hg, fun e' he' ↦ ?_⟩
    rcases he' with he' | rfl
    · exact h e' he'
    · exact he

theorem history_eq_ofFn_castSucc {n : ℕ} (S : Fin (n + 1) → X × Y) :
    history S n = List.ofFn (fun i : Fin n ↦ S i.castSucc) := by
  unfold history
  rw [List.ofFn_succ', List.concat_eq_append, List.take_append_of_le_length (by simp)]
  simp

theorem history_castSucc {n : ℕ} (S : Fin (n + 1) → X × Y) (t : ℕ) (ht : t ≤ n) :
    history (fun i : Fin n ↦ S i.castSucc) t = history S t := by
  unfold history
  rw [List.ofFn_succ' S, List.concat_eq_append, List.take_append_of_le_length (by simpa using ht)]

theorem mistakes_succ [DecidableEq Y] (A : OnlineAlg X Y) {n : ℕ} (S : Fin (n + 1) → X × Y) :
    mistakes A S = mistakes A (fun i : Fin n ↦ S i.castSucc) +
      if A (List.ofFn (fun i : Fin n ↦ S i.castSucc)) (S (Fin.last n)).1 ≠ (S (Fin.last n)).2
      then 1 else 0 := by
  unfold mistakes
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [history_castSucc S i (by omega)]
    rfl
  · rw [← history_eq_ofFn_castSucc]
    rfl

/-- The potential method for mistake bounds: if a potential `Φ` of the version space drops by
at least one on every mistake and never increases, then the number of mistakes plus the final
potential is at most the initial potential `Φ H`. -/
theorem mistakes_add_potential_le [DecidableEq Y] (A : OnlineAlg X Y) (H : Set (X → Y))
    (h : X → Y) (Φ : Set (X → Y) → ℕ∞)
    (hstep : ∀ (hist : List (X × Y)) (x : X), h ∈ versionSpace H hist →
      ((if A hist x ≠ h x then 1 else 0 : ℕ) : ℕ∞) +
        Φ (versionSpace H (hist ++ [(x, h x)])) ≤ Φ (versionSpace H hist)) :
    ∀ (n : ℕ) (x : Fin n → X), h ∈ H →
      (mistakes A (fun t ↦ (x t, h (x t))) : ℕ∞) +
        Φ (versionSpace H (List.ofFn (fun t ↦ (x t, h (x t))))) ≤ Φ H := by
  intro n
  induction n with
  | zero =>
    intro x _
    simp [mistakes, versionSpace_nil]
  | succ n ih =>
    intro x hh
    have ih' := ih (fun i ↦ x i.castSucc) hh
    rw [mistakes_succ]
    have hmem : h ∈ versionSpace H (List.ofFn (fun i : Fin n ↦ (x i.castSucc, h (x i.castSucc)))) := by
      refine ⟨hh, fun e he ↦ ?_⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      rfl
    have hs := hstep _ (x (Fin.last n)) hmem
    have hlist : List.ofFn (fun t : Fin (n + 1) ↦ (x t, h (x t))) =
        List.ofFn (fun i : Fin n ↦ (x i.castSucc, h (x i.castSucc))) ++
          [(x (Fin.last n), h (x (Fin.last n)))] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    rw [hlist, Nat.cast_add, add_assoc]
    exact le_trans (add_le_add le_rfl hs) ih'

/-- A potential argument bounds the mistake bound `M_A(H)`. -/
theorem mistakeBound_le_of_potential [DecidableEq Y] (A : OnlineAlg X Y) (H : Set (X → Y))
    (Φ : Set (X → Y) → ℕ∞)
    (hstep : ∀ h ∈ H, ∀ (hist : List (X × Y)) (x : X), h ∈ versionSpace H hist →
      ((if A hist x ≠ h x then 1 else 0 : ℕ) : ℕ∞) +
        Φ (versionSpace H (hist ++ [(x, h x)])) ≤ Φ (versionSpace H hist)) :
    mistakeBound A H ≤ Φ H := by
  unfold mistakeBound
  refine iSup_le fun T ↦ iSup_le fun x ↦ iSup_le fun h ↦ iSup_le fun hh ↦ ?_
  exact le_trans le_self_add
    (mistakes_add_potential_le A H h Φ (hstep h hh) T x hh)

end Potential
section Littlestone

variable {X : Type*}

theorem ShattersTree.mono {V W : Set (X → Bool)} (hVW : V ⊆ W) {d : ℕ} {v : List Bool → X}
    (h : ShattersTree V d v) : ShattersTree W d v := by
  intro y
  obtain ⟨g, hg, hgy⟩ := h y
  exact ⟨g, hVW hg, hgy⟩

theorem ldim_mono {V W : Set (X → Bool)} (hVW : V ⊆ W) : ldim V ≤ ldim W := by
  unfold ldim
  refine iSup₂_le fun d hd ↦ ?_
  obtain ⟨v, hv⟩ := hd
  exact le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree W d v) ↦ (d : ℕ∞))
    d ⟨v, hv.mono hVW⟩

theorem le_ldim_of_shatters {V : Set (X → Bool)} {d : ℕ} {v : List Bool → X}
    (h : ShattersTree V d v) : (d : ℕ∞) ≤ ldim V :=
  le_iSup₂ (f := fun (d : ℕ) (_ : ∃ v : List Bool → X, ShattersTree V d v) ↦ (d : ℕ∞)) d ⟨v, h⟩

/-- If `Ldim(V) = n` is finite and `V` is nonempty, a shattered tree of depth `n` exists. -/
theorem exists_shatters_of_ldim_eq {V : Set (X → Bool)} (hV : V.Nonempty) (x : X) {n : ℕ}
    (hn : ldim V = n) : ∃ v : List Bool → X, ShattersTree V n v := by
  have h0 : ∃ v : List Bool → X, ShattersTree V 0 v := by
    refine ⟨fun _ ↦ x, fun y ↦ ?_⟩
    obtain ⟨g, hg⟩ := hV
    exact ⟨g, hg, fun t ↦ t.elim0⟩
  have hlt : (⨆ (d : ℕ), ⨆ (_ : ∃ v : List Bool → X, ShattersTree V d v), (d : ℕ∞)) < ⊤ := by
    change ldim V < ⊤
    rw [hn]; exact ENat.coe_lt_top n
  obtain ⟨d, hd⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  change _ = ldim V at hd
  rw [hn] at hd
  by_cases hP : ∃ v : List Bool → X, ShattersTree V d v
  · rw [iSup_pos hP] at hd
    have : d = n := by exact_mod_cast hd
    subst this; exact hP
  · rw [iSup_neg hP, bot_eq_zero] at hd
    have : n = 0 := by exact_mod_cast hd.symm
    subst this; exact h0

/-- Gluing two shattered trees of depth `d` for `V ∩ {h | h x = 0}` and `V ∩ {h | h x = 1}`
under a new root `x` yields a shattered tree of depth `d + 1` for `V`. -/
theorem shatters_glue {V : Set (X → Bool)} (x : X) {d : ℕ} {v0 v1 : List Bool → X}
    (h0 : ShattersTree (V ∩ {g | g x = false}) d v0)
    (h1 : ShattersTree (V ∩ {g | g x = true}) d v1) :
    ShattersTree V (d + 1)
      (fun p ↦ match p with
        | [] => x
        | b :: q => if b then v1 q else v0 q) := by
  intro y
  have key : ∀ r : Bool, y 0 = r → ∃ g ∈ V, ∀ t : Fin (d + 1),
      g ((fun p ↦ match p with
        | [] => x
        | b :: q => if b then v1 q else v0 q)
        (List.ofFn (fun j : Fin (t : ℕ) ↦ y ⟨j, lt_trans j.2 t.2⟩))) = y t := by
    intro r hr
    obtain ⟨g, ⟨hgV, hgx⟩, hg⟩ : ∃ g ∈ V ∩ {g | g x = r}, ∀ t : Fin d,
        g ((if r then v1 else v0)
          (List.ofFn (fun j : Fin (t : ℕ) ↦ y (Fin.succ ⟨j, lt_trans j.2 t.2⟩)))) = y t.succ := by
      cases r
      · exact h0 (fun j ↦ y j.succ)
      · exact h1 (fun j ↦ y j.succ)
    refine ⟨g, hgV, fun t ↦ ?_⟩
    refine Fin.cases ?_ (fun s ↦ ?_) t
    · simp only [Fin.val_zero, List.ofFn_zero]
      rw [hr]
      exact hgx
    · have hs := hg s
      simp only [Fin.val_succ, List.ofFn_succ]
      have e1 : y ⟨((0 : Fin (s + 1)) : ℕ), lt_trans (0 : Fin (s + 1)).2 s.succ.2⟩ = r := by
        rw [← hr]; rfl
      rw [e1]
      convert hs using 3
      cases r <;> rfl
  exact key (y 0) rfl

theorem ldimBot_of_nonempty {V : Set (X → Bool)} (hV : V.Nonempty) :
    ldimBot V = (ldim V : WithBot ℕ∞) := by
  unfold ldimBot; rw [if_pos hV]

theorem ldimBot_of_empty {V : Set (X → Bool)} (hV : ¬ V.Nonempty) : ldimBot V = ⊥ := by
  unfold ldimBot; rw [if_neg hV]

/-- The SOA step: if SOA errs on `x` whose true label `b` is realized in the version space,
then the Littlestone dimension of the new version space drops by at least one. -/
theorem soa_step (V : Set (X → Bool)) (x : X) (b : Bool) (hne : (V ∩ {g | g x = b}).Nonempty)
    (herr : decide (ldimBot (V ∩ {h | h x = false}) ≤ ldimBot (V ∩ {h | h x = true})) ≠ b) :
    ldim (V ∩ {g | g x = b}) + 1 ≤ ldim V := by
  rcases (le_top : ldim V ≤ ⊤).eq_or_lt with htop | hfin
  · rw [htop]; exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hfin.ne
  have hn' : ldim V = (n : ℕ∞) := hn.symm
  have hmono : ∀ c : Bool, ldim (V ∩ {g | g x = c}) ≤ n := fun c ↦
    hn' ▸ ldim_mono Set.inter_subset_left
  by_contra hcon
  have hbn : ldim (V ∩ {g | g x = b}) = n := by
    have h1 := hmono b
    have hne' : ldim (V ∩ {g | g x = b}) ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top n) h1
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne'
    rw [← hk] at h1 hcon ⊢
    rw [hn'] at hcon
    have hkn : k ≤ n := by exact_mod_cast h1
    have hkn' : ¬ (k + 1 ≤ n) := by exact_mod_cast hcon
    exact_mod_cast (by omega : k = n)
  -- both restricted version spaces are nonempty with dimension `n`
  have hboth : (V ∩ {g | g x = false}).Nonempty ∧ (V ∩ {g | g x = true}).Nonempty ∧
      ldim (V ∩ {g | g x = false}) = n ∧ ldim (V ∩ {g | g x = true}) = n := by
    cases b with
    | false =>
      have hle : ldimBot (V ∩ {h | h x = false}) ≤ ldimBot (V ∩ {h | h x = true}) := by
        by_contra hc; exact herr (by simp [hc])
      rw [ldimBot_of_nonempty hne, hbn] at hle
      have hne1 : (V ∩ {h | h x = true}).Nonempty := by
        by_contra hc
        rw [ldimBot_of_empty hc] at hle
        exact absurd hle (by simp)
      rw [ldimBot_of_nonempty hne1] at hle
      have hle' : (n : ℕ∞) ≤ ldim (V ∩ {h | h x = true}) := by exact_mod_cast hle
      exact ⟨hne, hne1, hbn, le_antisymm (hmono true) hle'⟩
    | true =>
      have hlt : ldimBot (V ∩ {h | h x = true}) < ldimBot (V ∩ {h | h x = false}) := by
        by_contra hc; exact herr (by simp [not_lt.1 hc])
      rw [ldimBot_of_nonempty hne, hbn] at hlt
      have hne0 : (V ∩ {h | h x = false}).Nonempty := by
        by_contra hc
        rw [ldimBot_of_empty hc] at hlt
        exact absurd hlt (by simp)
      rw [ldimBot_of_nonempty hne0] at hlt
      have hlt' : (n : ℕ∞) < ldim (V ∩ {h | h x = false}) := by exact_mod_cast hlt
      exact absurd (hmono false) (not_le.2 hlt')
  obtain ⟨hne0, hne1, hd0, hd1⟩ := hboth
  obtain ⟨v0, hv0⟩ := exists_shatters_of_ldim_eq hne0 x hd0
  obtain ⟨v1, hv1⟩ := exists_shatters_of_ldim_eq hne1 x hd1
  have := le_ldim_of_shatters (shatters_glue x hv0 hv1)
  rw [hn'] at this
  have : n + 1 ≤ n := by exact_mod_cast this
  omega

theorem soa_mistake_bound_main {X : Type*} (H : Set (X → Bool)) :
    mistakeBound (soa H) H ≤ ldim H := by
  refine mistakeBound_le_of_potential (soa H) H ldim ?_
  intro h _ hist x hmem
  rw [versionSpace_append_singleton]
  set V := versionSpace H hist
  by_cases hm : soa H hist x ≠ h x
  · rw [if_pos hm, add_comm]
    exact_mod_cast soa_step V x (h x) ⟨h, hmem, rfl⟩ hm
  · rw [if_neg hm]
    simp only [Nat.cast_zero, zero_add]
    exact ldim_mono Set.inter_subset_left

end Littlestone

end UnderstandingML

open UnderstandingML

theorem solution {X : Type*} (H : Set (X → Bool)) :
    mistakeBound (soa H) H ≤ ldim H := by
  apply UnderstandingML.soa_mistake_bound_main <;> assumption
