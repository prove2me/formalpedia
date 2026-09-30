-- Prove2me | solution 1 for UnderstandingML.halving_mistake_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T13:28:50.450927+00:00
-- url     : https://prove2.me/submissions/974beb3c-cac8-4254-a75e-10461e3f0ae9


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

section Halving

variable {X : Type*}

/-- The halving step: if Halving errs on `x` with true label `b`, the new version space has at
most half the size of the old one. -/
theorem halving_step (V : Set (X → Bool)) (hV : V.Finite) (x : X) (b : Bool)
    (hb : decide ((V ∩ {h | h x = false}).ncard ≤ (V ∩ {h | h x = true}).ncard) ≠ b) :
    2 * (V ∩ {g | g x = b}).ncard ≤ V.ncard := by
  have hsplit : (V ∩ {h | h x = false}).ncard + (V ∩ {h | h x = true}).ncard = V.ncard := by
    have := Set.ncard_inter_add_ncard_diff_eq_ncard V {h : X → Bool | h x = false} hV
    rw [← this]
    congr 2
    ext g
    simp
  cases b with
  | false =>
    have : (V ∩ {h | h x = false}).ncard ≤ (V ∩ {h | h x = true}).ncard := by
      by_contra hc; exact hb (by simp [hc])
    omega
  | true =>
    have : ¬ (V ∩ {h | h x = false}).ncard ≤ (V ∩ {h | h x = true}).ncard := by
      intro hc; exact hb (by simp [hc])
    omega

theorem halving_mistake_bound_main {X : Type*} (H : Set (X → Bool)) (hH : H.Finite) :
    mistakeBound (halving H) H ≤ (Nat.log 2 H.ncard : ℕ∞) := by
  have key := mistakeBound_le_of_potential (halving H) H (fun V ↦ (Nat.log 2 V.ncard : ℕ∞))
  refine key ?_
  intro h _ hist x hmem
  rw [versionSpace_append_singleton]
  simp only
  set V := versionSpace H hist
  have hVfin : V.Finite := hH.subset (fun g hg ↦ hg.1)
  have hVn : (V ∩ {g | g x = h x}).Nonempty := ⟨h, hmem, rfl⟩
  have hpos : (V ∩ {g | g x = h x}).ncard ≠ 0 :=
    (Set.ncard_pos (hVfin.subset Set.inter_subset_left)).2 hVn |>.ne'
  by_cases hm : halving H hist x ≠ h x
  · rw [if_pos hm]
    have h2 := halving_step V hVfin x (h x) hm
    have hlog : Nat.log 2 (V ∩ {g | g x = h x}).ncard + 1 ≤ Nat.log 2 V.ncard := by
      rw [← Nat.log_mul_base (by norm_num) hpos]
      exact Nat.log_mono_right (by omega)
    rw [add_comm]
    exact_mod_cast hlog
  · rw [if_neg hm]
    simp only [Nat.cast_zero, zero_add, Nat.cast_le]
    exact Nat.log_mono_right (Set.ncard_le_ncard Set.inter_subset_left hVfin)

end Halving

end UnderstandingML

open UnderstandingML

theorem solution {X : Type*} (H : Set (X → Bool)) (hH : H.Finite) :
    mistakeBound (halving H) H ≤ (Nat.log 2 H.ncard : ℕ∞) := by
  apply UnderstandingML.halving_mistake_bound_main <;> assumption
