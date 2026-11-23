-- Prove2me | solution 1 for TwoStageMatch.realizationwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T10:16:21.736717+00:00
-- url     : https://prove2.me/submissions/29ee5364-8456-44c3-ae4c-94554a317fe7

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_DualAssignment
import Theorems.Thm_TwoStageMatch_lp1_duality
import Theorems.Thm_TwoStageMatch_type_I_feasibility
import Theorems.Thm_TwoStageMatch_type_II_feasibility
import Theorems.Thm_TwoStageMatch_dual_objective_identity

open Finset

namespace TSMRealization

open TwoStageMatch

set_option linter.unusedSectionVars false

variable {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]

theorem levelSlack_nonneg (w : S → ℝ) (hw : ∀ j, 0 ≤ w j) (x : D₁ → S → ℝ)
    (hx : ∀ j, ∑ i, x i j ≤ 1) (l : Level x) : 0 ≤ levelSlack w x l := by
  cases l with
  | none => simp [levelSlack]
  | some K =>
    simp only [levelSlack]
    split_ifs with h
    · exact mul_nonneg (hw _) (sub_nonneg.2 (hx _))
    · exact le_rfl

/-- The bound for an instance with all weights positive. -/
theorem pos_case (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g)
    (hgm : Monotone g) (hgc : StrictConvexOn ℝ Set.univ g) (hw : ∀ j, 0 < I.w j)
    (r : Run I g) (A : Finset D₂) :
    (3 / 4 : ℝ) * maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ ≤
      ∑ M, r.ρ M * twoStageWeight I M A := by
  have hw0 : ∀ j, 0 ≤ I.w j := fun j => (hw j).le
  have hdual : ∀ M : Finset ((D₁ ⊕ D₂) × S), ∃ (α : D₁ ⊕ D₂ → ℝ) (β : S → ℝ),
      IsDualFeasible I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) α β ∧
      dualObj (secondStage A) (Finset.univ \ matchedSupply M) α β =
        maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) :=
    fun M => (lp1_duality I.E I.w hw0 _ _).2.1
  choose αh βh hopt using hdual
  have hdo := (dual_objective_identity I g hgd hgm hgc hw r A αh βh (fun M _ => hopt M)).2
  have hρ0 := r.ρ_rounding.1
  have hρ1 := r.ρ_rounding.2.1
  have hρM := r.ρ_rounding.2.2.1
  set X : Finset (D₁ ⊕ D₂) := firstStage ∪ secondStage A with hX
  set α' : D₁ ⊕ D₂ → ℝ := fun u => ∑ M, r.ρ M * dualAlpha I r.x (αh M) u with hα'
  set β' : S → ℝ := fun j => ∑ M, r.ρ M * dualBeta I r.x M (βh M) j with hβ'
  have hobj : dualObj X Finset.univ α' β' = ∑ M, r.ρ M * dualObj X Finset.univ
      (dualAlpha I r.x (αh M)) (dualBeta I r.x M (βh M)) := by
    simp only [dualObj, hα', hβ', mul_add, sum_add_distrib, mul_sum]
    rw [Finset.sum_comm (s := X), Finset.sum_comm (s := (Finset.univ : Finset S))]
  have hload : ∀ j, ∑ i, r.x i j ≤ 1 := r.x_opt.1.2.2.2
  have hfeas : IsDualFeasible I.E I.w X Finset.univ (fun u => 4 / 3 * α' u)
      (fun j => 4 / 3 * β' j) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      refine mul_nonneg (by norm_num) (sum_nonneg fun M _ => mul_nonneg (hρ0 M) ?_)
      rcases mem_union.1 hu with h | h
      · obtain ⟨i, -, rfl⟩ := mem_image.1 h
        exact levelSlack_nonneg _ hw0 _ hload _
      · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
        exact (hopt M).1.1 _ (mem_image_of_mem _ hi)
    · intro j _
      refine mul_nonneg (by norm_num) (sum_nonneg fun M _ => mul_nonneg (hρ0 M) ?_)
      simp only [dualBeta]
      refine add_nonneg (mul_nonneg (hw0 j) (sq_nonneg _)) ?_
      split_ifs with h
      · exact (hopt M).1.2.1 j h
      · exact le_rfl
    · intro u hu j _ hE
      have key : (3 / 4 : ℝ) * I.w j ≤ α' u + β' j := by
        rcases mem_union.1 hu with h | h
        · obtain ⟨i, -, rfl⟩ := mem_image.1 h
          have : ∑ M, r.ρ M * ((3 / 4 : ℝ) * I.w j) ≤
              ∑ M, r.ρ M * (dualAlpha I r.x (αh M) (Sum.inl i) + dualBeta I r.x M (βh M) j) := by
            refine sum_le_sum fun M _ => ?_
            by_cases h0 : r.ρ M = 0
            · simp [h0]
            · refine mul_le_mul_of_nonneg_left ?_ (hρ0 M)
              obtain ⟨h1, h2, h3, h4⟩ := type_I_feasibility I g hgd hgm hgc hw r A M (hρM M h0)
                (αh M) (βh M) (hopt M) i j hE
              linarith
          rw [← sum_mul, hρ1, one_mul] at this
          simpa [hα', hβ', mul_add, sum_add_distrib] using this
        · obtain ⟨i, hi, rfl⟩ := mem_image.1 h
          obtain ⟨h1, h2, h3⟩ := type_II_feasibility I g hgd hgm hgc hw r A αh βh
            (fun M _ => hopt M) i hi j hE
          have : ∑ M, r.ρ M * (I.w j * (if j ∈ Finset.univ \ matchedSupply M then 1 else 0) +
            I.w j * (load r.x j) ^ 2) ≤ α' (Sum.inr i) + β' j := by
            simpa [hα', hβ', mul_add, sum_add_distrib] using h1
          linarith
      linarith
  have hweak := (lp1_duality I.E I.w hw0 X Finset.univ).2.2 _ _ hfeas
  have hscale : dualObj X Finset.univ (fun u => 4 / 3 * α' u) (fun j => 4 / 3 * β' j) =
      4 / 3 * dualObj X Finset.univ α' β' := by
    simp only [dualObj, mul_add, mul_sum]
  rw [hscale, hobj, hdo] at hweak
  linarith

/-! ## Reduction from nonnegative to positive weights -/

/-- Remove every edge to a zero-weight supply and give such supplies weight `1`. -/
noncomputable def posInst (I : Instance D₁ D₂ S) : Instance D₁ D₂ S where
  E u j := I.E u j ∧ 0 < I.w j
  w j := if 0 < I.w j then I.w j else 1
  π := I.π
  w_nonneg j := by
    show 0 ≤ (if 0 < I.w j then I.w j else 1)
    split_ifs with h
    · exact h.le
    · norm_num
  π_nonneg := I.π_nonneg
  π_le_one := I.π_le_one

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] in
@[simp] theorem posInst_E (I : Instance D₁ D₂ S) (u : D₁ ⊕ D₂) (j : S) :
    (posInst I).E u j = (I.E u j ∧ 0 < I.w j) := rfl

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] in
@[simp] theorem posInst_w (I : Instance D₁ D₂ S) (j : S) :
    (posInst I).w j = if 0 < I.w j then I.w j else 1 := rfl

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] in
theorem posInst_w_pos (I : Instance D₁ D₂ S) (j : S) : 0 < (posInst I).w j := by
  rw [posInst_w]; split_ifs with h
  · exact h
  · norm_num

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] in
theorem w_eq_zero (I : Instance D₁ D₂ S) {j : S} (h : ¬ 0 < I.w j) : I.w j = 0 :=
  le_antisymm (not_lt.1 h) (I.w_nonneg j)

/-- Drop the pairs whose supply has weight zero. -/
noncomputable def filt (I : Instance D₁ D₂ S) (M : Finset ((D₁ ⊕ D₂) × S)) : Finset ((D₁ ⊕ D₂) × S) :=
  M.filter (fun e => 0 < I.w e.2)

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] in
theorem weight_filt (I : Instance D₁ D₂ S) (M : Finset ((D₁ ⊕ D₂) × S)) :
    weight (posInst I).w (filt I M) = weight I.w M := by
  unfold weight matchedSupply filt
  have hi : image Prod.snd (M.filter fun e => 0 < I.w e.2) =
      (image Prod.snd M).filter (fun j => 0 < I.w j) := by
    rw [Finset.filter_image]
  rw [hi, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : 0 < I.w j
  · simp [h]
  · simp [w_eq_zero I h]

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] in
theorem weight_pos (I : Instance D₁ D₂ S) (N : Finset ((D₁ ⊕ D₂) × S))
    (hN : ∀ e ∈ N, 0 < I.w e.2) : weight (posInst I).w N = weight I.w N := by
  unfold weight matchedSupply
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨e, he, rfl⟩ := mem_image.1 hj
  simp [hN e he]

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] in
theorem isMatching_filt (I : Instance D₁ D₂ S) {X : Finset (D₁ ⊕ D₂)} {Y : Finset S}
    {M : Finset ((D₁ ⊕ D₂) × S)} (h : IsMatching I.E X Y M) :
    IsMatching (posInst I).E X Y (filt I M) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e he => ?_, fun e he e' he' hee => ?_, fun e he e' he' hee => ?_⟩
  · simp only [filt, mem_filter] at he
    obtain ⟨a, b, c⟩ := h1 e he.1
    exact ⟨⟨a, he.2⟩, b, c⟩
  · simp only [filt, mem_filter] at he he'
    exact h2 e he.1 e' he'.1 hee
  · simp only [filt, mem_filter] at he he'
    exact h3 e he.1 e' he'.1 hee

omit [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S] in
theorem isMatching_of_pos (I : Instance D₁ D₂ S) {X : Finset (D₁ ⊕ D₂)} {Y : Finset S}
    {N : Finset ((D₁ ⊕ D₂) × S)} (h : IsMatching (posInst I).E X Y N) :
    IsMatching I.E X Y N :=
  ⟨fun e he => ⟨(h.1 e he).1.1, (h.1 e he).2⟩, h.2.1, h.2.2⟩

theorem mwm_le_pos (I : Instance D₁ D₂ S) (X : Finset (D₁ ⊕ D₂)) :
    maxWeightMatch I.E I.w X Finset.univ ≤ maxWeightMatch (posInst I).E (posInst I).w X
      Finset.univ := by
  classical
  unfold maxWeightMatch
  refine Finset.sup'_le _ _ fun M hM => ?_
  rw [← weight_filt]
  refine Finset.le_sup' (f := weight (posInst I).w) ?_
  simp only [matchings, mem_filter, mem_univ, true_and] at hM ⊢
  exact isMatching_filt I hM

theorem mwm_second_le (I : Instance D₁ D₂ S) (A : Finset D₂) (M : Finset ((D₁ ⊕ D₂) × S)) :
    maxWeightMatch (posInst I).E (posInst I).w (secondStage A)
        (Finset.univ \ matchedSupply (filt I M)) ≤
      maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M) := by
  classical
  unfold maxWeightMatch
  refine Finset.sup'_le _ _ fun N hN => ?_
  simp only [matchings, mem_filter, mem_univ, true_and] at hN
  have hpos : ∀ e ∈ N, 0 < I.w e.2 := fun e he => (hN.1 e he).1.2
  rw [weight_pos I N hpos]
  refine Finset.le_sup' (f := weight I.w) ?_
  simp only [matchings, mem_filter, mem_univ, true_and]
  have h := isMatching_of_pos I hN
  refine ⟨fun e he => ⟨(h.1 e he).1, (h.1 e he).2.1, ?_⟩, h.2.1, h.2.2⟩
  have h2 := (h.1 e he).2.2
  simp only [mem_sdiff, mem_univ, true_and, matchedSupply, filt, mem_image, mem_filter,
    not_exists, not_and] at h2 ⊢
  intro e' he' hee
  exact h2 e' ⟨he', by rw [hee]; exact hpos e he⟩ hee

/-- The modified fractional matching: zero out the columns of zero-weight supplies. -/
noncomputable def xPos (I : Instance D₁ D₂ S) (x : D₁ → S → ℝ) : D₁ → S → ℝ :=
  fun i j => if 0 < I.w j then x i j else 0

/-- The push-forward of `ρ` along `filt`. -/
noncomputable def ρPos (I : Instance D₁ D₂ S) (ρ : Finset ((D₁ ⊕ D₂) × S) → ℝ) :
    Finset ((D₁ ⊕ D₂) × S) → ℝ :=
  fun M' => ∑ M ∈ Finset.univ.filter (fun M => filt I M = M'), ρ M

theorem sum_ρPos (I : Instance D₁ D₂ S) (ρ : Finset ((D₁ ⊕ D₂) × S) → ℝ)
    (F : Finset ((D₁ ⊕ D₂) × S) → ℝ) :
    ∑ M', ρPos I ρ M' * F M' = ∑ M, ρ M * F (filt I M) := by
  simp only [ρPos, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ (filt I) (fun M => ρ M * F (filt I M))]
  refine Finset.sum_congr rfl fun M' _ => Finset.sum_congr rfl fun M hM => ?_
  rw [(mem_filter.1 hM).2]

theorem objective_pos (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (y : D₁ → S → ℝ)
    (hy : ∀ i j, ¬ 0 < I.w j → y i j = 0) :
    objective (posInst I) g y =
      objective I g y + ∑ j, (if 0 < I.w j then 0 else g 1) := by
  unfold objective
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : 0 < I.w j
  · simp [h]
  · simp [w_eq_zero I h, hy _ j h]

theorem objective_xPos (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (x : D₁ → S → ℝ) :
    objective I g (xPos I x) = objective I g x := by
  unfold objective xPos
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : 0 < I.w j
  · simp [h]
  · simp [w_eq_zero I h]

/-- The transported run on `posInst I`. -/
noncomputable def runPos (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (r : Run I g) :
    Run (posInst I) g where
  x := xPos I r.x
  ρ := ρPos I r.ρ
  x_opt := by
    obtain ⟨⟨f1, f2, f3, f4⟩, hmin⟩ := r.x_opt
    have hle : ∀ i j, xPos I r.x i j ≤ r.x i j := by
      intro i j; unfold xPos; split_ifs
      · exact le_rfl
      · exact f1 i j
    have hfeas : IsFeasible (posInst I) (xPos I r.x) := by
      refine ⟨fun i j => ?_, fun i j hE => ?_, fun i => ?_, fun j => ?_⟩
      · unfold xPos; split_ifs
        · exact f1 i j
        · exact le_rfl
      · unfold xPos; split_ifs with h
        · exact f2 i j (fun hE' => hE ⟨hE', h⟩)
        · rfl
      · exact (Finset.sum_le_sum fun j _ => hle i j).trans (f3 i)
      · exact (Finset.sum_le_sum fun i _ => hle i j).trans (f4 j)
    refine ⟨hfeas, ?_⟩
    intro y hy
    have hy0 : ∀ i j, ¬ 0 < I.w j → y i j = 0 :=
      fun i j h => hy.2.1 i j (fun hE => h hE.2)
    have hyI : IsFeasible I y :=
      ⟨hy.1, fun i j hE => hy.2.1 i j (fun hE' => hE hE'.1), hy.2.2.1, hy.2.2.2⟩
    have hx0 : ∀ i j, ¬ 0 < I.w j → xPos I r.x i j = 0 := by
      intro i j h; simp [xPos, h]
    show objective (posInst I) g (xPos I r.x) ≤ objective (posInst I) g y
    rw [objective_pos I g _ hx0, objective_pos I g _ hy0, objective_xPos]
    have := hmin hyI
    simp only [Set.mem_ofPred_eq] at this
    linarith
  ρ_rounding := by
    obtain ⟨h0, h1, h2, h3⟩ := r.ρ_rounding
    refine ⟨fun M => Finset.sum_nonneg fun M _ => h0 M, ?_, fun M' hM' => ?_, ?_⟩
    · have := sum_ρPos I r.ρ (fun _ => (1 : ℝ))
      simp only [mul_one] at this
      show ∑ M', ρPos I r.ρ M' = 1
      rw [this, h1]
    · obtain ⟨M, hM, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM'
      rw [← (mem_filter.1 hM).2]
      exact isMatching_filt I (h2 M hne)
    · intro i j hE
      have key := sum_ρPos I r.ρ (fun M' => if (Sum.inl i, j) ∈ M' then 1 else 0)
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter] at key
      rw [key]
      have hmem : ∀ M : Finset ((D₁ ⊕ D₂) × S), (Sum.inl i, j) ∈ filt I M ↔ (Sum.inl i, j) ∈ M :=
        fun M => by simp [filt, hE.2]
      simp only [hmem]
      rw [h3 i j hE.1]
      simp [xPos, hE.2]

end TSMRealization

open TwoStageMatch in
theorem solution {D₁ D₂ S : Type*} [Fintype D₁] [Fintype D₂] [Fintype S]
    [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]
    (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (hgm : Monotone g)
    (hgc : StrictConvexOn ℝ Set.univ g) (r : Run I g) (A : Finset D₂) :
    (3 / 4 : ℝ) * maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ ≤
      ∑ M, r.ρ M * twoStageWeight I M A := by
  have h1 := TSMRealization.mwm_le_pos I (firstStage ∪ secondStage A)
  have h2 := TSMRealization.pos_case (TSMRealization.posInst I) g hgd hgm hgc
    (TSMRealization.posInst_w_pos I) (TSMRealization.runPos I g r) A
  change _ ≤ ∑ M', TSMRealization.ρPos I r.ρ M' *
    twoStageWeight (TSMRealization.posInst I) M' A at h2
  rw [TSMRealization.sum_ρPos] at h2
  have h3 : ∑ M, r.ρ M * twoStageWeight (TSMRealization.posInst I) (TSMRealization.filt I M) A ≤
      ∑ M, r.ρ M * twoStageWeight I M A := by
    refine Finset.sum_le_sum fun M _ => mul_le_mul_of_nonneg_left ?_ (r.ρ_rounding.1 M)
    unfold twoStageWeight
    rw [TSMRealization.weight_filt]
    exact add_le_add_right (TSMRealization.mwm_second_le I A M) _
  linarith
