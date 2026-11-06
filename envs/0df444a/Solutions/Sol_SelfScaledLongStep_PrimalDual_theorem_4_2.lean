-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:43:19.550211+00:00
-- url     : https://prove2.me/submissions/18aa2709-a5bb-490f-9429-ac60d60dd681
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_1

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace PDThm42Aux

/-- On the open set where `F` is `C³`, `F` and `∇F` have the expected Fréchet derivatives. -/
lemma derivs {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiffOn ℝ 3 F U)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
    HasFDerivAt F (fderiv ℝ F y) y ∧ HasFDerivAt (gradient F) (hess F y) y := by
  have hn : U ∈ nhds y := hU.mem_nhds hy
  refine ⟨((hF.differentiableOn (by norm_num)).differentiableAt hn).hasFDerivAt, ?_⟩
  have h2 : ContDiffOn ℝ 2 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (h2.differentiableOn (by norm_num)).differentiableAt hn
  have hg : DifferentiableAt ℝ (gradient F) y := by
    have : gradient F = fun z => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ F z) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.differentiableAt.comp y hd
  exact hg.hasFDerivAt

end PDThm42Aux

open PDThm42Aux

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hσ : 0 < sigma K x p)
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α * sigma K x p < 1) :
    F (x - α • p) ≤ F x - α * ⟪gradient F x, p⟫_ℝ +
      (lnorm F x p) ^ 2 / (sigma K x p) ^ 2 *
        (-(α * sigma K x p) - Real.log (1 - α * sigma K x p)) := by
  set σ := sigma K x p with hσdef
  have hC3 : ContDiffOn ℝ 3 F (interior K) := hF.1.1.2.1
  have hpd := hF.1.2.2.2.2 x hx
  have hL : lnorm F x p ^ 2 = ⟪hess F x p, p⟫_ℝ := by
    unfold lnorm
    rw [Real.sq_sqrt]
    by_cases hp : p = 0
    · rw [hp, map_zero, inner_zero_left]
    · exact (hpd p hp).le
  set L := lnorm F x p ^ 2 with hLdef
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  -- Theorem 4.1 along the segment
  have h41 : ∀ t ∈ Set.Icc 0 α, x - t • p ∈ interior K ∧
      ⟪hess F (x - t • p) p, p⟫_ℝ ≤ (1 / (1 - t * σ) ^ 2) * L := by
    intro t ht
    have htσ : t * σ < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right ht.2 hσ.le) hα
    obtain ⟨hmem, hb⟩ := SelfScaledLongStep.PrimalDual.theorem_4_1 K hK F ν hν hF x p hx t ht.1 htσ
    exact ⟨hmem, by rw [hL]; exact (hb p).2⟩
  have hpos1 : ∀ t ∈ Set.Icc 0 α, 0 < 1 - t * σ := by
    intro t ht
    have := mul_le_mul_of_nonneg_right ht.2 hσ.le
    linarith
  -- derivatives along the line
  have hline : ∀ t ∈ Set.Icc 0 α,
      HasDerivAt (fun s : ℝ => F (x - s • p)) (-⟪gradient F (x - t • p), p⟫_ℝ) t ∧
      HasDerivAt (fun s : ℝ => ⟪gradient F (x - s • p), p⟫_ℝ)
        (-⟪hess F (x - t • p) p, p⟫_ℝ) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := derivs _ isOpen_interior F hC3 _ (h41 t ht).1
    have hl : HasDerivAt (fun s : ℝ => x - s • p) (-p) t := by
      have := ((hasDerivAt_id t).smul_const p).const_sub x
      simpa using this
    refine ⟨?_, ?_⟩
    · refine (h1.comp_hasDerivAt t hl).congr_deriv ?_
      rw [map_neg, gradient, InnerProductSpace.toDual_symm_apply]
    · refine ((h2.comp_hasDerivAt t hl).inner ℝ (hasDerivAt_const t p)).congr_deriv ?_
      simp [map_neg, inner_neg_left]
  -- comparison function for the first derivative
  set g0 := ⟪gradient F x, p⟫_ℝ with hg0
  let k : ℝ → ℝ := fun s => -⟪gradient F (x - s • p), p⟫_ℝ + g0 - L / σ * ((1 - s * σ)⁻¹ - 1)
  have hk : ∀ t ∈ Set.Icc 0 α, HasDerivAt k
      (⟪hess F (x - t • p) p, p⟫_ℝ - L / σ * (σ / (1 - t * σ) ^ 2)) t := by
    intro t ht
    have h1 := (hline t ht).2
    have hden : HasDerivAt (fun s : ℝ => 1 - s * σ) (-σ) t :=
      (hasDerivAt_mul_const σ).const_sub 1
    have hinv := hden.inv (hpos1 t ht).ne'
    refine ((h1.neg.add_const g0).sub ((hinv.sub_const 1).const_mul (L / σ))).congr_deriv ?_
    ring
  have hk_nonpos : ∀ t ∈ Set.Icc 0 α, k t ≤ 0 := by
    have hanti : AntitoneOn k (Set.Icc 0 α) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 α)
      · intro t ht; exact (hk t ht).continuousAt.continuousWithinAt
      · intro t ht
        exact (hk t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hk t ht').deriv]
        have hb := (h41 t ht').2
        have hp1 := hpos1 t ht'
        have : L / σ * (σ / (1 - t * σ) ^ 2) = 1 / (1 - t * σ) ^ 2 * L := by
          field_simp
        linarith
    have h0 : k 0 = 0 := by simp [k, hg0]
    intro t ht
    have := hanti ⟨le_rfl, hα0⟩ ht ht.1
    linarith
  -- comparison function for the value
  let h : ℝ → ℝ := fun s => F (x - s • p) - F x + s * g0 -
    L / σ ^ 2 * (-(s * σ) - Real.log (1 - s * σ))
  have hh : ∀ t ∈ Set.Icc 0 α, HasDerivAt h (k t) t := by
    intro t ht
    have h1 := (hline t ht).1
    have hden : HasDerivAt (fun s : ℝ => 1 - s * σ) (-σ) t :=
      (hasDerivAt_mul_const σ).const_sub 1
    have hlog := hden.log (hpos1 t ht).ne'
    have hlin : HasDerivAt (fun s : ℝ => -(s * σ)) (-σ) t := (hasDerivAt_mul_const σ).neg
    refine (((h1.sub_const (F x)).add (hasDerivAt_mul_const g0)).sub
      ((hlin.sub hlog).const_mul (L / σ ^ 2))).congr_deriv ?_
    have hp1 := (hpos1 t ht).ne'
    simp only [k]
    field_simp
    ring
  have hanti : AntitoneOn h (Set.Icc 0 α) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 α)
    · intro t ht; exact (hh t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hh t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hh t (interior_subset ht)).deriv]
      exact hk_nonpos t (interior_subset ht)
  have h0 : h 0 = 0 := by simp [h]
  have := hanti ⟨le_rfl, hα0⟩ ⟨hα0, le_rfl⟩ hα0
  rw [h0] at this
  simp only [h] at this
  linarith
