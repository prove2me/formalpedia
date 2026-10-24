-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.theorem_1_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:30:05.54541+00:00
-- url     : https://prove2.me/submissions/f9c35d9d-0ea4-468e-a7ff-016d93a72ad1

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Theorems.Thm_ProjSelfConcordant_ConicExt_cond1_iff
import Theorems.Thm_ProjSelfConcordant_ConicExt_hessian_third_expansion
import Theorems.Thm_ProjSelfConcordant_ConicExt_hessian_third_homogeneous
import Theorems.Thm_ProjSelfConcordant_ConicExt_cubic_ineq_iff_pmu_nonneg
import Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_inv_kappa_nonneg_iff
import Theorems.Thm_ProjSelfConcordant_ConicExt_pmu_nonneg_of_abs_le


namespace ProjSelfConcordant.ConicExt.MainProof

lemma rpow_three_halves_sq (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

lemma affine_cubic_iff (ν Q C : ℝ) (hν : 0 < ν) (hQ : 0 ≤ Q) :
    (|ν * C| ≤ 2 * (ν * Q) ^ (3 / 2 : ℝ)) ↔ C ^ 2 ≤ 4 * ν * Q ^ 3 := by
  have hnonneg : 0 ≤ 2 * (ν * Q) ^ (3 / 2 : ℝ) := by positivity
  have heq : (2 * (ν * Q) ^ (3 / 2 : ℝ)) ^ 2 = ν ^ 2 * (4 * ν * Q ^ 3) := by
    rw [mul_pow, rpow_three_halves_sq _ (mul_nonneg hν.le hQ)]
    ring
  rw [← sq_le_sq₀ (abs_nonneg _) hnonneg, sq_abs, heq, mul_pow]
  exact mul_le_mul_iff_right₀ (sq_pos_of_pos hν)

lemma polynomial_iff (ν μ : ℝ) (hν : 2 ≤ ν) :
    (∀ t : ℝ, 0 ≤ pmu ν μ t) ↔ |μ| ≤ 2 * ((ν - 2) / Real.sqrt (ν - 1)) := by
  constructor
  · intro hp
    have hs : Real.sqrt (ν - 1) ^ 2 = ν - 1 := Real.sq_sqrt (by linarith)
    have hk : 1 ≤ Real.sqrt (ν - 1) := by nlinarith [Real.sqrt_nonneg (ν - 1)]
    have heq : Real.sqrt (ν - 1) ^ 2 + 1 = ν := by linarith
    have hb := pmu_inv_kappa_nonneg_iff (Real.sqrt (ν - 1)) μ hk
    rw [heq] at hb
    exact hb.2 ▸ (hb.1.mp ⟨hp _, hp _⟩)
  · exact pmu_nonneg_of_abs_le ν μ hν

lemma normalized_iff (a b c ν : ℝ) (hν : 2 ≤ ν) (hc2 : 0 < b - a ^ 2)
    (hcubic : (∀ α : ℝ,
      (-2 * α ^ 3 + 6 * α ^ 2 * a - 6 * α * b + c) ^ 2 ≤
        4 * ν * (α ^ 2 - 2 * α * a + b) ^ 3) ↔
      ∀ t : ℝ, 0 ≤ pmu ν ((c - 6 * b * a + 4 * a ^ 3) /
        (b - a ^ 2) ^ (3 / 2 : ℝ)) t) :
    (∀ α : ℝ, (-2 * α ^ 3 + 6 * α ^ 2 * a - 6 * α * b + c) ^ 2 ≤
      4 * ν * (α ^ 2 - 2 * α * a + b) ^ 3) ↔
    |c - 6 * b * a + 4 * a ^ 3| ≤
      2 * ((ν - 2) / Real.sqrt (ν - 1)) * (b - a ^ 2) ^ (3 / 2 : ℝ) := by
  have hd : 0 < (b - a ^ 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hc2 _
  rw [hcubic, polynomial_iff ν _ hν, abs_div, abs_of_pos hd, div_le_iff₀ hd]

end ProjSelfConcordant.ConicExt.MainProof


namespace ProjSelfConcordant.ConicExt.MainProof

lemma dk_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (x : E) (k : ℕ) : dk (k + 1) g x 0 = 0 :=
  (iteratedFDeriv ℝ (k + 1) g x).map_coord_zero (0 : Fin (k + 1)) rfl

lemma third_iff {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 2 ≤ ν)
    (hproj : ProjCond1 D f)
    (hexp : ∀ x ∈ D, ∀ (v : EuclideanSpace ℝ (Fin n)) (α : ℝ),
      dk 2 (homExt ν f) (1, x) (α, v + α • x) =
        ν * (α ^ 2 - 2 * α * dk 1 f x v + dk 2 f x v) ∧
      dk 3 (homExt ν f) (1, x) (α, v + α • x) =
        ν * (-2 * α ^ 3 + 6 * α ^ 2 * dk 1 f x v - 6 * α * dk 2 f x v + dk 3 f x v))
    (hhom : ∀ q ∈ conicExt D, ∀ (h : ℝ × EuclideanSpace ℝ (Fin n)) (τ : ℝ),
      0 < τ → dk 2 (homExt ν f) (τ • q) (τ • h) = dk 2 (homExt ν f) q h ∧
        dk 3 (homExt ν f) (τ • q) (τ • h) = dk 3 (homExt ν f) q h) :
    ProjCond3 ((ν - 2) / Real.sqrt (ν - 1)) D f ↔
      AffCond3 (conicExt D) (homExt ν f) := by
  have hνpos : 0 < ν := by linarith
  constructor
  · intro hproj3
    have hslice (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D)
        (u : ℝ × EuclideanSpace ℝ (Fin n)) :
        |dk 3 (homExt ν f) (1, x) u| ≤
          2 * (dk 2 (homExt ν f) (1, x) u) ^ (3 / 2 : ℝ) := by
      let v := u.2 - u.1 • x
      have hu : (u.1, v + u.1 • x) = u := by
        apply Prod.ext
        · rfl
        · exact sub_add_cancel _ _
      obtain ⟨he2, he3⟩ := hexp x hx v u.1
      rw [hu] at he2 he3
      rw [he2, he3]
      by_cases hv : v = 0
      · rw [hv, dk_zero f x 0, dk_zero f x 1, dk_zero f x 2]
        simp only [mul_zero, sub_zero, add_zero]
        apply (affine_cubic_iff ν (u.1 ^ 2) (-2 * u.1 ^ 3) hνpos (sq_nonneg _)).mpr
        have hz : 0 ≤ (ν - 1) * (u.1 ^ 3) ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        nlinarith
      · have hc2 := hproj x hx v hv
        have hQ : 0 ≤ u.1 ^ 2 - 2 * u.1 * dk 1 f x v + dk 2 f x v := by
          nlinarith [sq_nonneg (u.1 - dk 1 f x v)]
        apply (affine_cubic_iff ν _ _ hνpos hQ).mpr
        exact ((normalized_iff (dk 1 f x v) (dk 2 f x v) (dk 3 f x v) ν hν hc2
          (cubic_ineq_iff_pmu_nonneg _ _ _ ν hc2)).mpr (hproj3 x hx v)) u.1
    intro q hq u
    have ht : 0 < q.1⁻¹ := inv_pos.mpr hq.1
    have hnormalize : q.1⁻¹ • q = (1, q.1⁻¹ • q.2) := by
      apply Prod.ext
      · exact inv_mul_cancel₀ (ne_of_gt hq.1)
      · rfl
    obtain ⟨he2, he3⟩ := hhom q hq u q.1⁻¹ ht
    rw [hnormalize] at he2 he3
    have hi := hslice (q.1⁻¹ • q.2) hq.2 (q.1⁻¹ • u)
    simpa only [he2, he3] using hi
  · intro haff x hx v
    by_cases hv : v = 0
    · rw [hv, dk_zero f x 0, dk_zero f x 1, dk_zero f x 2]
      norm_num
    · have hc2 := hproj x hx v hv
      apply (normalized_iff (dk 1 f x v) (dk 2 f x v) (dk 3 f x v) ν hν hc2
        (cubic_ineq_iff_pmu_nonneg _ _ _ ν hc2)).mp
      intro α
      have hslice : ((1 : ℝ), x) ∈ conicExt D := ⟨zero_lt_one, by simpa using hx⟩
      have hi := haff (1, x) hslice (α, v + α • x)
      obtain ⟨he2, he3⟩ := hexp x hx v α
      rw [he2, he3] at hi
      have hQ : 0 ≤ α ^ 2 - 2 * α * dk 1 f x v + dk 2 f x v := by
        nlinarith [sq_nonneg (α - dk 1 f x v)]
      exact (affine_cubic_iff ν _ _ hνpos hQ).mp hi

end ProjSelfConcordant.ConicExt.MainProof

open ProjSelfConcordant.ConicExt

theorem solution {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ) (hν : 2 ≤ ν) :
    (ProjCond1 D f ∧ ProjCond3 ((ν - 2) / Real.sqrt (ν - 1)) D f) ↔
      (AffCond1 (conicExt D) (homExt ν f) ∧ AffCond3 (conicExt D) (homExt ν f)) := by
  have hpos := cond1_iff D hDo hDc f hf ν hν
  have hthird (hp : ProjCond1 D f) := MainProof.third_iff D f ν hν hp
    (hessian_third_expansion D hDo hDc f hf ν)
    (hessian_third_homogeneous D hDo hDc f hf ν)
  constructor
  · intro hp
    exact ⟨hpos.mp hp.1, (hthird hp.1).mp hp.2⟩
  · intro ha
    have hp := hpos.mpr ha.1
    exact ⟨hp, (hthird hp).mpr ha.2⟩
