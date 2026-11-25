-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSections_plusMetric_joinPt_ee8b088ced98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:30.539305+00:00
-- url     : https://prove2.me/submissions/9ff296fa-8660-42c0-9907-4120cc351255

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_exists_evalCone_ne_zero_d1e48d88ea05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_cross_3f7d63056fd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_evalCone_chartMonomial_fd0871b69c38


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.SmallSections
theorem _root_.solution {P : ArithVariety n} {D : AddBlockData P} {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ} (hg : D.IsFormSystem d g)
    (N : HermLine n) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : z ∈ P.points ℂ) {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) :
    D.plusMetric N d g G δ (D.joinPt z (fun j ↦ evalCone z (g c j))) =
      ‖evalCone z (chartMonomial c d)‖ * N.metric z := by
  have hm : evalCone z (chartMonomial c d) ≠ 0 := by
    rw [evalCone_chartMonomial]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)
  have hm2 : 0 < ‖evalCone z (chartMonomial c d)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hm) 2
  have hGz : ∀ i, evalCone z (G i) = 0 := fun i ↦
    hz.2 _ (hG.span_eq ▸ Ideal.subset_span ⟨i, rfl⟩)
  have hL : 0 < ∑ j, ‖evalCone z (g c j)‖ ^ 2 := by
    obtain ⟨j, hj⟩ := exists_evalCone_ne_zero hg hz hzc
    exact Finset.sum_pos' (fun _ _ ↦ by positivity) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hj) 2⟩
  have hS : 0 < ∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ ↦ by positivity) ⟨c, Finset.mem_univ _, hm2⟩
  have hden : D.den d g G δ z = (∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2) *
      (∑ j, ‖evalCone z (g c j)‖ ^ 2) / ‖evalCone z (chartMonomial c d)‖ ^ 2 := by
    have hG0 : ∑ i, ‖evalCone z (G i)‖ ^ 2 *
        ∏ k, l2Norm (z k) ^ (2 * ((d k : ℤ) + D.deg k - δ i k)) = 0 :=
      Finset.sum_eq_zero fun i _ ↦ by rw [hGz i, norm_zero]; ring
    rw [AddBlockData.den, hG0, add_zero, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun c' _ ↦ ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [evalCone_cross hg hz hzc c' j, norm_div, norm_mul, div_pow, mul_pow]
  have hq : (∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2) / D.den d g G δ z =
      ‖evalCone z (chartMonomial c d)‖ ^ 2 / ∑ j, ‖evalCone z (g c j)‖ ^ 2 := by
    rw [hden]
    field_simp
  change N.metric z * l2Norm (fun j ↦ evalCone z (g c j)) *
    Real.sqrt ((∑ c', ‖evalCone z (chartMonomial c' d)‖ ^ 2) / D.den d g G δ z) = _
  rw [hq, l2Norm, mul_assoc, ← Real.sqrt_mul hL.le, mul_div_cancel₀ _ hL.ne',
    Real.sqrt_sq (norm_nonneg _), mul_comm]
end GroundTheory.Heights₂.Heights.SmallSections
