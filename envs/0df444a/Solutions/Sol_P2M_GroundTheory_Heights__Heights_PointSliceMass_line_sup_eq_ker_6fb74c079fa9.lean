-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointSliceMass_line_sup_eq_ker_6fb74c079fa9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:34.873916+00:00
-- url     : https://prove2.me/submissions/26cf84e3-a052-402d-b40f-bdd99d12309b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointChowForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPointSliceMass

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
open GroundTheory.Heights₂.Heights.PointSliceMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.PointSliceMass
theorem _root_.solution (y ℓ : Fin n → ℂ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : ∀ q, q ∈ J ↔ ∀ t : ℂ, eval (t • y) q = 0) (hc0 : ∑ a, ℓ a * y a ≠ 0) :
    J ⊔ Ideal.span {linForm ℓ - 1} =
      RingHom.ker (MvPolynomial.eval ((∑ a, ℓ a * y a)⁻¹ • y)) := by
  set c := ∑ a, ℓ a * y a with hc
  set I := J ⊔ Ideal.span {linForm ℓ - 1} with hI
  have hsmul : ∀ t : ℂ, eval (t • y) (linForm ℓ) = t * c := by
    intro t
    simp only [hc, linForm, map_sum, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  apply le_antisymm
  · refine sup_le (fun q hq => (hJ q).mp hq _) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      hsmul, inv_mul_cancel₀ hc0, sub_self]
  · have hX : ∀ b, X b - C ((c⁻¹ • y) b) ∈ I := by
      intro b
      have h1 : ∀ a, C (y a) * X b - C (y b) * X a ∈ J := fun a => (hJ _).mpr fun t => by
        simp only [map_sub, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
        ring
      have hs : ∑ a, C (ℓ a) * (C (y a) * X b - C (y b) * X a) =
          C c * X b - C (y b) * linForm ℓ := by
        rw [hc, map_sum, Finset.sum_mul, linForm, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul]
        ring
      have hcc : C c⁻¹ * C c = (1 : MvPolynomial (Fin n) ℂ) := by
        rw [← C_mul, inv_mul_cancel₀ hc0, C_1]
      have key : X b - C ((c⁻¹ • y) b) = C c⁻¹ * (∑ a, C (ℓ a) * (C (y a) * X b - C (y b) * X a) +
          C (y b) * (linForm ℓ - 1)) := by
        rw [hs, Pi.smul_apply, smul_eq_mul, C_mul]
        linear_combination (-X b) * hcc
      rw [key]
      exact Ideal.mul_mem_left _ _ (Ideal.add_mem _
        (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.mem_sup_left (h1 a)))
        (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))))
    have hext : Ideal.Quotient.mkₐ ℂ I =
        (Algebra.ofId ℂ (MvPolynomial (Fin n) ℂ ⧸ I)).comp (aeval (c⁻¹ • y)) := by
      apply MvPolynomial.algHom_ext
      intro b
      rw [AlgHom.comp_apply, aeval_X, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk,
        ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, MvPolynomial.algebraMap_eq]
      exact hX b
    intro q hq
    rw [RingHom.mem_ker] at hq
    have h := congrArg (fun φ => φ q) hext
    simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.comp_apply, Algebra.ofId_apply] at h
    rw [← Ideal.Quotient.eq_zero_iff_mem, h]
    rw [show aeval (c⁻¹ • y) q = eval (c⁻¹ • y) q from rfl, hq, map_zero]
end GroundTheory.Heights₂.Heights.PointSliceMass
