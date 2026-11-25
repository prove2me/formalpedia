-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finrank_coneTangent_of_jacobian_0027e1f387a0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:09.166603+00:00
-- url     : https://prove2.me/submissions/b8b9d45a-9613-4ec7-b13c-d7e3be6fbb0e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeKrullDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointEquiv_apply_448488b77ab2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_frameDeriv_basisFun_c27fbd710823

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by
  set x := h.pointOf y with hx
  let a : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun k j => eval x (pderiv j (f k))

  have hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap := by
    ext v
    simp only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]
    constructor
    · intro hv
      funext k
      simpa [Matrix.mulVec, dotProduct, a] using hv (f k) (hf k)
    · intro hv q hq
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)
      have hq0 : eval x q = 0 := hy q hq
      have hf0 : ∀ k, eval x (f k) = 0 := fun k => hy _ (hf k)
      have hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j := by
        intro j
        have := congrArg (fun P => eval x (pderiv j P)) hc
        simp only [map_sum, pderiv_mul, map_add, map_mul, hq0, hf0, mul_zero, zero_add] at this
        simpa [a, mul_comm] using this.symm
      have hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0 := fun k => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv k
      have : eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, hder, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
      exact (mul_eq_zero.1 this).resolve_left hsy

  let M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ := Matrix.of fun k j => a k j
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    convert hD using 1
    rw [frameJacobianDet, RingHom.map_det]
    congr 1
    ext k j
    simp [M, a, frameDeriv_basisFun]
  have hsurj : Function.Surjective a.mulVecLin := by
    intro t
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM t
    refine ⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩
    rw [← hv]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by
      simp only [Finset.mem_compl, not_not] at hj; simp [hj]),
      Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrank := LinearMap.finrank_range_add_finrank_ker a.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hle : I₀.card ≤ n := by simpa using Finset.card_le_univ I₀
  omega
end GroundTheory.Heights₂.Heights
