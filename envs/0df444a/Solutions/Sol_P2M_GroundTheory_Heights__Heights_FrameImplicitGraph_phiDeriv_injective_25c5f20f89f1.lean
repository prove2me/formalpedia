-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_phiDeriv_injective_25c5f20f89f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:53.894065+00:00
-- url     : https://prove2.me/submissions/70c53027-7a31-4eba-b6e7-f2b7393e1722

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameImplicitGraph
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HasStrictFDerivAtEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameImplicitGraph_polyDeriv_apply_12bd4a73affc

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
noncomputable section
open MvPolynomial
open GroundTheory.Heights₂.Heights.FrameImplicitGraph
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.FrameImplicitGraph
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hx : eval (fun i => x i) (frameJacobianDet b I f) ≠ 0) :
    Function.Injective (phiDeriv b I f x) := by
  refine (injective_iff_map_eq_zero (phiDeriv b I f x)).2 fun v hv => ?_
  set c : Fin n → ℂ := fun j => inner ℂ (b j) v with hc
  have h1 : ∀ i ∈ I, c i = 0 := fun i hi => by
    have := congrFun (congrArg Prod.fst hv) ⟨i, hi⟩
    simpa [phiDeriv, projCLM, c] using this
  have hvl : ∀ l, v l = ∑ j, c j * b j l := fun l => by
    have := congrArg (fun y : EuclideanSpace ℂ (Fin n) => y l) (b.sum_repr' v)
    simpa [c, smul_eq_mul] using this.symm
  have h2 : ∀ k, ∑ j, c j * eval (fun i => x i) (frameDeriv b j (f k)) = 0 := fun k => by
    have := congrFun (congrArg Prod.snd hv) k
    simp only [phiDeriv, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply, polyDeriv_apply,
      Prod.snd_zero, Pi.zero_apply] at this
    rw [← this]
    simp only [frameDeriv, map_sum, map_mul, eval_C, hvl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  let M : Matrix {j // j ∉ I} {j // j ∉ I} ℂ := Matrix.of fun k j => eval (fun i => x i) (frameDeriv b j (f k))
  have hM : M.det ≠ 0 := by
    have : eval (fun i => x i) (frameJacobianDet b I f) = M.det := by
      rw [frameJacobianDet, RingHom.map_det]
      rfl
    rwa [← this]
  have hMc : M.mulVec (fun j => c j) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h2 k, ← Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ I)]
    simp [M, Matrix.mulVec, dotProduct, h1, mul_comm]
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hM hMc
  have hc0 : ∀ j, c j = 0 := fun j => by
    by_cases hj : j ∈ I
    · exact h1 j hj
    · exact congrFun h3 ⟨j, hj⟩
  have hv' : v = ∑ j, c j • b j := (b.sum_repr' v).symm
  rw [hv']
  simp [hc0]
end GroundTheory.Heights₂.Heights.FrameImplicitGraph
