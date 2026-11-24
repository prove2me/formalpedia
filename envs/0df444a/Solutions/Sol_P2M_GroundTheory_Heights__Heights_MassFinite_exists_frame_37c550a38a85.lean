-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MassFinite_exists_frame_37c550a38a85
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:46.205059+00:00
-- url     : https://prove2.me/submissions/cbd4edd8-522a-4ef4-b669-19facfbc578a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite

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
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite
namespace GroundTheory.Heights₂.Heights.MassFinite
theorem _root_.solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j := by
  classical
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 fun j => star (U i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp [v, PiLp.inner_apply, Matrix.star_apply, mul_comm]
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge,
    fun i z => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  simp [v, PiLp.inner_apply, mul_comm]
end GroundTheory.Heights₂.Heights.MassFinite
