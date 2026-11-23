-- Prove2me | solution 1 for P2M_GlobalTheory_ThetaRational_algHom_eval__435c3be33efa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:55.065333+00:00
-- url     : https://prove2.me/submissions/ae82ada3-f9d2-4f2a-91ff-60ac4d4bf35e

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ}
namespace GlobalTheory.ThetaRational
theorem _root_.solution (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (χ : A →ₐ[ℂ] ℂ)
    (r : Polynomial (MvPolynomial (Fin n) ℂ)) (a : A) :
    χ (r.eval₂ j.toRingHom a) =
      (r.map (MvPolynomial.eval fun i => χ (j (MvPolynomial.X i)))).eval (χ a) := by
  rw [Polynomial.eval_map]
  have := Polynomial.hom_eval₂ r j.toRingHom χ.toRingHom a
  refine this.trans ?_
  congr 1
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => by simp)
  rw [MvPolynomial.eval_C]
  exact (χ.comp j).commutes c
end GlobalTheory.ThetaRational
