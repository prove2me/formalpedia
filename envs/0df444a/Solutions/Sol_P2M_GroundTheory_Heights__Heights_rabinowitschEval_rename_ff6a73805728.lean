-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_rabinowitschEval_rename_ff6a73805728
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:57.075388+00:00
-- url     : https://prove2.me/submissions/e0a1138a-6400-4844-85b7-52091bd2c44e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch

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
variable {R : Type*} [CommRing R] {ι : Type*}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (K : Ideal (MvPolynomial ι R)) (g p : MvPolynomial ι R) :
    rabinowitschEval K g (rename some p) =
      algebraMap (MvPolynomial ι R ⧸ K) _ (Ideal.Quotient.mk K p) := by
  have h : (rabinowitschEval K g).comp (rename (R := R) (some : ι → Option ι)).toRingHom =
      (algebraMap (MvPolynomial ι R ⧸ K) (Localization.Away (Ideal.Quotient.mk K g))).comp
        (Ideal.Quotient.mk K) :=
    MvPolynomial.ringHom_ext (fun r => by simp [rabinowitschEval]) (fun i => by simp [rabinowitschEval])
  exact congrArg (fun f => f p) h
end GroundTheory.Heights₂.Heights
