-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:42.101592+00:00
-- url     : https://prove2.me/submissions/40d978a1-4900-4165-8678-3173f26504c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength

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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) := by
  have hu : IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) f) :=
    IsLocalization.map_units _ (⟨f, fun h ↦ hf (RingHom.mem_ker.1 h)⟩ : (RingHom.ker (eval q)).primeCompl)
  exact hu.map (Ideal.Quotient.mk _)
end GroundTheory.Heights₂.Heights
