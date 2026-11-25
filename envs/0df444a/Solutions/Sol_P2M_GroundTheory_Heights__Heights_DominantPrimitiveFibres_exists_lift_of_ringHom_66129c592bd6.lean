-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_ringHom_66129c592bd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:40.346862+00:00
-- url     : https://prove2.me/submissions/1d0d3b96-0d7c-4959-9f3d-89abeb489105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDominantPrimitiveFibres
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_isIntegral_7e7da0323e6d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
open GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
namespace GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
theorem _root_.solution {R' B' : Type*} [CommRing R'] [CommRing B'] (f : R' →+* B')
    (hf : f.IsIntegral) (φ : R' →+* ℂ) (hφ : Function.Surjective φ)
    (hker : RingHom.ker f ≤ RingHom.ker φ) :
    ∃ ψ : B' →+* ℂ, ψ.comp f = φ := by
  letI := f.toAlgebra
  have : Algebra.IsIntegral R' B' := ⟨hf⟩
  exact exists_lift_of_isIntegral φ hφ hker
end GroundTheory.Heights₂.Heights.DominantPrimitiveFibres
