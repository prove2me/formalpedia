-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreMap_eval__aeval_d46a46815112
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:55.069793+00:00
-- url     : https://prove2.me/submissions/cc436d44-b0b3-4394-a8ad-8c3a4534fe56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreRadicalPrime

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {σ ι : Type*} {d : ℕ} (t : σ → ℂ)
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) :
    MvPolynomial.map (eval t) (Polynomial.eval₂ (aeval y).toRingHom θ H) =
      Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) (H.map (MvPolynomial.map (eval t))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro s
    simp [MvPolynomial.algebraMap_eq]
  · intro j
    simp
end GroundTheory.Heights₂.Heights
