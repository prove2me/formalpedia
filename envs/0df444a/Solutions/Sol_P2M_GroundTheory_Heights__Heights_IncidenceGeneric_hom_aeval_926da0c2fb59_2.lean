-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:45.945184+00:00
-- url     : https://prove2.me/submissions/9fe97ad7-f9a5-4a57-8d49-0765e2022f78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric

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
open GroundTheory.Heights₂.Heights.IncidenceGeneric
namespace GroundTheory.Heights₂.Heights.IncidenceGeneric
theorem _root_.solution {F σ R T : Type*} [Field F] [CommRing R] [CommRing T] [Algebra F R] [Algebra F T]
    (Φ : R →+* T) (hΦ : ∀ r : F, Φ (algebraMap F R r) = algebraMap F T r) (y : σ → R)
    (g : MvPolynomial σ F) : Φ (aeval y g) = aeval (fun s => Φ (y s)) g := by
  rw [aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  ext r
  exact hΦ r
end GroundTheory.Heights₂.Heights.IncidenceGeneric
