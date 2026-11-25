-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_eq_zero_of_9eb668df8ce3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:50.498359+00:00
-- url     : https://prove2.me/submissions/5c2b3561-175a-4b20-baaa-17e28682a442

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_hom_aeval_926da0c2fb59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_genSubst_5af28047283e

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
theorem _root_.solution {F R : Type*} [Field F] [CommRing R] [Algebra F R] {n k : ℕ}
    (ζ c c' : Fin n → R) (hc : ∑ l, c l * ζ l = 1) (g : MvPolynomial (Fin k × Fin n) F)
    (h : aeval (genSubst ζ c') g = 0) : aeval (genSubst ζ c) g = 0 := by
  have := hom_aeval (F := F) (aeval (genSubst ζ c) : MvPolynomial (Fin k × Fin n) R →ₐ[R] _).toRingHom
    (fun r => by simp [MvPolynomial.algebraMap_apply]) (genSubst ζ c') g
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_genSubst_genSubst ζ c c' hc, h,
    map_zero] at this
  exact this.symm
end GroundTheory.Heights₂.Heights.IncidenceGeneric
