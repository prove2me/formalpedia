-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Comb_alt_isAlt_9f813e5016fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:57:05.80396+00:00
-- url     : https://prove2.me/submissions/b607aca2-7245-49e8-adc2-fb9701bde9ca

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_rename_alt_18e743d13c03

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Comb
open MvPolynomial Finset Equiv
noncomputable section
variable {m : ℕ}
namespace GroundTheory.Heights₂.Heights.RestTerms.Comb
theorem _root_.solution (v : Fin m → ℕ) : IsAlt (alt v) := fun σ => rename_alt v σ
end GroundTheory.Heights₂.Heights.RestTerms.Comb
