-- Prove2me | solution 1 for P2M_Formalism_MainNotions_PlaneGram_vge_zero__d9b99f199353
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:25.080977+00:00
-- url     : https://prove2.me/submissions/fd6192fd-b5ab-44d6-a3ac-f5f7b0effa7a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vge_iff__8395374a28ef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
variable (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (a : ℝ) : vge v a (0 : K) := by
  rw [vge_iff']; intro n hn; rw [AddValuation.map_zero] at hn; exact absurd hn (by simp)
end Formalism.MainNotions.PlaneGram
