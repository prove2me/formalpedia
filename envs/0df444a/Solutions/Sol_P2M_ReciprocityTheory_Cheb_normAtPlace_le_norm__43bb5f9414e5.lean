-- Prove2me | solution 1 for P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:38.878566+00:00
-- url     : https://prove2.me/submissions/5d9eab81-d21e-446d-aa38-c6542bbee969

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (w : InfinitePlace E) (z : mixedSpace E) : normAtPlace w z ≤ ‖z‖ := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w z) (Finset.mem_univ w)
end ReciprocityTheory.Cheb
