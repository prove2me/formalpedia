-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fixJ_ker_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:27.041168+00:00
-- url     : https://prove2.me/submissions/73ab8aad-17fb-409f-a77e-40cb56226e29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E)) (hk : art.ker = hilbertSubgroup E Ω) :
    IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) := by
  refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
  rw [hk]
  exact Subgroup.isClosed_topologicalClosure _
end ReciprocityTheory.ChartRestriction.L1
