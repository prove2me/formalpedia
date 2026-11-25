-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fixJStab_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:15:34.412823+00:00
-- url     : https://prove2.me/submissions/38ed9c14-9a4a-4b14-88e9-91ffb0c8d4cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModChebOm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFrobCong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_IsIntegralOfRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFixJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_map_mem_fixJRoots
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_mem_fixJStab

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
theorem _root_.solution {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {P : Polynomial ℤ} (hP : P.Monic) :
    (fixJStab E Ω P).Normal := by
  constructor
  intro n hn g
  rw [mem_fixJStab] at hn ⊢
  intro r hr
  have h1 : g⁻¹ r ∈ fixJRoots (Ω := Ω) P := map_mem_fixJRoots hP g⁻¹ hr
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel]
  rfl
end ReciprocityTheory.ChartRestriction.L1
