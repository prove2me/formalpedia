-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:35.537489+00:00
-- url     : https://prove2.me/submissions/403ac436-0c95-4b5f-b21b-1e04fd771507

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [Fintype (GK p K ⧸ subG p K L)] (y : KbarMult p) :
    normHom p K L y = ∑ c : GK p K ⧸ subG p K L, kbarRep p K c.out y := by
  unfold normHom
  rw [finsum_eq_sum_of_fintype, AddMonoidHom.finsetSum_apply]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
