-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.subG_normal_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:28.930496+00:00
-- url     : https://prove2.me/submissions/b70f309f-5b35-4358-8a14-12309f5f0d59

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_normal_iff

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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') (hL : K ≤ L)
    (hn : (subG p K L).Normal) : (subG p K' L).Normal :=
  subG_normal_of_stable fun σ x hx => (subG_normal_iff hL).1 hn (resGK h σ) x hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
