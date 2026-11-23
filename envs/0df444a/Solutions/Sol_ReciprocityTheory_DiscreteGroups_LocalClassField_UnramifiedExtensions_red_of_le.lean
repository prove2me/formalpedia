-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.red_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:01.972081+00:00
-- url     : https://prove2.me/submissions/1ea393fc-7d39-462e-af3d-c1c585f960d9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_MemOfPowQKSubOne
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Obar_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {x : PadicAlgCl p} (h : ‖x‖ ≤ 1) : red x = res ⟨x, mem_Obar_iff.2 h⟩ := dif_pos h
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
