-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.uval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:42.318286+00:00
-- url     : https://prove2.me/submissions/073665ce-b80d-414a-8639-0d748fe191f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_iff_fixed


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
variable [(subG p K L).Normal]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) (w : (layerU p K L).V) : uval w ∈ L :=
  (mem_iff_fixed h _).2 fun σ hσ =>
    congrArg (fun y : Ubar p => ((Additive.toMul (y : KbarMult p) : (PadicAlgCl p)ˣ) : PadicAlgCl p))
      (w.2 ⟨σ, hσ⟩)
end ReciprocityTheory.DiscreteGroups.LocalClassField
