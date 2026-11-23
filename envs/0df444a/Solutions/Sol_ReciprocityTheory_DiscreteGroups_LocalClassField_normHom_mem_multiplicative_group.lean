-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normHom_mem_multiplicative_group
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:22.486535+00:00
-- url     : https://prove2.me/submissions/3422de12-dc44-405d-bef6-ebdc36deadb4

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_mul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_out
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finite_GalLK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_multOf_iff_fixed


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
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := by
  have := finite_GalLK (p := p) (K := K) hL
  have := Fintype.ofFinite (GK p K ⧸ subG p K L)
  rw [mem_multOf_iff_fixed (le_refl K)]
  intro σ _
  rw [normHom_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H τ =>
    show _ = kbarRep p K (QuotientGroup.mk (σ * τ) : GK p K ⧸ subG p K L).out y
    rw [kbarRep_out y hy, kbarRep_out y hy, kbarRep_mul]
end ReciprocityTheory.DiscreteGroups.LocalClassField
