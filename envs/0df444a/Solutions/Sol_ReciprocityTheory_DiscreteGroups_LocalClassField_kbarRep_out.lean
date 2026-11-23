-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.kbarRep_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:29.513236+00:00
-- url     : https://prove2.me/submissions/c2410b4d-01ea-479d-967f-73b20e0751c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_kbarRep_mul

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
theorem _root_.solution (y : KbarMult p) (hy : y ∈ multOf p L) (σ : GK p K) :
    kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y = kbarRep p K σ y := by
  have h1 : σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out ∈ subG p K L :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
  have h2 : kbarRep p K (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out) y = y :=
    Units.ext (h1 _ hy)
  calc kbarRep p K (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out y
      = kbarRep p K (σ * (σ⁻¹ * (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out)) y := by
        rw [mul_inv_cancel_left]
    _ = kbarRep p K σ y := by rw [kbarRep_mul, h2]
end ReciprocityTheory.DiscreteGroups.LocalClassField
