-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_equiv_subG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:39.765878+00:00
-- url     : https://prove2.me/submissions/2be4dcd3-625f-4f05-9dfc-254e911d656c

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_resGK_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_range_resGK

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
theorem _root_.solution (h : K ≤ L) : ∃ e : GK p L ≃* subG p K L, (∀ σ, (e σ : GK p K) = resGK h σ) ∧
    Continuous e ∧ Continuous e.symm := by
  have hmem : ∀ σ, resGK h σ ∈ subG p K L := fun σ => by
    rw [← range_resGK h]; exact ⟨σ, rfl⟩
  let f : GK p L →* subG p K L := (resGK h).codRestrict (subG p K L) hmem
  have hf : Bijective f := by
    refine ⟨fun a b hab => resGK_injective h (congrArg Subtype.val hab), fun τ => ?_⟩
    have hτ : τ.1 ∈ (resGK h).range := by rw [range_resGK h]; exact τ.2
    obtain ⟨σ, hσ⟩ := hτ
    exact ⟨σ, Subtype.ext hσ⟩
  have hc : Continuous (MulEquiv.ofBijective f hf) := (resGK_continuous h).subtype_mk hmem
  refine ⟨MulEquiv.ofBijective f hf, fun _ => rfl, hc, ?_⟩
  exact Continuous.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective f hf).toEquiv) hc
end ReciprocityTheory.DiscreteGroups.LocalClassField
