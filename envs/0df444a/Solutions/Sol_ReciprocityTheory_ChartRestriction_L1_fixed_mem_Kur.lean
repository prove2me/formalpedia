-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.fixed_mem_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:09:54.866937+00:00
-- url     : https://prove2.me/submissions/ddc16de8-b946-4409-8397-84e28a4a14fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModLocA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kur
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_iff_fixed
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_subG_Kur_iff


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
theorem _root_.solution {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hK : FiniteDimensional ℚ_[l] K) (y : PadicAlgCl l)
    (h : ∀ ρ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, (∀ z : PadicAlgCl l, ‖z‖ ≤ 1 → ‖ρ z - z‖ < 1) → ρ y = y) :
    y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l K := by
  rw [ReciprocityTheory.DiscreteGroups.LocalClassField.mem_iff_fixed (ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (p := l) (K := K)) y]
  intro σ hσ
  exact h σ ((ReciprocityTheory.DiscreteGroups.LocalClassField.mem_subG_Kur_iff hK σ).1 hσ)
end ReciprocityTheory.ChartRestriction.L1
