-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_l_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:51.155491+00:00
-- url     : https://prove2.me/submissions/1a918c0b-faf6-48d9-9856-d5f3dab48707

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {a b : Fin n} (h : bl a < bl b) (x : ℂ) (Y : Module.End ℂ M) :
    l ∘ₗ (capEntry E x a b * Y) = ψ a b • (l ∘ₗ Y) := by
  have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
  have : capEntry E x a b = E a b := by simp [capEntry, hab]
  rw [this, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, hl a b h, LinearMap.smul_comp]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
