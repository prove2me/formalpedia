-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.not_isUnit_algebraMap_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:29.215544+00:00
-- url     : https://prove2.me/submissions/d9e9aac3-33da-43ce-adcf-f9ad5c353f6a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHorPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {O V : Type} [CommRing O] [IsLocalRing O] [CommRing V]
    [Nontrivial V] [Algebra O V] [Module.Finite O V] (π : O) (hπ : π ∈ maximalIdeal O) :
    ¬ IsUnit (algebraMap O V π) := by
  intro hu
  have htop : (⊤ : Submodule O V) ≤ maximalIdeal O • ⊤ := by
    intro v _
    obtain ⟨w, hw⟩ : ∃ w : V, algebraMap O V π * w = v :=
      ⟨hu.unit⁻¹ * v, by rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]⟩
    rw [← hw, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hπ Submodule.mem_top
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) ⊤
    Module.Finite.fg_top htop (IsLocalRing.maximalIdeal_le_jacobson _)
  have h1 : (1 : V) ∈ (⊥ : Submodule O V) := hbot ▸ Submodule.mem_top
  exact one_ne_zero ((Submodule.mem_bot O).mp h1)
end ReciprocityTheory.ChartRestriction.G.T0
