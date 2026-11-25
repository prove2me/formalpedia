-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.jets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:30:13.155268+00:00
-- url     : https://prove2.me/submissions/0d909b64-e36c-4cc1-afb0-7bc571aba043

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_le_sup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_inv_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]
namespace ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
theorem _root_.solution {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R} (hm : ∀ x ∈ m, ¬ IsUnit x)
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m)
    (hfrac : ∀ f : R, ∃ (n : ℕ) (G G' : R), G ∈ V ^ n ∧ G' ∈ V ^ n ∧ IsUnit G' ∧ f * G' = G)
    (D : ℕ) (f : R) : ∃ v ∈ V ^ D, f - v ∈ m ^ (D + 1) := by
  obtain ⟨n, G, G', hG, hG', ⟨u, rfl⟩, hf⟩ := hfrac f
  obtain ⟨w, hw, hw'⟩ := inv_approx h1 hm hres D n u hG'
  have hGw : G * w ∈ V ^ D ⊔ (m ^ (D + 1)).restrictScalars F := by
    refine pow_le_sup h1 hres D (n + n * D) ?_
    rw [pow_add]
    exact Submodule.mul_mem_mul hG hw
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hGw
  refine ⟨y, hy, ?_⟩
  have hfG : f = G * ((u⁻¹ : Rˣ) : R) := by rw [← hf, mul_assoc, u.mul_inv, mul_one]
  have : f - y = G * (((u⁻¹ : Rˣ) : R) - w) + z := by
    rw [hfG]
    have : y = G * w - z := by rw [← hyz]; ring
    rw [this]; ring
  rw [this]
  exact (m ^ (D + 1)).add_mem ((m ^ (D + 1)).mul_mem_left _ hw') hz
end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
