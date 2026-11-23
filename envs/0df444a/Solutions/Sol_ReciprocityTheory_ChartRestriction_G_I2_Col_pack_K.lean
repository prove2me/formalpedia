-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.Col.pack_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:16.675414+00:00
-- url     : https://prove2.me/submissions/0d95395a-f05a-4abf-8049-2a059a941b6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SecondProjectionOrthogonalComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_MemOfProjTwoEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex NumberField
open scoped InnerProductSpace
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.Col
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.Col
theorem _root_.solution {ι : Type} [Fintype ι] (hP : Ext.PackingCount) (K : Submodule ℝ (EuclideanSpace ℂ ι))
    (S : Finset (EuclideanSpace ℂ ι)) (hS : ∀ u ∈ S, u ∈ K) (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hR : ∀ u ∈ S, ‖u‖ ≤ R) (hsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → δ ≤ dist u v) :
    (S.card : ℝ) ≤ (3 * R / δ) ^ (dK K) := by
  classical
  let f : EuclideanSpace ℂ ι → EuclideanSpace ℝ (Fin (dK K)) :=
    fun u => if h : u ∈ K then (ob K).repr ⟨u, h⟩ else 0
  have hf : ∀ u (h : u ∈ K), f u = (ob K).repr ⟨u, h⟩ := fun u h => by simp [f, h]
  have hinj : Set.InjOn f S := by
    intro u hu v hv huv
    rw [hf u (hS u hu), hf v (hS v hv)] at huv
    exact congrArg Subtype.val ((ob K).repr.injective huv)
  have hcard := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply hP (dK K) (S.image f) δ R hδ hδR
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    rw [hf u (hS u hu), LinearIsometryEquiv.norm_map]
    exact hR u hu
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    have huv : u ≠ v := fun h => hxy (by rw [h])
    rw [hf u (hS u hu), hf v (hS v hv), LinearIsometryEquiv.dist_map]
    exact hsep u hu v hv huv
end ReciprocityTheory.ChartRestriction.G.I2.Col
