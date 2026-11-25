-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.scale_pow_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:01.712265+00:00
-- url     : https://prove2.me/submissions/1d97dca6-7f08-47d1-b9c7-6a43adf5271f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_pow_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] (x : A) {m M : ℕ} (hm : m ≤ M)
    {y₁ y₂ : sp (R₀ := S) (DualNumber A) ⟶ G} (h : spMap (scaleS (S := S) (x ^ m)) ≫ y₁ = spMap (scaleS (x ^ m)) ≫ y₂) :
    spMap (scaleS (S := S) (x ^ M)) ≫ y₁ = spMap (scaleS (x ^ M)) ≫ y₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm m d, ← scale_pow_add x d m y₁, ← scale_pow_add x d m y₂, h]
end ReciprocityTheory.ChartRestriction.G.Chart
