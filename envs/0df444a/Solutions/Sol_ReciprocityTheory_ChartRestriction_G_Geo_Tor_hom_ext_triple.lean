-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.hom_ext_triple
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:48.849796+00:00
-- url     : https://prove2.me/submissions/cfb3655f-685e-4b4b-b90c-42c6fcb27e80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {S : Scheme.{0}} (G : Over S) {X : Scheme.{0}} {a b : X ⟶ (G3 G).left}
    (h : ∀ i, a ≫ (x3 G i).left = b ≫ (x3 G i).left) : a = b := by
  have w : b ≫ (G3 G).hom = a ≫ (G3 G).hom := by
    have h0 := h 0
    have k := Over.w (x3 G 0)
    rw [← k, ← Category.assoc, ← Category.assoc, h0]
  let T : Over S := Over.mk (a ≫ (G3 G).hom)
  let A : T ⟶ G3 G := Over.homMk a rfl
  let B : T ⟶ G3 G := Over.homMk b w
  have hAB : A = B := by
    apply CartesianMonoidalCategory.hom_ext
    · ext
      simpa [A, B, x3] using h 0
    · apply CartesianMonoidalCategory.hom_ext
      · ext
        simpa [A, B, x3] using h 1
      · ext
        simpa [A, B, x3] using h 2
  exact congrArg CommaMorphism.left hAB
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
