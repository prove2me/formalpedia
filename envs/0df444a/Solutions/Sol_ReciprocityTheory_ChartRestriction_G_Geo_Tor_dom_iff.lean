-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.dom_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:01:34.523148+00:00
-- url     : https://prove2.me/submissions/808123e7-449c-4dd0-96d8-13d67ac6eb42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {O₀ O : Type} [CommRing O₀] [CommRing O] {β₀ : O₀ →+* c.F} {β : O →+* c.F} {b : O₀ →+* O}
    {Yg : Model Xo c β₀} {Y : Model Xo c β} {f : pullback Yg.s (spMap b) ⟶ Y.X} {t₁ : SAB H (pullback Yg.s (spMap b))}
    (m₁ : SABMap t₁ Yg.t (pullback.fst _ _)) (m₂ : SABMap t₁ Y.t f)
    (hc : ∀ (T : Scheme.{0}) (g : T ⟶ t₁.G.left) (g₁ : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Yg.m.φ → g₁ ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
      g₁ ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ m₂.φ = g₂ ≫ Y.m.φ)
    (aF : Xo.XF c ⟶ pullback Yg.s (spMap b)) (haF : aF ≫ pullback.fst _ _ = Yg.j) {T : Scheme.{0}}
    (g : T ⟶ t₁.G.left) (gg : T ⟶ Yg.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left)
    (h₀ : gg ≫ Yg.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ) (h₁ : gg ≫ Yg.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom)
    (hb : g ≫ t₁.G.hom = gg ≫ Yg.oF.t.G.hom ≫ aF) : g ≫ m₁.φ = gg ≫ Yg.m.φ ↔ g ≫ m₂.φ = g₂ ≫ Y.m.φ := by
  refine ⟨fun h => hc T g gg g₂ h h₀ h₁, fun h2 => ?_⟩
  have w1 : (gg ≫ Yg.m.φ) ≫ Yg.t.G.hom = (g ≫ t₁.G.hom) ≫ pullback.fst Yg.s (spMap b) := by
    have e1 := Yg.m.cart.1.w
    have e2 : aF ≫ pullback.fst Yg.s (spMap b) = Yg.jQ ≫ pullback.fst _ _ := haF
    simp only [SABMap.φ, Category.assoc] at e1 ⊢
    rw [e1, reassoc_of% hb, e2]
  let k := m₁.cart.1.lift (gg ≫ Yg.m.φ) (g ≫ t₁.G.hom) w1
  have hk1 : k ≫ m₁.φ = gg ≫ Yg.m.φ := m₁.cart.1.lift_fst _ _ _
  have hk2 : k ≫ t₁.G.hom = g ≫ t₁.G.hom := m₁.cart.1.lift_snd _ _ _
  have hk3 : k ≫ m₂.φ = g₂ ≫ Y.m.φ := hc T k gg g₂ hk1 h₀ h₁
  have hkg : k = g := m₂.cart.1.hom_ext (by rw [hk3, h2]) hk2
  rw [← hkg]
  exact hk1
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
