-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.ArcWit.uwIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:38.575774+00:00
-- url     : https://prove2.me/submissions/3fa677f8-299a-4a65-a634-f63b9017989d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabMap_iso

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
open scoped CategoryTheory.Obj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace ArcWit
theorem _root_.solution {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
    {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {f : O' →+* R} {u : R} {χ : Sp R ⟶ Y.X}
    (W W' : ArcWit Y a I f u χ) :
    ∃ ψ : W.t.G ≅ W'.t.G, ψ.hom.left ≫ W'.m.φ = W.m.φ ∧ IsMonHom ψ.hom ∧
      (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) ∧
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y.m.φ) ∧
      ∃ (he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G)
        (wL : LB.Iso W.P.U.LG.L (W'.P.U.LG.L.pull ψ.hom.left)),
        wL.IsGen ∧ LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec W.t.G) (fun _ => 1)) W.P.U.LG.rig
          (rigPullOf ψ.hom.left (𝟙 _) he W'.P.U.LG.L W'.P.U.LG.rig) := by
  obtain ⟨ψ, hmon, hφ, hact, he, wL, hgen, hmaps⟩ :=
    sabMap_iso W.m W'.m (L₁ := W.P.U.LG) (L₂ := W'.P.U.LG) W.P.bundle W'.P.bundle
  refine ⟨ψ, hφ, hmon, hact, fun T g g₁ g₂ h1 h2 h3 => ?_, he, wL, hgen, hmaps⟩
  rw [hφ, h1]

  have hc := Y.m0.toSABMap.cart
  unfold IsGrpPullback at hc
  unfold SABMap.φ at h2
  rw [hc.1.hom_ext h2 h3]
end ArcWit
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
