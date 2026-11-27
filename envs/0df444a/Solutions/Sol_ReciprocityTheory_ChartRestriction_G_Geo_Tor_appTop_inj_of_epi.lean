-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.appTop_inj_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:18.871818+00:00
-- url     : https://prove2.me/submissions/9d81b4fe-8609-4242-af21-cb45a523fd40

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsVal

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y Z W : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (p : W ⟶ Z) [Epi p] {a b : Γ(Z, ⊤)} (h : p.appTop.hom a = p.appTop.hom b) : a = b := by
  classical

  let R := CommRingCat.of (Polynomial ℤ)
  let g : Γ(Z, ⊤) → (R ⟶ Γ(Z, ⊤)) := fun c =>
    CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) c)
  let φ : Γ(Z, ⊤) → (Z ⟶ Spec R) := fun c => Z.toSpecΓ ≫ Spec.map (g c)
  have hrec : ∀ c, ((Scheme.ΓSpecIso R).inv ≫ (φ c).appTop).hom Polynomial.X = c := by
    intro c
    have e : (Scheme.ΓSpecIso R).inv ≫ (φ c).appTop = g c := by
      simp only [φ, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
        Iso.inv_hom_id_assoc]
    rw [e]
    exact Polynomial.eval₂_X _ _
  have hg : g a ≫ p.appTop = g b ≫ p.appTop := by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro n
      simp [g]
    · simp [g, h]
  have hφ : φ a = φ b := by
    rw [← cancel_epi p]
    simp only [φ]
    rw [← Category.assoc, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
      Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hg]
  rw [← hrec a, ← hrec b, hφ]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
