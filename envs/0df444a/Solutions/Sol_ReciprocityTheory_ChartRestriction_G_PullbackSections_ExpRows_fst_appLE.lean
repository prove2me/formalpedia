-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.fst_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:33:38.995626+00:00
-- url     : https://prove2.me/submissions/7421a99d-cb29-42e6-a1b2-c96a2a6179dd

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_specMap_comp_appLE


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
open AlgebraicGeometry CategoryTheory Opposite NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped MonObj
variable {g : ℕ} {Y : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (U : Y.Opens) (hU : ⊤ ≤ (e 0) ⁻¹ᵁ U) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(Y, U)) :
    TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h f)) =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ hU f) := by
  have he : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 := hv.1
  have hh : ∀ {a b : Sp ℂ ⟶ Y} (_ : a = b) (h1 : ⊤ ≤ a ⁻¹ᵁ U) (h2 : ⊤ ≤ b ⁻¹ᵁ U),
      a.appLE U ⊤ h1 = b.appLE U ⊤ h2 := by
    intro a b hab h1 h2
    subst hab
    rfl
  have h0 : ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
    rw [he]
    exact hU
  have key := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h
  rw [← hh he h0 hU]
  have key2 := congrArg (fun φ => φ.hom f) key
  first
  | exact key2.symm
  | simpa using key2.symm
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
