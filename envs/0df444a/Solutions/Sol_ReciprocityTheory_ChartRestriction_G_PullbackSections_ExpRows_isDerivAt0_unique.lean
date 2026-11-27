-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:59.494238+00:00
-- url     : https://prove2.me/submissions/ca4604ba-91b5-4924-988c-06e12036d78a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_fst_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_tangent_open_preimage_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_hom_ext_of_local


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
theorem _root_.solution {e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e w v) (hv' : IsDerivAt0 e w v') : v = v' := by
  apply hom_ext_of_local
  · have hc : (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).base (IsLocalRing.closedPoint ℂ) =
        IsLocalRing.closedPoint (DualNumber ℂ) :=
      IsLocalRing.comap_closedPoint _
    have e1 := congrArg (fun φ => φ.base (IsLocalRing.closedPoint ℂ)) (hv.1.trans hv'.1.symm)
    have e2 : v ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) =
        v' ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (IsLocalRing.closedPoint ℂ)) := e1
    rw [hc] at e2
    exact e2
  · intro U h₁ h₂
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom]
    ext f
    have hU := tangent_open_preimage_zero hv U h₁
    · exact (fst_appLE hv U hU h₁ f).trans (fst_appLE hv' U hU h₂ f).symm
    · exact (hv.2 U h₁ f).trans (hv'.2 U h₂ f).symm
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
