-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_precomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:02:36.463584+00:00
-- url     : https://prove2.me/submissions/6b06c917-3403-414e-9edb-f6bab9065c2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_jet__loc_e980629664a9
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_hom_ext_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_nbhdPt_closedPoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_spec_comp_nbhdPt


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (hol' : IsHolFam e')
    (h0 : e' 0 = e 0) (m : ℕ) (χ : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) [hχl : IsLocalHom χ]
    (hχ : ∀ (U : Y.Opens) (_ : e 0 cpt ∈ U) (f : Γ(Y, U)),
      χ (jetOf m (fun z => valAt' (e z) U f)) = jetOf m (fun z => valAt' (e' z) U f)) :
    spMap χ ≫ jetPt e hol m = jetPt e' hol' m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom χ) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom χ :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom χ) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol m U hU f (hχl.map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hpt' := nbhdPt_closedPoint (y₀ := e' 0 cpt) _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m)
  refine hom_ext_of_local (hpt.trans (by rw [hpt', h0])) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  have hU' : e' 0 cpt ∈ U := by rw [h0]; exact hU
  rw [nbhdPt_appLE _ hres hloc U hU h₁, nbhdPt_appLE _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m) U hU' h₂]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact hχ U hU f
end ReciprocityTheory.ChartRestriction.G.PullbackSections
