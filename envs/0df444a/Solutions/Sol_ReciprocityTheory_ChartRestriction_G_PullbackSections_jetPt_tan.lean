-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:40:30.558305+00:00
-- url     : https://prove2.me/submissions/d77a7283-9a3f-4f7f-a2b7-a99115fd08ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_specMap_comp_appLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetTan_jetOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_appLE_congr_hom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetTan
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
variable {Y : Scheme.{0}}
variable {g : ℕ}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (ℓ : Fin 1 × Fin g)
    (v : Sp (DualNumber ℂ) ⟶ Y) (hd : IsDerivAt0 e (Pi.single ℓ.2 1) v) :
    spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) ≫ jetPt e hol (0 + 1) = v := by
  haveI := isLocalHom_jetTan (g := g) ℓ
  haveI hfl : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol (0 + 1) V hV ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) =
      jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol _ U hU f ((isLocalHom_jetTan ℓ).map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hv : v (IsLocalRing.closedPoint _) = e 0 cpt := by
    rw [← hd.1, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
  refine hom_ext_of_local (hpt.trans hv.symm) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  have h0 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v) ⁻¹ᵁ U := by
    have := top_le_of_mem hU
    rwa [← hd.1] at this
  have hfst := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h₂
  rw [appLE_congr_hom hd.1 U h0 (top_le_of_mem hU)] at hfst
  have hf1 : ∀ f, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ (top_le_of_mem hU) f) =
      TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h₂ f)) := fun f => by
    have := ConcreteCategory.congr_hom hfst f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  ext f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).fst = _
    rw [jetTan_jetOf, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      valAt'_of _ _ (top_le_of_mem hU)]
    exact hf1 f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).snd = _
    rw [jetTan_jetOf, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    exact (hd.2 U h₂ f).symm
end ReciprocityTheory.ChartRestriction.G.PullbackSections
