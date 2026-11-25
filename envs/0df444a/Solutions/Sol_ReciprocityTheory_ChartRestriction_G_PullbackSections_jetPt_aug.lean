-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.jetPt_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:31:16.686893+00:00
-- url     : https://prove2.me/submissions/05d4f717-b500-4b0d-a21c-8c4d248759a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_ValAt_valAt__ne_zero_iff_2a770214a5a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_hom_ext_of_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_jetOf
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
variable {g : ℕ} {Y Y' : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ) :
    spMap ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) ≫ jetPt e hol m = e 0 := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) f) →
        e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply, jetψ_apply] at hf
    change IsUnit ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _) at hf
    rw [jetAug_jetOf] at hf
    exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp hf.ne_zero
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ)) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom
        ((jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) : Jet ℂ (Fin 1 × Fin g) m →+* ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hpt := nbhdPt_closedPoint _ hres hloc
  refine hom_ext_of_local (hpt.trans rfl) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  ext f
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, jetψ_apply]
  change (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) _ = _
  rw [jetAug_jetOf, valAt'_of _ _ h₂]
  rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
