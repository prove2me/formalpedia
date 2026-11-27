-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:33:43.608016+00:00
-- url     : https://prove2.me/submissions/3d215f2e-54cb-493a-af27-0fc59361e0ef

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ExpRowsPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_ExpRows_dual_top_le
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
    (hv : IsDerivAt0 e w v) (cc : ℂ) : IsDerivAt0 e (cc • w) (spMap (epsMul cc) ≫ v) := by
  have hcomp : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsMul cc) =
      (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    RingHom.ext fun x => by simp [epsMul]
  refine ⟨?_, fun U h f => ?_⟩
  · rw [← Category.assoc, ← hv.1]
    congr 1
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  · have hp : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ U := by
      have hx := h (show IsLocalRing.closedPoint (DualNumber ℂ) ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
      have hc : (spMap (epsMul cc)).base (IsLocalRing.closedPoint (DualNumber ℂ)) =
          IsLocalRing.closedPoint (DualNumber ℂ) :=
        IsLocalRing.comap_closedPoint (epsMul cc)
      first
      | (rw [← hc]; exact hx)
      | (simp only [Scheme.Hom.mem_preimage, Scheme.comp_base_apply] at hx ⊢; rwa [hc] at hx)
    have hq : ⊤ ≤ v ⁻¹ᵁ U := dual_top_le _ hp
    have key := congrArg (fun φ => φ.hom f) (specMap_comp_appLE (CommRingCat.ofHom (epsMul cc)) v U h hq)
    have hd := hv.2 U hq f
    simp only at key
    rw [map_smul, ← hd]
    show TrivSqZeroExt.snd (((spMap (epsMul cc) ≫ v).appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom).hom f) = _
    rw [key]
    first
    | simp [epsMul]
    | rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows
