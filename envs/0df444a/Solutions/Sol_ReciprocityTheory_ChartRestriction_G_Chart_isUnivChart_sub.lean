-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isUnivChart_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:51.52939+00:00
-- url     : https://prove2.me/submissions/82409fff-fbd0-4c0f-92c0-f05e18301c7f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_RestrictDiagCompInclFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetSub_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetSub_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_jetSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_trunc_comp_jetSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zero_comp_jetSub
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {n d : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (T : (Fin d → R) ≃ₗ[R] (Fin n → R)) :
    IsUnivChart G d (fun m => spMap (jetSub T.toLinearMap m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · show spMap (jetTruncR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap (m + 1)) ≫ x (m + 1) =
      spMap (jetSub T.toLinearMap m) ≫ x m
    rw [← Category.assoc, spMap_comp, trunc_comp_jetSub, ← spMap_comp, Category.assoc, hx.1 m]
  · show spMap (jetZeroR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap m) ≫ x m = 1
    rw [← Category.assoc, spMap_comp, zero_comp_jetSub, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']
  · intro A _ _ aug m hA y hy
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := hx.2.2 A aug m hA y hy
    have e1 : (jetSub T.symm.toLinearMap m).comp (jetSub T.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    have e2 : (jetSub T.toLinearMap m).comp (jetSub T.symm.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    refine ⟨ψ.comp (jetSub T.symm.toLinearMap m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψ1, jetAug_comp_jetSub]
    · show y = spMap (ψ.comp (jetSub T.symm.toLinearMap m)) ≫ spMap (jetSub T.toLinearMap m) ≫ x m
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e1, AlgHom.comp_id]
      exact hψ2
    · rintro φ ⟨hφ1, hφ2⟩
      have hφ2' : y = spMap φ ≫ spMap (jetSub T.toLinearMap m) ≫ x m := hφ2
      have hφ : φ.comp (jetSub T.toLinearMap m) = ψ := by
        apply hψu
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, hφ1, jetAug_comp_jetSub]
        · rw [hφ2', ← Category.assoc, spMap_comp]
      rw [← hφ, AlgHom.comp_assoc, e2, AlgHom.comp_id]
end ReciprocityTheory.ChartRestriction.G.Chart
