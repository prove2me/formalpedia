-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.exists_ptJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:18.088465+00:00
-- url     : https://prove2.me/submissions/ff416eb7-0262-4061-b5be-c0a845d7c8a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_pj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jP_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {σ τ : Type} [Finite σ] [Finite τ]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) {n l : ℕ}
variable {x} (hx : IsUnivChart G d x)
include hx
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (y : ∀ m, sp (R₀ := R) (JetR R (Fin n × Fin d) m) ⟶ G) (h₀ : ∀ m, spMap (jetAug R _ m) ≫ y m = 1)
    (h₁ : ∀ m, spMap (jetTruncR R _ m) ≫ y (m + 1) = y m) : ∃ p : Q R d n, ∀ m, ptJ x m p = y m := by
  choose ψ hψ hu using fun m => hx.2.2 _ (jetAug R _ m) m (ker_jetAug_pow _ m) _ (h₀ m)
  have at' : ∀ κ m, (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) := fun κ m =>
    jet_ext fun j => (jetAug_zR m j).trans (jetAug_zR (m + 1) j).symm
  have cmp : ∀ m, (jetTruncR R _ m).comp (ψ (m + 1)) = (ψ m).comp (jetTruncR R _ m) := fun m =>
    (hx.2.2 _ (jetAug R _ m) (m + 1) (le_bot_iff.1 ((Ideal.pow_le_pow_right (Nat.le_succ _)).trans (ker_jetAug_pow _ m).le))
      _ (h₀ m)).unique
      ⟨by rw [← AlgHom.comp_assoc, at', (hψ _).1], by rw [← spMap_comp, Category.assoc, ← (hψ _).2, h₁]⟩
      ⟨by rw [← AlgHom.comp_assoc, (hψ _).1, at'], by rw [← spMap_comp, Category.assoc, hx.1, ← (hψ _).2]⟩
  choose f hf using fun j => exists_pj (fun m => ψ m (zR m j)) fun m => AlgHom.congr_fun (cmp m) (zR (m + 1) j)
  refine ⟨⟨f, fun j => ?_⟩, fun m => ?_⟩
  · rw [← aug_pj 0, hf]; exact (AlgHom.congr_fun (hψ 0).1 _).trans (jetAug_zR 0 j)
  · rw [(hψ m).2, ptJ]
    exact congrArg (fun g => spMap g ≫ x m) (jet_ext fun j => (jP_zR _ _ j).trans (hf j m))
end ReciprocityTheory.ChartRestriction.G.Chart
