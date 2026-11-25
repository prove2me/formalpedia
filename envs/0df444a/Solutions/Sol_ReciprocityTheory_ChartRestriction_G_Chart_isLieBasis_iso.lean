-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:28:51.718441+00:00
-- url     : https://prove2.me/submissions/31a70f40-caa1-48f4-8002-d18138b5962c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G')} (hv : IsLieBasis fun i => v i ≫ e.hom) : IsLieBasis v := by
  have tan : ∀ w : epsR R ⟶ G', IsTangent (w ≫ e.hom) ↔ IsTangent w := fun w => by
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [IsTangent, IsTangent, ← IsMonHom.one_hom e.hom, Over.comp_left, Over.comp_left, ← Category.assoc, cancel_mono]
  have pr : ∀ u : Fin n → (epsR R ⟶ G'), (List.ofFn u).prod ≫ e.hom = (List.ofFn fun i => u i ≫ e.hom).prod := fun u =>
    (map_list_prod (IsMonHom.monoidHom e.hom (epsR R)) _).trans (by rw [List.map_ofFn]; rfl)
  have comb : ∀ c w, IsLieComb c (fun i => v i ≫ e.hom) (w ≫ e.hom) ↔ IsLieComb c v w := fun c w => by
    constructor
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => u i ≫ e.inv, fun i => ?_, ?_⟩
      · rw [Over.comp_left, hu, Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
      · rw [← cancel_mono e.hom, pr, hw]; simp
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => u i ≫ e.hom, fun i => by rw [Over.comp_left, hu, Category.assoc]; rfl, pr u⟩
  refine ⟨fun i => (tan _).1 (hv.1 i), fun w hw => ?_⟩
  simpa only [comb] using hv.2 _ ((tan w).2 hw)
end ReciprocityTheory.ChartRestriction.G.Chart
