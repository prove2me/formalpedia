-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.flatIso_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:03.808341+00:00
-- url     : https://prove2.me/submissions/553b8438-260e-4e28-b325-df96d010228d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comm_alg
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_gm_pull_g__87f367b34377
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) {K : Type} [Fintype K] (ε : K → ℤ) :
    (flatIso L₁ L₂ f₁ f₂ w ε).IsGen := by
  have hP := (isGen_iff w).1 hw
  intro (p : (K → L₁.ι) × (K → L₂.ι)) (q : (K → L₁.ι) × (K → L₂.ι))
  apply unit_ext
  intro y hy
  have hp : y ∈ LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 := hy.1
  have hq : y ∈ LB.wchart L₁ (fun _ : K => f₁) q.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) q.2 := hy.2
  show gm (𝟙 Y) y _ (res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k))) =
    gm (𝟙 Y) y _ ((res _ ((LB.LinComb L₁ (fun _ : K => f₁) ε).g p.1 q.1) *
      (res _ ((LB.LinComb L₂ (fun _ : K => f₂) ε).g p.2 q.2))⁻¹) *
      res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ q k) (w.s (fun _ => q.2 k, fun _ => q.1 k)) ^ (-ε k)))
  erw [map_mul, map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy,
    gm_linComb L₁ _ ε (𝟙 Y) y p.1 q.1 hp.1 hq.1, gm_linComb L₂ _ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2]
  erw [map_prod, map_prod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : f₁ y ∈ L₁.U (p.1 k) := Set.mem_iInter.1 hp.1 k
  have h1' : f₁ y ∈ L₁.U (q.1 k) := Set.mem_iInter.1 hq.1 k
  have h2 : f₂ y ∈ L₂.U (p.2 k) := Set.mem_iInter.1 hp.2 k
  have h2' : f₂ y ∈ L₂.U (q.2 k) := Set.mem_iInter.1 hq.2 k
  have e := hP Y (𝟙 Y) y (p.2 k) (q.2 k) (fun _ => p.1 k) (fun _ => q.1 k) (by simpa using h2) (by simpa using h2')
    (Set.mem_iInter.2 fun _ => by simpa using h1) (Set.mem_iInter.2 fun _ => by simpa using h1')
  rw [gm_pull_g' L₁ f₁ (𝟙 Y) y (p.1 k) (q.1 k) (by simpa using h1) (by simpa using h1')] at e
  rw [map_zpow, map_zpow]
  erw [gm_res _ y _ hp, gm_res _ y _ hq]
  change gw w (𝟙 Y) y (p.2 k) (fun _ => p.1 k) ^ (-ε k) = _ * _ * gw w (𝟙 Y) y (q.2 k) (fun _ => q.1 k) ^ (-ε k)
  rw [e]
  simp only [Category.id_comp]
  exact comm_alg _ _ _ _
end ReciprocityTheory.ChartRestriction.G.DVR
