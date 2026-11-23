-- Prove2me | solution 1 for P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:54.305087+00:00
-- url     : https://prove2.me/submissions/1c6eb48f-f1f1-4a16-83ad-f8835d2affa4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
namespace GlobalTheory.SelfCube
theorem _root_.solution {g : ℕ} {α : Type*} {f : α → (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)}
    (s : Finset α) (hf : ∀ i, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const 1
  | insert a s ha ih => simp only [Finset.prod_insert ha]; exact (hf a).mul ih
end GlobalTheory.SelfCube
