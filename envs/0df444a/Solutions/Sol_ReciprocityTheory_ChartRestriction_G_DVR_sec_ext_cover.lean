-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.sec_ext_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:55.741599+00:00
-- url     : https://prove2.me/submissions/4d3adb2b-d950-44f5-84fd-a6f2e80004e8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sec_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Classical
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y : Scheme.{0}} (W : Y.Opens) {ι : Type} (V : ι → Y.Opens) (hle : ∀ i, V i ≤ W)
    (hcov : W ≤ ⨆ i, V i) (a b : Γ(Y, W)) (h : ∀ i, rs (hle i) a = rs (hle i) b) : a = b := by
  obtain ⟨g, -, hu⟩ := sec_glue W V hle hcov (fun i => rs (hle i) a) (fun i j => by
    simp only [rs_rs])
  exact (hu a (fun i => rfl)).trans (hu b (fun i => (h i).symm)).symm
end ReciprocityTheory.ChartRestriction.G.DVR
