-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isPotential_ofFun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:33.770931+00:00
-- url     : https://prove2.me/submissions/67b830f0-ea97-4643-bb25-a759e0ca822a

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory
open scoped ContDiff
noncomputable section
open FinHolAtlas
variable {e : ℕ} {X : Type*} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (u : X → ℝ) (hu : A.Smooth u) :
    IsPotential A (LocPot.ofFun u) := by
  refine ⟨fun x => hu, fun x x' y _ => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
    fun j => by exact analyticOnNhd_const, fun z _ => by simp [LocPot.ofFun]⟩⟩
end ReciprocityTheory.AnForm.M
