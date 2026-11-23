-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_isPotential_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:31.889454+00:00
-- url     : https://prove2.me/submissions/2d8071fb-3350-4bd2-82f3-6a534aab54a6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas (e + 1) X) {u : X → ℝ} (hu : A.Smooth u)
    {Φ : Fin e → LocPot X} (hΦ : ∀ i, IsPotential A (Φ i)) :
    ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun u) Φ : Fin (e + 1) → LocPot X) i) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · show IsPotential A (LocPot.ofFun u)
    exact ⟨fun x => hu, fun x x' y _ => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0,
      fun j => analyticOnNhd_const, fun z _ => by simp [LocPot.ofFun]⟩⟩
  · show IsPotential A (Φ i)
    exact hΦ i
end ReciprocityTheory.AnForm.M
