-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.locDens_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:45.87944+00:00
-- url     : https://prove2.me/submissions/637cd9ba-bba9-4617-93cf-672b7a5a893a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt

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
open scoped ContDiff ComplexOrder
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas (e + 1) X) (P : LocPot X) (Φ : Fin e → LocPot X)
    (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) j y = ((e + 1).factorial : ℝ) * (2 / Real.pi) ^ (e + 1) *
      (mdisc (Fin.cons (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)
        (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) :
          Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)).re := by
  unfold locDens maDens
  congr 3
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp
end ReciprocityTheory.AnForm.M
