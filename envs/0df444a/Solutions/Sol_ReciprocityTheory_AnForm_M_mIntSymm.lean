-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntSymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:25.386394+00:00
-- url     : https://prove2.me/submissions/b4a86d3e-390f-4b4d-826d-261ab8c69fdf

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
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
section Chart
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end Chart
private theorem mdisc_comp_perm_potential {D : ℕ} (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    ReciprocityTheory.AnForm.mdisc (B ∘ σ) = ReciprocityTheory.AnForm.mdisc B := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  simp [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : MIntSymmStatement := by
  intro e X _ A Φ σ g
  have hloc : ∀ j y, locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
    intro j y
    unfold locDens maDens
    congr 2
    exact mdisc_comp_perm_potential (fun k => ReciprocityTheory.AnForm.hessC
      (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ
  unfold mInt integralWith
  simp only [hloc]
end ReciprocityTheory.AnForm.M
