-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_blockSum_pos_f3a6ed830dc6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:28.1208+00:00
-- url     : https://prove2.me/submissions/4e5eec65-d1da-4256-a53a-90d7d7609157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEqGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjPotMassEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open scoped ContDiff
open GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)}
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := by
  obtain ⟨i, hi⟩ := hz k
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2)
    (fun i _ => by positivity) (Finset.mem_univ i))
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
