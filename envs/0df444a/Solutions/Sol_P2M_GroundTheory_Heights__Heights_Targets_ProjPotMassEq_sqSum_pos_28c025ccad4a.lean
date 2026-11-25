-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjPotMassEq_sqSum_pos_28c025ccad4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:45.215521+00:00
-- url     : https://prove2.me/submissions/7cef0510-6851-40ad-ba2e-c9c6bf18f6f9

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
namespace GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
theorem _root_.solution {m : ℕ} {v : Fin (m + 1) → ℂ} (hv : v ≠ 0) : 0 < ∑ l, ‖v l‖ ^ 2 := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hv
  exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hl) 2) (Finset.single_le_sum (f := fun l => ‖v l‖ ^ 2)
    (fun l _ => by positivity) (Finset.mem_univ l))
end GroundTheory.Heights₂.Heights.Targets.ProjPotMassEq
