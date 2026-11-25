-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_chartMonomial_mem_of_not_isLive_a21aa707419f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:22.06084+00:00
-- url     : https://prove2.me/submissions/989c706b-d0e4-4006-b363-e0b33223a991

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExtMapLiftOldOfIsWeightedHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.AddBlockData
variable {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : ¬ P.IsLive c)
    {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  obtain ⟨k, hk⟩ : ∃ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
    simpa [ArithVariety.IsLive] using hc
  exact P.ideal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
    (P.ideal.pow_mem_of_mem hk (d k) (hd k))
end GroundTheory.Heights₂.Heights.AddBlockData
