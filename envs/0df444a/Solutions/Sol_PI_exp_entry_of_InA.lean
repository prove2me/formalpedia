-- Prove2me | solution 1 for PI.exp_entry_of_InA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:59.560825+00:00
-- url     : https://prove2.me/submissions/dd609f73-0e23-468f-9093-0b3384f0bf01

import Definitions.Def_Formalism_PeriodIntegrals_HaarDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_ContinuousExpLie
import Theorems.Thm_PI_exp_entry_hasSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
noncomputable section
open PI
open Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI
theorem _root_.solution {X : Mx k r} (i j : Fin (2 * r + k + 1)) (h : ∀ n : ℕ, (X ^ (n + 1)) i j = 0) :
    (NormedSpace.exp X) i j = if i = j then 1 else 0 := by
  have h1 := exp_entry_hasSum X i j
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) (((Nat.factorial 0 : ℂ)⁻¹) * (X ^ 0) i j) := by
    apply hasSum_single 0
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [h m, mul_zero]
  rw [h1.unique h2]
  simp [Matrix.one_apply]
end PI
