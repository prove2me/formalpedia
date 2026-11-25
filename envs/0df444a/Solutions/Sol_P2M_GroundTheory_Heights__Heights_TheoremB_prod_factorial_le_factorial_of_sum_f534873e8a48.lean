-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_prod_factorial_le_factorial_of_sum_f534873e8a48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:22:25.407498+00:00
-- url     : https://prove2.me/submissions/02047634-06ad-445b-84b2-cc21ddc75762

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_PPolarisationBound

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.TheoremB
theorem _root_.solution {σ : Type*} (m : σ →₀ ℕ) (n : ℕ)
    (hm : (m.sum fun _ e => e) = n) :
    (m.prod fun _ e => (e.factorial : ℝ)) ≤ (n.factorial : ℝ) := by
  have hd : (∏ i ∈ m.support, (m i).factorial) ∣ (∑ i ∈ m.support, m i).factorial :=
    Nat.prod_factorial_dvd_factorial_sum _ _
  have hle : (∏ i ∈ m.support, (m i).factorial) ≤ n.factorial := by
    rw [← hm]; exact Nat.le_of_dvd (Nat.factorial_pos _) hd
  show (∏ a ∈ m.support, ((m a).factorial : ℝ)) ≤ (n.factorial : ℝ)
  exact_mod_cast hle
end GroundTheory.Heights₂.Heights.TheoremB
