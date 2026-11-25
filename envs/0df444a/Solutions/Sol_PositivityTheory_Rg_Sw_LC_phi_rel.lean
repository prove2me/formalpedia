-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.phi_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:54.564301+00:00
-- url     : https://prove2.me/submissions/8b88eb0f-4399-4a1d-acb6-dc3813598387

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_gaussian_moment_symm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_gaussian_moment_recurrence
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_phi_split
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_rest_congr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_flip_flip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LC.flip_flip



set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (hc : 0 < c) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (u k : ℂ) * phi c (u - Finsupp.single k 1) = (c : ℂ) * phi c (Finsupp.single (flip k) 1 + u) := by
  obtain ⟨a, i, b⟩ := k
  rw [phi_split c _ a i, phi_split c _ a i,
    rest_congr c (u - Finsupp.single (a, i, b) 1) (Finsupp.single (flip (a, i, b)) 1 + u) a i (fun x hx b' => by
      have h1 : (x.1, x.2, b') ≠ (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa using this)
      have h2 : (x.1, x.2, b') ≠ flip (a, i, b) := fun h => hx (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simpa [flip] using this)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg (Ne.symm h1), if_neg (Ne.symm h2), tsub_zero, zero_add])]
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  cases b
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact gaussian_moment_recurrence c hc _ _
  · have e1 : (a, i, true) ≠ (a, i, false) := by simp
    simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [gaussian_moment_symm c _ (u (a, i, true) - 1), gaussian_moment_symm c (1 + u (a, i, false)), add_comm]
    exact gaussian_moment_recurrence c hc _ _
end PositivityTheory.Rg.Sw.LC
