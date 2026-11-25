-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.wC_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:56:59.918843+00:00
-- url     : https://prove2.me/submissions/d9708291-7418-4474-a3da-b728f5422fc2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_GaussianMomentRecurrence
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hC_comm
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_hC_rel
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_wC_split
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
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (u : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    wC c (Finsupp.single k 1 + u) = (2 * c : ℂ) * (u (flip k) : ℂ) * wC c (u - Finsupp.single (flip k) 1) := by
  obtain ⟨a, i, b⟩ := k
  rw [wC_split c _ a i, wC_split c _ a i]
  have hrest : ∏ x ∈ Finset.univ.erase (a, i), hC c ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) =
      ∏ x ∈ Finset.univ.erase (a, i), hC c ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, false))
        ((u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, true)) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    have hx' := (Finset.mem_erase.1 hx).1
    have key : ∀ b', (Finsupp.single (a, i, b) 1 + u : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') = (u - Finsupp.single (flip (a, i, b)) 1 : Fin m × Fin n × Bool →₀ ℕ) (x.1, x.2, b') := by
      intro b'
      have h1 : (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp at this; exact this.symm)
      have h2 : flip (a, i, b) ≠ (x.1, x.2, b') := fun h => hx' (by
        have := congrArg (fun y : Fin m × Fin n × Bool => (y.1, y.2.1)) h; simp [flip] at this; exact this.symm)
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        if_neg h1, if_neg h2, tsub_zero, zero_add]
    rw [key false, key true]
  rw [hrest, ← mul_assoc]
  congr 1
  have e1 : (a, i, true) ≠ (a, i, false) := by simp
  cases b
  · simp only [flip, Bool.not_false, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [add_comm]
    exact hC_rel c _ _
  · simp only [flip, Bool.not_true, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.single_apply, if_pos, if_neg e1, if_neg e1.symm, tsub_zero, zero_add]
    rw [hC_comm c (u (a, i, false)), hC_comm c (u (a, i, false) - 1), add_comm]
    exact hC_rel c _ _
end PositivityTheory.Rg.Sw.LC
