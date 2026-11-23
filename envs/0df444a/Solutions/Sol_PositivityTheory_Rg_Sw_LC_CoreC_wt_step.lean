-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.wt_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:25.652834+00:00
-- url     : https://prove2.me/submissions/783c3614-83d2-4796-81ff-419bf88d6dca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreC_wt_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) (k : Fin m × Fin n × Bool) :
    (wt c (Finsupp.single k 1 + s) : ℂ) = ((2 * c : ℝ) : ℂ) * ((s k : ℂ) + 1) * (wt c s : ℂ) := by
  have h : wt c (Finsupp.single k 1 + s) = (2 * c) * ((s k : ℝ) + 1) * wt c s := by
    rw [wt_univ, wt_univ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun j => ((s j).factorial : ℝ) * (2 * c) ^ (s j)) (Finset.mem_univ k)]
    have hrest : ∏ j ∈ Finset.univ.erase k, (((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j).factorial : ℝ) *
          (2 * c) ^ ((Finsupp.single k 1 + s : Fin m × Fin n × Bool →₀ ℕ) j) =
        ∏ j ∈ Finset.univ.erase k, ((s j).factorial : ℝ) * (2 * c) ^ (s j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjk : j ≠ k := Finset.ne_of_mem_erase hj
      simp [Finsupp.single_apply, Ne.symm hjk]
    rw [hrest]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [add_comm 1 (s k), Nat.factorial_succ, pow_succ]
    push_cast; ring
  rw [h]; push_cast; ring
end PositivityTheory.Rg.Sw.LC.CoreC
