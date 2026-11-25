-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.symW_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:43.882+00:00
-- url     : https://prove2.me/submissions/04ea5d09-b0f8-4f9c-8dbd-8fe6333ba38f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_BfSmulRight
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX

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
theorem _root_.solution (u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (k) :
    symW (Finsupp.single k 1 + u) = 1 * ((u k : ℂ) + 1) * symW u := by
  have hu : ∀ v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ,
      symW v = ∏ k, ((v k).factorial : ℂ) := fun v => by
    unfold symW
    refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_
    have : v k = 0 := by simpa [Finsupp.mem_support_iff] using hk
    simp [this]
  rw [hu, hu, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => ((u j).factorial : ℂ)) (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k,
      (((Finsupp.single k 1 + u : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) j).factorial : ℂ) =
      ∏ j ∈ Finset.univ.erase k, ((u j).factorial : ℂ) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    simp [Finsupp.single_apply, Ne.symm hjk]
  rw [hrest]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [add_comm 1 (u k), Nat.factorial_succ]
  push_cast; ring
end PositivityTheory.Rg.Sw.LC.CoreC
