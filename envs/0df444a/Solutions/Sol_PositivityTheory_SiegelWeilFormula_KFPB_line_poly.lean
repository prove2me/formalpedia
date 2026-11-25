-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.line_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:29.739406+00:00
-- url     : https://prove2.me/submissions/1fb8970c-561b-4f0d-b3e3-a45a0462f361

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_K_eq_sum
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_multi_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {ι : Type} [Fintype ι] (N : ℕ) (K : EuclideanSpace ℝ ι → ℂ) (hK : ContDiff ℝ N K)
    (H : ∀ ξ : EuclideanSpace ℝ ι, ∃ p : Polynomial ℂ, p.natDegree ≤ N ∧ ∀ t : ℝ, K (t • ξ) = p.eval (t : ℂ)) :
    ∃ Q : MvPolynomial ι ℂ, Q.totalDegree ≤ N ∧ ∀ η, K η = MvPolynomial.eval (fun i => ((η i : ℝ) : ℂ)) Q := by
  choose Q hQd hQ using fun k => multi_poly k (iteratedFDeriv ℝ k K 0)
  refine ⟨∑ k ∈ Finset.range (N + 1), MvPolynomial.C (((k.factorial : ℂ))⁻¹) * Q k, ?_, fun η => ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k hk => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    have hk' : k ≤ N := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
    exact (hQd k).trans hk'
  · obtain ⟨p, hp, hpK⟩ := H η
    rw [K_eq_sum K hK η p hp hpK]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, hQ]
end PositivityTheory.SiegelWeilFormula.KFPB
