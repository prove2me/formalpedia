-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.K_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:44.144234+00:00
-- url     : https://prove2.me/submissions/6d46035f-83f2-4e46-875a-8d370feba72a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_line
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_iteratedDeriv_poly_real_zero

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
theorem _root_.solution {N : ℕ} (K : EuclideanSpace ℝ ι → ℂ) (hK : ContDiff ℝ N K) (ξ : EuclideanSpace ℝ ι)
    (p : Polynomial ℂ) (hp : p.natDegree ≤ N) (hpK : ∀ t : ℝ, K (t • ξ) = p.eval (t : ℂ)) :
    K ξ = ∑ k ∈ Finset.range (N + 1), ((k.factorial : ℂ))⁻¹ * iteratedFDeriv ℝ k K 0 (fun _ => ξ) := by
  have h1 : K ξ = p.eval 1 := by simpa using hpK 1
  rw [h1, Polynomial.eval_eq_sum_range' (n := N + 1) (by omega)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ N := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hk
  have e : (fun t : ℝ => K (t • ξ)) = fun t : ℝ => p.eval (t : ℂ) := funext hpK
  rw [← iteratedDeriv_line K hK ξ hk', e, iteratedDeriv_poly_real_zero]
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp
  simp
end PositivityTheory.SiegelWeilFormula.KFPB
