-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.fL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:31.055231+00:00
-- url     : https://prove2.me/submissions/c6612c17-3610-4bc3-9cf2-dc4adc28a150

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_pderiv_X_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_Bf_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_pd_Qp_f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) : ∀ R ∈ QA ε, fL ε i j R ∈ QA ε := by
  intro R hR
  induction hR using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, l⟩, rfl⟩ := hx
    have : fL ε i j (Qp ε k l : PX m n) =
        ∑ a, C (sgn ε a) * pderiv (a, j, true) (if l = i then C (sgn ε a) * X (a, k, true) else 0) := by
      simp only [fL, pd_Qp_f]
    rw [this]
    refine sum_mem fun a _ => mul_mem (by simpa using (algebraMap_mem (QA ε) (sgn ε a))) ?_
    split_ifs
    · rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
      exact mul_mem (by simpa using (algebraMap_mem (QA ε) (sgn ε a))) (pderiv_X_mem ε _ _)
    · simp
  | algebraMap r => simp [fL]
  | add x y _ _ hx hy => simpa [fL, mul_add, Finset.sum_add_distrib] using add_mem hx hy
  | mul x y hx' hy' hx hy =>
    have e : fL ε i j (x * y) = x * fL ε i j y + y * fL ε i j x + Bf ε i j x y := by
      simp only [fL, Bf, Derivation.leibniz, smul_eq_mul, map_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    exact add_mem (add_mem (mul_mem hx' hy) (mul_mem hy' hx)) (Bf_mem ε i j x hx' y hy')
end PositivityTheory.Rg.Sw.LC.NullS
