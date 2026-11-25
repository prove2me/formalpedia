-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.Bf_der
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:10.123692+00:00
-- url     : https://prove2.me/submissions/f4afe903-3ade-4925-bc94-cba7fbbb4032

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_fun_mem

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
theorem _root_.solution (ε : Fin m → Bool) (i j : Fin n) (U : PX m n) (hU : ∀ k l, Bf ε i j U (Qp ε k l) ∈ QA ε) :
    ∀ V ∈ QA ε, Bf ε i j U V ∈ QA ε :=
  fun_mem ε _ (fun x y => by simp only [Bf, map_add, mul_add, ← Finset.sum_add_distrib];
                             exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y => by simp only [Bf, Derivation.leibniz, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib];
                   exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun r => by simp [Bf]) hU
end PositivityTheory.Rg.Sw.LC.NullS
