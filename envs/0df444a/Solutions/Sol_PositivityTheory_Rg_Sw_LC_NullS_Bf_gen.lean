-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.Bf_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:25.867815+00:00
-- url     : https://prove2.me/submissions/abcaad58-f23c-4321-8fa2-26d307029c2d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sumT
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_NullS_sumT__9219b03eb577
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_ite_mem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_partial_deriv_quadratic_pairing
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
theorem _root_.solution (ε : Fin m → Bool) (i j k l k' l' : Fin n) :
    Bf ε i j (Qp ε k l) (Qp ε k' l') ∈ QA ε := by
  simp only [Bf, pd_Qp_f, partial_deriv_quadratic_pairing, mul_add, Finset.sum_add_distrib, sumT, sumT']
  exact add_mem (ite_mem _ _ _ _) (ite_mem _ _ _ _)
end PositivityTheory.Rg.Sw.LC.NullS
