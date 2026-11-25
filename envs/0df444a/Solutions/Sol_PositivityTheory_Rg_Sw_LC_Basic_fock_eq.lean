-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Basic.fock_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:58:20.336434+00:00
-- url     : https://prove2.me/submissions/096f5e15-8b25-4de2-8d3c-874c17000b78

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Basic_fockMono_eq

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Basic
theorem _root_.solution (c : ℝ) (p : PX m n) : fock c p = ((phi c p : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by
  conv_rhs => rw [p.as_sum]
  rw [map_sum, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply, fockMono_eq]
end PositivityTheory.Rg.Sw.LC.Basic
