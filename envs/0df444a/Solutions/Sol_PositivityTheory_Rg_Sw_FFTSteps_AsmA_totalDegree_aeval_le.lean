-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.totalDegree_aeval_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:02.698142+00:00
-- url     : https://prove2.me/submissions/c8d64d1c-42ba-41b8-a60f-f8baaa7d2e89

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution {σ τ : Type} (φ : σ → MvPolynomial τ ℂ) (h : ∀ v, (φ v).totalDegree ≤ 1)
    (p : MvPolynomial σ ℂ) : (aeval φ p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (algebraMap ℂ (MvPolynomial τ ℂ) (coeff m p)).totalDegree = 0 := by
    rw [MvPolynomial.algebraMap_eq]; exact totalDegree_C _
  rw [h1, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (h i))) ?_
  simp only [mul_one]
  exact le_totalDegree hm
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
