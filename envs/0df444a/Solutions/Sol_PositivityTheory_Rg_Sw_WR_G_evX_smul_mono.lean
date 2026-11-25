-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.evX_smul_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:58.42637+00:00
-- url     : https://prove2.me/submissions/47003e9c-3fef-43c6-9526-694c53c03b54

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousGramX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G
theorem _root_.solution {m n : ℕ} (ζ : ℂ) (d : (Fin m × Fin n × Bool) →₀ ℕ) (hd : ∀ k, k.2.2 = true → d k = 0)
    (x : Fin m → Fin n → ℂ) :
    evX (monomial d 1) (ζ • x) = ζ ^ (d.sum fun _ e => e) * evX (monomial d 1) x := by
  unfold evX
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, one_mul, one_mul, Finsupp.prod, Finsupp.prod,
    Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk => ?_
  have hk2 : k.2.2 = false := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hk) (hd k (by simpa using h))
  simp [hk2, mul_pow]
end PositivityTheory.Rg.Sw.WR.G
