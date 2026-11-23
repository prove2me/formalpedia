-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.fun_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:44.109904+00:00
-- url     : https://prove2.me/submissions/e5909f8f-5301-496e-8453-70cfb85bca37

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem

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
theorem _root_.solution (ε : Fin m → Bool) (f : PX m n → PX m n) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hmul : ∀ x y, f (x * y) = x * f y + y * f x) (hC : ∀ r : ℂ, f (algebraMap ℂ (PX m n) r) = 0)
    (hgen : ∀ i j, f (Qp ε i j) ∈ QA ε) : ∀ R ∈ QA ε, f R ∈ QA ε := by
  intro R hR
  induction hR using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨⟨i, j⟩, rfl⟩ := hx; exact hgen i j
  | algebraMap r => rw [hC]; exact zero_mem _
  | add x y _ _ hx hy => rw [hadd]; exact add_mem hx hy
  | mul x y hx' hy' hx hy => rw [hmul]; exact add_mem (mul_mem hx' hy) (mul_mem hy' hx)
end PositivityTheory.Rg.Sw.LC.NullS
