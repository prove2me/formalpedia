-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.pderiv_true_AT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:25.714898+00:00
-- url     : https://prove2.me/submissions/b434032f-5439-44ae-ba79-3d103dbf76d8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (true, a, d) Q ∈ AT n := by
  classical
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx' hy) (Subalgebra.mul_mem _ hy' hx)
end PositivityTheory.Rg.Sw.SP
