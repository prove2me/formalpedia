-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.pderiv_false_AT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:23.559111+00:00
-- url     : https://prove2.me/submissions/c9a3cb48-95d7-469d-893c-75fbbe15689e

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
theorem _root_.solution {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (false, a, d) Q = 0 := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact pderiv_X_of_ne (by simp)
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
end PositivityTheory.Rg.Sw.SP
