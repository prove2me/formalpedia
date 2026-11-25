-- Prove2me | solution 1 for PI.OpWords.wtLe_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:13.934128+00:00
-- url     : https://prove2.me/submissions/2a1c9c69-2a37-4aca-b60b-a73a3eec301a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_DivideAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution (K : Type) [Field K] (k : ℕ) (c : ℤ) (s : Set (Pol K k))
    (hs : ∀ f ∈ s, WtLe K k c f) : ∀ f ∈ Submodule.span K s, WtLe K k c f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm a
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hx m h a
    · exact hy m h a
  | smul r x _ hx =>
    intro m hm a
    exact hx m (support_smul hm) a
end PI.OpWords
