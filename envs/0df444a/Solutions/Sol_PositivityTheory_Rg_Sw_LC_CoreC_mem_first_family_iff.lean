-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreC.mem_first_family_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:26:47.360826+00:00
-- url     : https://prove2.me/submissions/2afe0204-ba1d-45cf-b435-07b303b09666

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoeffSmulX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivZeroSecondFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finsupp
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw.LC.CoreC
open PositivityTheory.Rg.Sw G
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreC
theorem _root_.solution (ε : Fin m → Bool) (p : PX m n) : p ∈ F1 ε ↔ ∀ s ∈ p.support, ∀ k ∈ s.support, inF1 ε k := by
  unfold F1
  rw [Subalgebra.mem_toSubmodule, MvPolynomial.mem_supported]
  constructor
  · intro h s hs k hk; exact h (mem_vars k |>.mpr ⟨s, hs, hk⟩)
  · intro h k hk; obtain ⟨s, hs, hk'⟩ := (mem_vars k).mp hk; exact h s hs k hk'
end PositivityTheory.Rg.Sw.LC.CoreC
