-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.CoreBb.collapse
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:24.42006+00:00
-- url     : https://prove2.me/submissions/10c1c135-e411-4a87-815e-2ce2318ed4c0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
theorem _root_.solution (P : Fin m → Prop) [DecidablePred P] (c : Fin n) (b : Bool) (F : Fin m → PX m n)
    (k : Fin m × Fin n × Bool) :
    ∑ a ∈ Finset.univ.filter P, (if k = (a, c, b) then F a else 0) =
      if P k.1 ∧ k.2.1 = c ∧ k.2.2 = b then F k.1 else 0 := by
  rw [Finset.sum_filter, Finset.sum_eq_single k.1]
  · obtain ⟨a, c', b'⟩ := k
    by_cases hP : P a <;> by_cases hc : c' = c <;> by_cases hb : b' = b <;> simp [hP, hc, hb]
  · intro a _ ha
    split_ifs with h1 h2
    · exact absurd (by rw [h2]) ha
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h
end PositivityTheory.Rg.Sw.LC.CoreBb
