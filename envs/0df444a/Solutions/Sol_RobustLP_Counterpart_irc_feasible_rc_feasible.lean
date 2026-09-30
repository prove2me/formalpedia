-- Prove2me | solution 1 for RobustLP.Counterpart.irc_feasible_rc_feasible
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:25:19.427064+00:00
-- url     : https://prove2.me/submissions/29627ab5-f627-4027-9de8-cf2abdd74e39

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts
open scoped BigOperators

namespace RobustLP.Counterpart

/-- **(RC) is less conservative than (IRC)** (Ben-Tal–Nemirovski 2000, §3.1, p. 420). For
`ε > 0`, `δ > 0`, `Ω > 0`: if `(x, y)` is feasible for (IRC[ε, δ]), then `(x, y', z')` with
`y'_{ij} = y_j` and `z'_{ij} = 0` is feasible for (RC[ε, δ, Ω]). -/
theorem _root_.solution {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω) (x y : Fin n → ℝ)
    (hIRC : L.IRCFeasible ε δ x y) :
    L.RCFeasible ε δ Ω x (fun _ j => y j) (fun _ _ => 0) := by
  rcases hIRC with ⟨hE, hA, hb, hy, hbox⟩
  refine ⟨hE, hA, ?_, hbox, ?_⟩
  · simpa using hb
  · simpa using (fun (i : Fin m) (j : Fin n) => hy j)

end RobustLP.Counterpart
