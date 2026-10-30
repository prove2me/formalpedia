-- Prove2me | solution 1 for OPG1808.order_eight_normalized_cycle_prefix001
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T03:05:55.208133+00:00
-- url     : https://prove2.me/submissions/10beb120-3895-4567-8b96-69e2bddf8cb2

import Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix0011
import Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix0010
import Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix0012
import Lean.Elab.Tactic.Omega

open OPG1808

theorem solution
    (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8))
    (htournament : IsTournament D)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin 8, D i (finRotate 8 i))
    (hminimal : ∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
      toLex (fun i ↦ color i (finRotate 8 i)) ≤
        toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r)))))
    (hprefix0 : color (0:Fin 8) (finRotate 8 (0:Fin 8)) = (0:Fin 3))
    (hprefix1 : color (1:Fin 8) (finRotate 8 (1:Fin 8)) = (0:Fin 3))
    (hprefix2 : color (2:Fin 8) (finRotate 8 (2:Fin 8)) = (1:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by
  have hcases : color (3 : Fin 8) (finRotate 8 (3 : Fin 8)) = 0 ∨
      color (3 : Fin 8) (finRotate 8 (3 : Fin 8)) = 1 ∨
      color (3 : Fin 8) (finRotate 8 (3 : Fin 8)) = 2 := by omega
  rcases hcases with h3 | h3 | h3
  · exact OPG1808.order_eight_normalized_cycle_prefix0010
      D color htournament hnoRainbow hcycle hminimal hprefix0 hprefix1 hprefix2 h3
  · exact OPG1808.order_eight_normalized_cycle_prefix0011
      D color htournament hnoRainbow hcycle hminimal hprefix0 hprefix1 hprefix2 h3
  · exact OPG1808.order_eight_normalized_cycle_prefix0012
      D color htournament hnoRainbow hcycle hminimal hprefix0 hprefix1 hprefix2 h3
