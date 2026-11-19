-- Prove2me | solution 1 for RobertsonSeymour1986.GM5.excluding_planar_graph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-18T12:50:56.986569+00:00
-- url     : https://prove2.me/submissions/d5faa267-b4c0-4133-97e9-c2eb58ad217e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_Params
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_RobertsonSeymour1986_GM5_treewidth_le_theta9
import Theorems.Thm_RobertsonSeymour1986_GM5_isMinor_trans

open RobertsonSeymour1986.GM5 in
theorem solution {W : Type} [Fintype W] (H : SimpleGraph W) (hH : IsPlanar H)
    (θ : ℕ) (hθ : IsLeast {t : ℕ | Even t ∧ 6 ≤ t ∧ IsMinor H (grid t)} θ)
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : ¬ IsMinor H G) :
    TreewidthLE G (theta9 θ) :=
  treewidth_le_theta9 G θ hθ.1.1 hθ.1.2.1 (fun hgrid => hG (isMinor_trans hθ.1.2.2 hgrid))
