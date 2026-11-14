-- Prove2me | solution 1 for SeymourThomas1993.haven_of_not_treewidth_le
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T20:00:12.022669+00:00
-- url     : https://prove2.me/submissions/618b7b9e-b2d5-4348-a5b2-7511ae54a958

import Theorems.Thm_SeymourThomas1993_bramble_of_not_treewidth_le
import Theorems.Thm_SeymourThomas1993_haven_of_bramble
set_option autoImplicit false
open StableMSR.Recovery.Havens RobertsonSeymour1986.GM5

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    ∃ β : Finset V → Finset V, Haven G (w+2) β := by
  obtain ⟨family,hB,horder⟩ := SeymourThomas1993.bramble_of_not_treewidth_le G w hwidth
  exact SeymourThomas1993.haven_of_bramble hB horder
