-- Prove2me | solution 1 for SeymourThomas1993.bramble_of_not_treewidth_le
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T23:02:14.121219+00:00
-- url     : https://prove2.me/submissions/b859e5ff-e55f-486d-8c1b-5cf65af357c4

import Theorems.Thm_Mazoit2013_flap_system_of_not_treewidth_le
import Theorems.Thm_Mazoit2013_bramble_from_flap_families
set_option autoImplicit false
open StableMSR.Recovery.Brambles StableMSR.Recovery.Havens RobertsonSeymour1986.GM5
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    ∃ family : Finset (Finset V), IsBramble G family ∧ OrderAtLeast family (w+2) := by
  obtain ⟨F,D,hfamilies,hglue,hstar⟩ := Mazoit2013.flap_system_of_not_treewidth_le G w hwidth
  obtain ⟨B,_,hB,horder⟩ := Mazoit2013.bramble_from_flap_families G F D (w+2) hfamilies hglue hstar
  exact ⟨B,hB,horder⟩
