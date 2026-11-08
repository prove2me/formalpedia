-- Prove2me | solution 1 for Tatamibari.NPC.terminator_parity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:34:12.379189+00:00
-- url     : https://prove2.me/submissions/443e7947-5d84-4806-b8fb-9b96b4c674c6

import Definitions.Def_Tatamibari_NPC_ClauseSemantics

set_option autoImplicit false

open Tatamibari.NPC in
theorem solution (down : Bool) :
    terminator.locallySolvable (terminator.profile [down]) := by
  cases down
  · exact ⟨[⟨0, 0, 1, 10⟩, ⟨1, 0, 2, 3⟩, ⟨2, 0, 3, 2⟩, ⟨3, 0, 4, 2⟩, ⟨4, 0, 5, 3⟩, ⟨5, 0, 6, 10⟩, ⟨2, 2, 4, 4⟩, ⟨1, 3, 2, 5⟩, ⟨4, 3, 5, 5⟩, ⟨2, 4, 4, 6⟩, ⟨1, 5, 2, 7⟩, ⟨4, 5, 5, 7⟩, ⟨2, 6, 4, 8⟩, ⟨1, 7, 2, 9⟩, ⟨4, 7, 5, 9⟩, ⟨2, 8, 4, 10⟩], by decide +kernel⟩
  · exact ⟨[⟨0, 0, 1, 10⟩, ⟨1, 0, 2, 4⟩, ⟨2, 0, 3, 3⟩, ⟨3, 0, 4, 3⟩, ⟨4, 0, 5, 4⟩, ⟨5, 0, 6, 10⟩, ⟨2, 3, 4, 5⟩, ⟨1, 4, 2, 6⟩, ⟨4, 4, 5, 6⟩, ⟨2, 5, 4, 7⟩, ⟨1, 6, 2, 8⟩, ⟨4, 6, 5, 8⟩, ⟨2, 7, 4, 9⟩, ⟨1, 8, 2, 10⟩, ⟨4, 8, 5, 10⟩, ⟨2, 9, 4, 11⟩], by decide +kernel⟩
