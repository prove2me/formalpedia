-- Prove2me | solution 1 for Poly1305Debian.internalOk_donna_init_update_final_oneshot
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-25T21:26:49.228622+00:00
-- url     : https://prove2.me/submissions/75f4d61a-000b-4a8b-8ab5-2ae1d2b314ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Poly1305Debian_internalOk_donna_oneshot
import Theorems.Thm_Poly1305Debian_internalOk_donna_init_update_final

open Poly1305Debian in
theorem solution :
    (∃ Rep : Poly1305Libsodium.StateRep, donnaInitOk Rep ∧ donnaUpdateOk Rep ∧ donnaFinalOk Rep) ∧
      donnaOneshotOk :=
  ⟨internalOk_donna_init_update_final, internalOk_donna_oneshot⟩
