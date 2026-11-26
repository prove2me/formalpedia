-- Prove2me | solution 1 for Poly1305DebianApi.internalOk_donna_init_update_final_oneshot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-26T12:11:30.477583+00:00
-- url     : https://prove2.me/submissions/28cae6d2-132f-4e87-9427-7e0caad957af

import Theorems.Thm_Poly1305DebianApi_internalOk_donna_oneshot
import Theorems.Thm_Poly1305DebianApi_internalOk_donna_init_update_final

open Poly1305DebianApi in
theorem solution :
    (∃ Rep : Poly1305Libsodium.StateRep,
      internalOk "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]"
          (fun _ => initSpec Rep) ∧
        internalOk "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]"
          (fun _ => updateSpec Rep) ∧
        internalOk "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]"
          (fun _ => finalSpec Rep)) ∧
      internalOk "crypto_onetimeauth_poly1305_donna [libsodium_la_poly1305_donna]" oneshotSpec :=
  ⟨internalOk_donna_init_update_final, internalOk_donna_oneshot⟩
