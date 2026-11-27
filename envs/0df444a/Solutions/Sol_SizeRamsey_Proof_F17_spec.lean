-- Prove2me | solution 1 for SizeRamsey.Proof.F17_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:31:36.064112+00:00
-- url     : https://prove2.me/submissions/8bbd50ef-62d1-4aa1-8b52-6d68651b636d

module
public import Definitions.Def_SizeRamsey_AInterface
public import Definitions.Def_SizeRamsey_Upper
public import Theorems.Thm_SizeRamsey_F17_connected
public import Theorems.Thm_SizeRamsey_F17_arrows_matching4_c4
public import Theorems.Thm_SizeRamsey_F17_edgeCount


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
open SizeRamsey.Proof
namespace SizeRamsey.Proof
theorem _root_.solution :
    F17.Connected ∧ edgeCount F17 = 17 ∧
      ArrowsMatching4C4 F17 :=
  ⟨F17_connected, F17_edgeCount, F17_arrows_matching4_c4⟩
end SizeRamsey.Proof
