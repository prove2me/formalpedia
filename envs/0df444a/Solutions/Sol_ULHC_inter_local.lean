-- Prove2me | solution 1 for ULHC.inter_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:51.924908+00:00
-- url     : https://prove2.me/submissions/44ac57e6-d113-42f7-9951-c89946180aa9

import Definitions.Def_ULHC_V2
import Definitions.Def_ULHC_Chain
import Theorems.Thm_ULHC_ACell_ab
import Theorems.Thm_ULHC_ACell_dk


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution : ∀ (mb mt ml mr ab ad ak bd bk dk : Bool),
    triOK ab ad ak bd bk dk = true →
    -- dark sides join corners of one class
    (mb ≤ ab) → (mt ≤ dk) → (ml ≤ ad) → (mr ≤ bk) →
    -- no Type III cell
    ((mb && mt && !ml && !mr) ≤ ad) → ((ml && mr && !mb && !mt) ≤ ab) →
    -- an inter side has a dark neighbouring side
    ((!mb && !ab) ≤ (ml || mr)) → ((!mt && !dk) ≤ (ml || mr)) →
    ((!ml && !ad) ≤ (mb || mt)) → ((!mr && !bk) ≤ (mb || mt)) →
    (bI (!mb && !ab) + bI (!mt && !dk) + bI (!ml && !ad) + bI (!mr && !bk)) % 2 = 0 := by
  decide
end ULHC
