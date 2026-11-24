-- Prove2me | solution 1 for ULHC.walk_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:17:39.416913+00:00
-- url     : https://prove2.me/submissions/513e8422-39c9-4a04-aeb5-0b9e3b9d4c2c

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution : ∀ (mb mt ml mr pbl pbr ptl ptr q o : Bool) (si : Side),
    (∀ s, mS mb mt ml mr s = true → cutS pbl pbr ptl ptr s = false) →
    (∀ s, cutS pbl pbr ptl ptr s = true →
        (mS mb mt ml mr (latA s) || mS mb mt ml mr (latB s)) = true) →
    ((mb == mt) && (ml == mr) && (mb != ml) = true → ∀ s, cutS pbl pbr ptl ptr s = false) →
    cutS pbl pbr ptl ptr si = true → outS q (mS mb mt ml mr) si = !o →
    (∃ so, so ≠ si ∧ cutS pbl pbr ptl ptr so = true ∧ outS q (mS mb mt ml mr) so = o ∧
        ∀ s', cutS pbl pbr ptl ptr s' = true → outS q (mS mb mt ml mr) s' = !o → s' = si) ∨
    (∃ d, mS mb mt ml mr d = true ∧ mS mb mt ml mr d.opp = false ∧
        mS mb mt ml mr (latA d) = false ∧ mS mb mt ml mr (latB d) = false ∧
        (si = latA d ∨ si = latB d) ∧ cutS pbl pbr ptl ptr d.opp = false ∧
        outS q (mS mb mt ml mr) d.opp = o ∧
        ∀ s, cutS pbl pbr ptl ptr s = true → outS q (mS mb mt ml mr) s = !o) := by
  decide
end ULHC
