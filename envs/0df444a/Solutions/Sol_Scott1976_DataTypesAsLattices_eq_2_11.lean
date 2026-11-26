-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.eq_2_11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:25.571377+00:00
-- url     : https://prove2.me/submissions/bcd3dd65-5678-490f-ada1-7cf82c707c13

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (f g x : Pomega) :
    funOf (f ∩ g) x ⊆ funOf f x ∩ funOf g x := by
  intro m ⟨n, hn, hp, hq⟩
  exact ⟨⟨n, hn, hp⟩, ⟨n, hn, hq⟩⟩
end Scott1976.DataTypesAsLattices
