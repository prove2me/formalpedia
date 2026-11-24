-- Prove2me | solution 1 for ULHC.Border.not_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:46.169278+00:00
-- url     : https://prove2.me/submissions/8084b2d3-5135-41b4-8472-ae5bd66c626b

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Border
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {e : Edge} (he : e ∈ F) : ¬ Cut P e := by
  unfold Cut
  have h1 : e.p ∈ P → e.q ∈ P := fun h => hB.2 _ h _ ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have h2 : e.q ∈ P → e.p ∈ P := fun h => hB.2 _ h _ ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
  tauto
end Border
end ULHC
