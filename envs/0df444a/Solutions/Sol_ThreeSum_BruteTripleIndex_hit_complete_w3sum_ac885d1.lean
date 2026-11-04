-- Prove2me | solution 1 for ThreeSum.BruteTripleIndex.hit_complete_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:11:15.25177+00:00
-- url     : https://prove2.me/submissions/9c9a09ae-57ab-4171-9b2c-2a7ee2936d78

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex
import Theorems.Thm_ThreeSum_BruteTripleIndex_code_lt
import Theorems.Thm_ThreeSum_BruteTripleIndex_decode_code

set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex
namespace ThreeSum.BruteTripleIndex
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) (hn : 0 < n) :
    Hit x hn (n^3) ↔ Coloring.DistinctZeroSum x := by
  constructor
  · rintro ⟨i,hi,_,hx⟩
    exact ⟨⟨first n i,(bounds hn hi).1⟩,⟨second n i,(bounds hn hi).2.1⟩,
      ⟨third n i,(bounds hn hi).2.2⟩,hx⟩
  · rintro ⟨i,j,k,hij,hik,hjk,hzero⟩
    refine ⟨code i j k,code_lt i j k,code_lt i j k,?_⟩
    have ha : (⟨first n (code i j k),(bounds hn (code_lt i j k)).1⟩ : Fin n)=i :=
      Fin.ext (decode_code i j k).1
    have hb : (⟨second n (code i j k),(bounds hn (code_lt i j k)).2.1⟩ : Fin n)=j :=
      Fin.ext (decode_code i j k).2.1
    have hc : (⟨third n (code i j k),(bounds hn (code_lt i j k)).2.2⟩ : Fin n)=k :=
      Fin.ext (decode_code i j k).2.2
    simpa only [witness,ha,hb,hc] using And.intro hij (And.intro hik (And.intro hjk hzero))
end ThreeSum.BruteTripleIndex
