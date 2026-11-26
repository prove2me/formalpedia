-- Prove2me | solution 1 for TunnellMap.odd_y_of_bOdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:25.099954+00:00
-- url     : https://prove2.me/submissions/3d7fbe05-1f53-4767-8857-4d818364fea1

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (p : BOddRep n) : Odd p.1.y := by
  rcases Int.even_or_odd p.1.y with hy | hy
  · rcases hy with ⟨ky, hky⟩
    have hform := p.2.1
    change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 = n at hform
    have heven : Even n := by
      refine ⟨p.1.x ^ 2 + 2 * ky ^ 2 + 4 * p.1.z ^ 2, ?_⟩
      calc
        n = 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 := hform.symm
        _ = (p.1.x ^ 2 + 2 * ky ^ 2 + 4 * p.1.z ^ 2) +
            (p.1.x ^ 2 + 2 * ky ^ 2 + 4 * p.1.z ^ 2) := by rw [hky]; ring
    exfalso
    exact (Int.not_even_iff_odd.mpr hn) heven
  · exact hy
end TunnellMap
