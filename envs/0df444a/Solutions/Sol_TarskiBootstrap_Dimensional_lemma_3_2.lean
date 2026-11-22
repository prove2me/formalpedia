-- Prove2me | solution 1 for TarskiBootstrap.Dimensional.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T14:31:33.52432+00:00
-- url     : https://prove2.me/submissions/1d6f53a7-dfba-4b42-b173-64176ace213f

import Definitions.Def_TarskiBootstrap_Dimensional_DownwardClosure
open TarskiBootstrap.Dimensional

theorem solution {L : Type*} [PartialOrder L] (A : Set L)
    (hA : IsAntichain (· ≤ ·) A) {x y : L} (hxy : x < y) :
    (x ∈ A → y ∉ downwardClosure A) ∧
    (y ∈ A → x ∈ downwardClosure A \ A) := by
  constructor
  · intro hx
    rintro ⟨a, ha, hya⟩
    have hxa : x < a := hxy.trans_le hya
    exact (hA hx ha hxa.ne) hxa.le
  · intro hy
    refine ⟨⟨y, hy, hxy.le⟩, ?_⟩
    intro hx
    exact (hA hx hy hxy.ne) hxy.le

#print axioms solution
