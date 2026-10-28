-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.roots_on_uniq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:20:32.975767+00:00
-- url     : https://prove2.me/submissions/4acd3601-03b1-4324-82a6-3074fae7ce08

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial


theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) (s1 s2 : List R)
    (h1 : s1.Pairwise (· < ·)) (h2 : s2.Pairwise (· < ·))
    (hr1 : rootsOn p a b s1) (hr2 : rootsOn p a b s2) : s1 = s2 := by
  exact h1.eq_of_mem_iff h2 (fun x => (hr1 x).trans (hr2 x).symm)

end
