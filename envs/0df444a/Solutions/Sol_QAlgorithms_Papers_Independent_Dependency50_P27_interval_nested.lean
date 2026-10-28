-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.interval_nested
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:19:39.499565+00:00
-- url     : https://prove2.me/submissions/8c9e19f8-6c3f-4f89-943f-bcc6bfc207cf

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27
open Polynomial


theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (a b c d x : R)
    (hc : c ∈ Set.Icc a b) (hd : d ∈ Set.Icc a b) (hx : x ∈ Set.Icc c d) :
    x ∈ Set.Icc a b := by
  exact ⟨hc.1.trans hx.1, hx.2.trans hd.2⟩

end
