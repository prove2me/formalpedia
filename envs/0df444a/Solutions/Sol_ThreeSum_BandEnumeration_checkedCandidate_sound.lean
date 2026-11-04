-- Prove2me | solution 1 for ThreeSum.BandEnumeration.checkedCandidate_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:52.941042+00:00
-- url     : https://prove2.me/submissions/581030da-2c19-4566-8475-993801c5863d

import Definitions.Def_Submission_ThreeSum_Bands
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Definitions.Def_Submission_ThreeSum_BandEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.BandEnumeration
open Family
namespace ThreeSum.BandEnumeration
theorem _root_.solution (A B C : Family) (o : Owner A B C)
    {t : Triple A B C} (h : checkedCandidate A B C o = some t) :
    relevant A B C t ∧ owner A B C t = o := by
  unfold checkedCandidate at h
  cases hc : candidate A B C o with
  | none => simp [hc] at h
  | some u =>
      simp only [hc] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · rename_i hu
        have heq := Option.some.inj h
        subst u
        exact hu
      · cases h
end ThreeSum.BandEnumeration
