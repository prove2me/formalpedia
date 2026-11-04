-- Prove2me | solution 1 for ThreeSum.RawReporting.mem_childList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:22:52.556684+00:00
-- url     : https://prove2.me/submissions/3780d0d4-31da-4c32-891d-1992f4d90e71

import Definitions.Def_Submission_ThreeSum_RawIncidences
import Definitions.Def_Submission_ThreeSum_Reporting
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Sort
import Definitions.Def_Submission_ThreeSum_RawReporting

set_option autoImplicit false
open ThreeSum ThreeSum.RawReporting
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences
namespace ThreeSum.RawReporting
theorem _root_.solution {L h : ℕ} {Q S : Finset (Fin L)} :
    S ∈ childList Q h ↔ S ∈ Q.powersetCard h := by
  constructor
  · intro hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    obtain ⟨s, hsLayer, rfl⟩ := Finset.mem_map.mp ((Finset.mem_sort _).mp hc)
    exact hsLayer
  · intro hs
    apply List.mem_map.mpr
    refine ⟨toColex S, ?_, rfl⟩
    apply (Finset.mem_sort _).mpr
    exact Finset.mem_map.mpr ⟨S, hs, rfl⟩
end ThreeSum.RawReporting
