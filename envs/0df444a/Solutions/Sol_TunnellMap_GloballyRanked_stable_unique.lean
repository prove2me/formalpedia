-- Prove2me | solution 1 for TunnellMap.GloballyRanked.stable_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:37.92136+00:00
-- url     : https://prove2.me/submissions/679252e2-739e-4c90-99e0-7e4edebeae69

import Mathlib
import Definitions.Def_TunnellMap_GloballyRanked

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}
variable [LinearOrder K] [Fintype S] [Fintype T]
namespace TunnellMap.GloballyRanked
theorem _root_.solution (I : GloballyRanked K S T) (M N : S ≃ T)
    (hM : I.Stable M) (hN : I.Stable N) : M = N := by
  classical
  by_contra hne
  have hfun : ∃ s, M s ≠ N s := by
    by_contra hnone
    apply hne
    apply Equiv.ext
    intro s
    by_contra hs
    exact hnone ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := hfun
  let D := matchingSymmDiff M N
  have hD : D.Nonempty := by
    refine ⟨(s₀, M s₀), ?_⟩
    simp [D, matchingSymmDiff, InMatchingSymmDiff, Ne.symm hs₀]
  let R : Finset K := D.image (fun e => I.rank e.1 e.2)
  have hR : R.Nonempty := hD.image _
  let k := R.min' hR
  have hkR : k ∈ R := Finset.min'_mem R hR
  obtain ⟨e, heD, hek⟩ := Finset.mem_image.mp hkR
  have hmin {e' : S × T} (he' : e' ∈ D) :
      I.rank e.1 e.2 ≤ I.rank e'.1 e'.2 := by
    have hr' : I.rank e'.1 e'.2 ∈ R := Finset.mem_image.mpr ⟨e', he', rfl⟩
    rw [hek]
    change R.min' hR ≤ I.rank e'.1 e'.2
    exact Finset.min'_le R (I.rank e'.1 e'.2) hr'
  have heCases : InMatchingSymmDiff M N e := by
    simpa [D, matchingSymmDiff] using (Finset.mem_filter.mp heD).2
  rcases heCases with heM | heN
  · rcases heM with ⟨hMe, hNe⟩
    have hsourceD : (e.1, N e.1) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, hMe, Ne.symm hNe]
    have htarget_ne : M (N.symm e.2) ≠ e.2 := by
      intro h
      have hs : N.symm e.2 = e.1 := M.injective (h.trans hMe.symm)
      have : N e.1 = e.2 := by
        rw [← hs]
        simp
      exact hNe this
    have htargetD : (N.symm e.2, e.2) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, htarget_ne]
    have hle_source := hmin hsourceD
    have hle_target := hmin htargetD
    have hlt_source : I.rank e.1 e.2 < I.rank e.1 (N e.1) := by
      apply lt_of_le_of_ne hle_source
      intro h
      exact hNe (I.source_injective e.1 h).symm
    have hlt_target : I.rank e.1 e.2 < I.rank (N.symm e.2) e.2 := by
      apply lt_of_le_of_ne hle_target
      intro h
      have hs := I.target_injective e.2 h
      exact htarget_ne (by simpa [hs] using hMe)
    exact hN e.1 e.2 ⟨hlt_source, hlt_target⟩
  · rcases heN with ⟨hNe, hMe⟩
    have hsourceD : (e.1, M e.1) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, hNe, Ne.symm hMe]
    have htarget_ne : N (M.symm e.2) ≠ e.2 := by
      intro h
      have hs : M.symm e.2 = e.1 := N.injective (h.trans hNe.symm)
      have : M e.1 = e.2 := by
        rw [← hs]
        simp
      exact hMe this
    have htargetD : (M.symm e.2, e.2) ∈ D := by
      simp [D, matchingSymmDiff, InMatchingSymmDiff, htarget_ne]
    have hle_source := hmin hsourceD
    have hle_target := hmin htargetD
    have hlt_source : I.rank e.1 e.2 < I.rank e.1 (M e.1) := by
      apply lt_of_le_of_ne hle_source
      intro h
      exact hMe (I.source_injective e.1 h).symm
    have hlt_target : I.rank e.1 e.2 < I.rank (M.symm e.2) e.2 := by
      apply lt_of_le_of_ne hle_target
      intro h
      have hs := I.target_injective e.2 h
      exact htarget_ne (by simpa [hs] using hNe)
    exact hM e.1 e.2 ⟨hlt_source, hlt_target⟩
end TunnellMap.GloballyRanked
