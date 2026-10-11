-- Prove2me | solution 1 for SecondLawThermo.kelvin_of_clausius
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T08:35:01.510779+00:00
-- url     : https://prove2.me/submissions/1e6bb056-781d-4653-89ff-3fdc85c341bf

import Definitions.Def_SecondLawThermo_Defs
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open SecondLawThermo

private theorem work_two_reservoirs {Θ : Type*} [LinearOrder Θ]
    (c : SecondLawThermo.Cycle Θ) (h k : Θ) (hkh : k < h)
    (hbetween : OperatesBetween c h k) :
    work c = c h + c k := by
  classical
  have hne : h ≠ k := ne_of_gt hkh
  have hc : c = Finsupp.single h (c h) + Finsupp.single k (c k) := by
    ext t
    by_cases hth : t = h
    · subst t
      simp [hne]
    · by_cases htk : t = k
      · subst t
        simp [hne]
      · simp [hth, htk, hbetween t hth htk]
  rw [hc]
  simp [work, Finsupp.sum_single_add_single, ne_of_gt hkh]

private theorem work_single_reservoir {Θ : Type*} [LinearOrder Θ]
    (c : SecondLawThermo.Cycle Θ) (t : Θ)
    (hsingle : ∀ s, s ≠ t → c s = 0) :
    work c = c t := by
  classical
  unfold work
  rw [Finsupp.sum_eq_single (f := c) (a := t) (g := fun (_ : Θ) (q : ℝ) => q)
    (by
      intro b hb hbt
      exact (hb (hsingle b hbt)).elim)
    (by
      intro ht
      simp)]

theorem solution {Θ : Type*} [LinearOrder Θ] [Nontrivial Θ]
    (𝒞 : Set (SecondLawThermo.Cycle Θ))
    (h𝒞 : IsCycleCone 𝒞) (hCarnot : CarnotEnginesExist 𝒞) (hCl : ClausiusStatement 𝒞) :
    KelvinStatement 𝒞 := by
  classical
  unfold KelvinStatement
  intro t c hc hsingle
  by_contra hn
  have hwpos : 0 < work c := lt_of_not_ge hn
  have hcwork : work c = c t := work_single_reservoir c t hsingle
  have hct : 0 < c t := by rw [← hcwork]; exact hwpos
  obtain ⟨u, hut⟩ := exists_ne t
  by_cases htu : t < u
  · obtain ⟨e, he⟩ := hCarnot u t htu
    rcases he with ⟨hrev, hebetween, hehot, hecold, hework⟩
    rcases hrev with ⟨hemem, hnegmem⟩
    let d : SecondLawThermo.Cycle Θ := (work e) • c + (work c) • (-e)
    have hdmem : d ∈ 𝒞 := by
      apply h𝒞.add_mem
      · exact h𝒞.smul_mem (work e) c hework.le hc
      · exact h𝒞.smul_mem (work c) (-e) hwpos.le hnegmem
    have hdbetween : OperatesBetween d u t := by
      intro s hsu hst
      have hcs : c s = 0 := hsingle s hst
      simp [d, hcs, hebetween s hsu hst]
    have hework2 : work e = e u + e t := work_two_reservoirs e u t htu hebetween
    have hdwork : work d = 0 := by
      rw [work_two_reservoirs d u t htu hdbetween]
      simp [d, hsingle u (ne_of_gt htu)]
      rw [hcwork, hework2]
      ring
    have hdcold := hCl u t htu d hdmem hdbetween hdwork
    have hdval : d t = work e * c t + work c * (-e t) := by simp [d]
    have hdpos : 0 < d t := by
      rw [hdval]
      exact add_pos (mul_pos hework hct) (mul_pos hwpos (neg_pos.mpr hecold))
    linarith
  · have hut' : u < t := lt_of_le_of_ne (le_of_not_gt htu) hut
    obtain ⟨e, he⟩ := hCarnot t u hut'
    rcases he with ⟨hrev, hebetween, hehot, hecold, hework⟩
    rcases hrev with ⟨hemem, hnegmem⟩
    let d : SecondLawThermo.Cycle Θ := (work e) • c + (work c) • (-e)
    have hdmem : d ∈ 𝒞 := by
      apply h𝒞.add_mem
      · exact h𝒞.smul_mem (work e) c hework.le hc
      · exact h𝒞.smul_mem (work c) (-e) hwpos.le hnegmem
    have hdbetween : OperatesBetween d t u := by
      intro s hst hsu
      have hcs : c s = 0 := hsingle s hst
      simp [d, hcs, hebetween s hst hsu]
    have hework2 : work e = e t + e u := work_two_reservoirs e t u hut' hebetween
    have hdwork : work d = 0 := by
      rw [work_two_reservoirs d t u hut' hdbetween]
      simp [d, hsingle u hut]
      rw [hcwork, hework2]
      ring
    have hdcold := hCl t u hut' d hdmem hdbetween hdwork
    have hdval : d u = work e * c u + work c * (-e u) := by simp [d]
    have hcu : c u = 0 := hsingle u hut
    have hdpos : 0 < d u := by
      rw [hdval, hcu]
      simpa using mul_pos hwpos (neg_pos.mpr hecold)
    linarith
