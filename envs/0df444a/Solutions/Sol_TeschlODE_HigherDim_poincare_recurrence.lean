-- Prove2me | solution 1 for TeschlODE.HigherDim.poincare_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:09:45.577983+00:00
-- url     : https://prove2.me/submissions/760e4c5e-e549-43a8-a243-b2cb9fe37d31

import Mathlib

open MeasureTheory in
theorem solution {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hbij : Set.BijOn Φ D D)
    (hvol : ∀ A ⊆ D, MeasurableSet A → MeasurableSet (Φ '' A) ∧ volume (Φ '' A) = volume A) :
    ∀ y : EuclideanSpace ℝ (Fin n), ∀ U ∈ nhds y, U ⊆ D →
      ∃ x ∈ U, ∃ k : ℕ, 1 ≤ k ∧ Φ^[k] x ∈ U := by
  intro y U hU hUD
  have hAopen : IsOpen (interior U) := isOpen_interior
  have hyA : y ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hAU : interior U ⊆ U := interior_subset
  have hAD : interior U ⊆ D := hAU.trans hUD
  have hApos : volume (interior U) ≠ 0 := (hAopen.measure_pos volume ⟨y, hyA⟩).ne'
  have hDfin : volume D ≠ ⊤ := hDb.measure_lt_top.ne
  have himg : ∀ k : ℕ, Φ^[k] '' interior U ⊆ D ∧ MeasurableSet (Φ^[k] '' interior U) ∧
      volume (Φ^[k] '' interior U) = volume (interior U) := by
    intro k
    induction k with
    | zero =>
      rw [Function.iterate_zero, Set.image_id]
      exact ⟨hAD, hAopen.measurableSet, rfl⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have he : Φ^[k+1] '' interior U = Φ '' (Φ^[k] '' interior U) := by
        rw [Function.iterate_succ', Set.image_comp]
      rw [he]
      obtain ⟨m, v⟩ := hvol _ h1 h2
      exact ⟨(Set.image_mono h1).trans hbij.mapsTo.image_subset, m, v.trans h3⟩
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hApos hDfin
  have H : (volume.restrict D) Set.univ <
      ∑ i ∈ Finset.range N, (volume.restrict D) (Φ^[i] '' interior U) := by
    rw [Measure.restrict_apply_univ]
    have hc : ∀ i ∈ Finset.range N, (volume.restrict D) (Φ^[i] '' interior U) =
        volume (interior U) := by
      intro i _
      rw [Measure.restrict_apply (himg i).2.1, Set.inter_eq_left.mpr (himg i).1, (himg i).2.2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact hN
  obtain ⟨i, _, j, _, hij, z, hzi, hzj⟩ :=
    exists_nonempty_inter_of_measure_univ_lt_sum_measure _
      (fun i _ => (himg i).2.1.nullMeasurableSet) H
  obtain ⟨a, ha, rfl⟩ := hzi
  obtain ⟨b, hb, hab⟩ := hzj
  have hinj : ∀ m : ℕ, Set.InjOn Φ^[m] D := hbij.injOn.iterate hbij.mapsTo
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨b, hAU hb, j - i, by omega, ?_⟩
    have hba : Φ^[j - i] b = a := by
      apply hinj i ((hbij.mapsTo.iterate (j - i)) (hAD hb)) (hAD ha)
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
      exact hab
    rw [hba]
    exact hAU ha
  · refine ⟨a, hAU ha, i - j, by omega, ?_⟩
    have hab' : Φ^[i - j] a = b := by
      apply hinj j ((hbij.mapsTo.iterate (i - j)) (hAD ha)) (hAD hb)
      rw [← Function.iterate_add_apply, Nat.add_sub_cancel' h.le]
      exact hab.symm
    rw [hab']
    exact hAU hb
