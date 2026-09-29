-- Prove2me | solution 1 for WangZahlKakeya.tubeVol_comparable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T21:13:35.280499+00:00
-- url     : https://prove2.me/submissions/6a68179d-629b-420c-b2cf-63191a11a096

import Mathlib
import Definitions.Def_WangZahlKakeya_wolff

namespace WZTubeVolAux

open MeasureTheory Metric Set WangZahlKakeya

/-- Membership in a closed ball about the origin of `E3`, in coordinates. -/
lemma mem_closedBall_zero_E3 {δ : ℝ} (hδ : 0 ≤ δ) (y : E3) :
    y ∈ closedBall (0 : E3) δ ↔ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≤ δ ^ 2 := by
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_left hδ]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

/-- Membership in a closed ball about the origin of the Euclidean plane, in coordinates. -/
lemma mem_closedBall_zero_E2 {δ : ℝ} (hδ : 0 ≤ δ) (z : Fin 2 → ℝ) :
    WithLp.toLp 2 z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) δ ↔ z 0 ^ 2 + z 1 ^ 2 ≤ δ ^ 2 := by
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_left hδ]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Membership in the reference tube, in coordinates. -/
lemma mem_tube_iff {δ : ℝ} (hδ : 0 ≤ δ) (x : E3) :
    x ∈ tube 0 (EuclideanSpace.single 0 (1 : ℝ)) δ ↔
      ∃ t ∈ Icc (0 : ℝ) 1, (x 0 - t) ^ 2 + x 1 ^ 2 + x 2 ^ 2 ≤ δ ^ 2 := by
  unfold tube
  simp only [mem_iUnion, exists_prop, zero_add]
  refine exists_congr fun t => and_congr Iff.rfl ?_
  rw [mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq, Real.sqrt_le_left hδ]
  simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

/-- The coordinate splitting `E3 → ℝ × ℝ²` is measure preserving. -/
lemma split_mp :
    MeasurePreserving
      (Prod.map id (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
        (WithLp.ofLp : E3 → (Fin 3 → ℝ)))
      (volume : Measure E3) (volume : Measure (ℝ × EuclideanSpace ℝ (Fin 2))) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin 2))
  exact h3.comp (h2.comp h1)

lemma split_apply (x : E3) :
    (Prod.map id (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
        (WithLp.ofLp : E3 → (Fin 3 → ℝ))) x = (x 0, WithLp.toLp 2 (fun j : Fin 2 => x j.succ)) := by
  simp [MeasurableEquiv.piFinSuccAbove_apply]
  rfl

end WZTubeVolAux

open MeasureTheory Metric Set WangZahlKakeya in
theorem solution (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    3 * δ ^ 2 ≤ WangZahlKakeya.tubeVol δ ∧ WangZahlKakeya.tubeVol δ ≤ 8 * δ ^ 2 := by
  have hδ0 : 0 ≤ δ := hδ.le
  set e : E3 := EuclideanSpace.single 0 (1 : ℝ) with he
  set F := (Prod.map id (WithLp.toLp 2) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘
        (WithLp.ofLp : E3 → (Fin 3 → ℝ))) with hF
  -- the solid cylinder `[0,1] × disc(δ)`
  set Cyl : Set E3 := F ⁻¹' (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin 2)) δ) with hCyl
  have mem_Cyl : ∀ x : E3, x ∈ Cyl ↔ (0 ≤ x 0 ∧ x 0 ≤ 1) ∧ x 1 ^ 2 + x 2 ^ 2 ≤ δ ^ 2 := by
    intro x
    rw [hCyl, mem_preimage, hF, WZTubeVolAux.split_apply, mem_prod, mem_Icc, WZTubeVolAux.mem_closedBall_zero_E2 hδ0]
    rfl
  have vol_Cyl : volume Cyl = ENNReal.ofReal (Real.pi * δ ^ 2) := by
    rw [hCyl, WZTubeVolAux.split_mp.measure_preimage
      (measurableSet_Icc.prod measurableSet_closedBall).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      EuclideanSpace.volume_closedBall_fin_two]
    rw [← ENNReal.ofReal_pow hδ0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have vol_ball : volume (closedBall (0 : E3) δ) = ENNReal.ofReal (Real.pi * 4 / 3 * δ ^ 3) := by
    rw [EuclideanSpace.volume_closedBall_fin_three, ← ENNReal.ofReal_pow hδ0,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have tube_eq : WangZahlKakeya.tubeVol δ = (volume (tube 0 e δ)).toReal := rfl
  -- the two end caps
  set Bm : Set E3 := {x : E3 | x 0 < 0} ∩ closedBall (0 : E3) δ with hBm
  set Bp' : Set E3 := {x : E3 | 0 < x 0} ∩ closedBall (0 : E3) δ with hBp'
  set Bp : Set E3 := (fun x => x + (-e)) ⁻¹' Bp' with hBp
  have hBp'meas : MeasurableSet Bp' := by
    refine MeasurableSet.inter ?_ measurableSet_closedBall
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have hdisj : Disjoint Bm Bp' := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have a := hx1.1
    have b := hx2.1
    simp only [mem_ofPred_eq] at a b
    linarith
  have caps : volume Bm + volume Bp ≤ ENNReal.ofReal (Real.pi * 4 / 3 * δ ^ 3) := by
    rw [hBp, measure_preimage_add_right, ← measure_union hdisj hBp'meas, ← vol_ball]
    exact measure_mono (union_subset inter_subset_right inter_subset_right)
  -- tube is covered
  have cover : tube 0 e δ ⊆ Cyl ∪ Bm ∪ Bp := by
    intro x hx
    rw [he, WZTubeVolAux.mem_tube_iff hδ0] at hx
    obtain ⟨t, ⟨ht0, ht1⟩, hxt⟩ := hx
    rcases lt_or_ge (x 0) 0 with h0 | h0
    · left; right
      refine ⟨h0, ?_⟩
      rw [WZTubeVolAux.mem_closedBall_zero_E3 hδ0]
      nlinarith
    rcases lt_or_ge 1 (x 0) with h1 | h1
    · right
      rw [hBp, mem_preimage]
      have c0 : (x + -e) 0 = x 0 - 1 := by simp [he]; ring
      have c1 : (x + -e) 1 = x 1 := by simp [he]
      have c2 : (x + -e) 2 = x 2 := by simp [he]
      refine ⟨?_, ?_⟩
      · show 0 < (x + -e) 0
        rw [c0]; linarith
      · rw [WZTubeVolAux.mem_closedBall_zero_E3 hδ0, c0, c1, c2]
        nlinarith
    · left; left
      rw [mem_Cyl]
      exact ⟨⟨h0, h1⟩, by nlinarith⟩
  have inner : Cyl ⊆ tube 0 e δ := by
    intro x hx
    rw [mem_Cyl] at hx
    rw [he, WZTubeVolAux.mem_tube_iff hδ0]
    exact ⟨x 0, ⟨hx.1.1, hx.1.2⟩, by nlinarith [hx.2]⟩
  have upper : volume (tube 0 e δ) ≤
      ENNReal.ofReal (Real.pi * δ ^ 2 + Real.pi * 4 / 3 * δ ^ 3) := by
    calc volume (tube 0 e δ) ≤ volume (Cyl ∪ Bm ∪ Bp) := measure_mono cover
      _ ≤ volume (Cyl ∪ Bm) + volume Bp := measure_union_le _ _
      _ ≤ volume Cyl + volume Bm + volume Bp := by gcongr; exact measure_union_le _ _
      _ = volume Cyl + (volume Bm + volume Bp) := by rw [add_assoc]
      _ ≤ ENNReal.ofReal (Real.pi * δ ^ 2) + ENNReal.ofReal (Real.pi * 4 / 3 * δ ^ 3) := by
          rw [vol_Cyl]; exact add_le_add_right caps _
      _ = ENNReal.ofReal (Real.pi * δ ^ 2 + Real.pi * 4 / 3 * δ ^ 3) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  have fin : volume (tube 0 e δ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top upper
  have lower : ENNReal.ofReal (Real.pi * δ ^ 2) ≤ volume (tube 0 e δ) := by
    rw [← vol_Cyl]; exact measure_mono inner
  rw [tube_eq]
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hd2 : 0 < δ ^ 2 := by positivity
  have hd3 : δ ^ 3 ≤ δ ^ 2 := by
    have : δ ^ 3 = δ ^ 2 * δ := by ring
    rw [this]; nlinarith
  constructor
  · have := (ENNReal.ofReal_le_iff_le_toReal fin).mp lower
    calc 3 * δ ^ 2 ≤ Real.pi * δ ^ 2 := by nlinarith
      _ ≤ _ := this
  · refine le_trans (ENNReal.toReal_le_of_le_ofReal (by positivity) upper) ?_
    nlinarith [mul_le_mul_of_nonneg_left hd3 Real.pi_pos.le]
