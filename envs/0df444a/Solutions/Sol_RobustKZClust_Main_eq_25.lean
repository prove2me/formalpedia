-- Prove2me | solution 1 for RobustKZClust.Main.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T18:36:58.955329+00:00
-- url     : https://prove2.me/submissions/d78596ed-b6c3-474a-957b-16ba808e83cf

import Mathlib
import Definitions.Def_RobustKZClust_Main_Spline
namespace RobustKZClust.Main
open MeasureTheory

noncomputable def PP (n : ℕ) (t : ℝ) : ℝ :=
  (1 / (n.factorial : ℝ)) * ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - j) 0) ^ n

lemma pospow_deriv (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (max x 0) ^ m / (m : ℝ)) ((max x 0) ^ (m - 1)) x := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have key : HasDerivAt (fun x : ℝ => (max x 0) ^ m) ((m : ℝ) * (max x 0) ^ (m - 1)) x := by
    rcases lt_trichotomy x 0 with h | h | h
    · have : (fun x : ℝ => (max x 0) ^ m) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with y hy
        simp [max_eq_right (le_of_lt (Set.mem_Iio.1 hy)), show m ≠ 0 by omega]
      have h2 := (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq this
      simpa [max_eq_right h.le, show m - 1 ≠ 0 by omega] using h2
    · subst h
      have hm1 : m - 1 ≠ 0 := by omega
      have a : HasDerivWithinAt (fun x : ℝ => (max x 0) ^ m) 0 (Set.Ici 0) 0 := by
        have := ((hasDerivAt_pow m (0:ℝ)).hasDerivWithinAt (s := Set.Ici 0))
        simp [hm1] at this
        refine this.congr (fun y hy => ?_) (by simp [show m ≠ 0 by omega])
        simp [max_eq_left (Set.mem_Ici.1 hy)]
      have b : HasDerivWithinAt (fun x : ℝ => (max x 0) ^ m) 0 (Set.Iic 0) 0 := by
        refine (hasDerivWithinAt_const (0:ℝ) (Set.Iic 0) (0:ℝ)).congr (fun y hy => ?_) (by simp [show m ≠ 0 by omega])
        simp [max_eq_right (Set.mem_Iic.1 hy), show m ≠ 0 by omega]
      have c := a.union b
      rw [Set.Ici_union_Iic, hasDerivWithinAt_univ] at c
      simpa [hm1] using c
    · have : (fun x : ℝ => (max x 0) ^ m) =ᶠ[nhds x] fun y => y ^ m := by
        filter_upwards [Ioi_mem_nhds h] with y hy
        simp [max_eq_left (le_of_lt (Set.mem_Ioi.1 hy))]
      have h2 := (hasDerivAt_pow m x).congr_of_eventuallyEq this
      simpa [max_eq_left h.le] using h2
  have := key.div_const (m : ℝ)
  rw [mul_div_cancel_left₀ _ hm0] at this
  exact this

lemma int_pospow (n : ℕ) (hn : 1 ≤ n) (d : ℝ) :
    ∫ u in (0:ℝ)..1, (max (d - u) 0) ^ n =
      ((max d 0) ^ (n + 1) - (max (d - 1) 0) ^ (n + 1)) / ((n : ℝ) + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => (max x 0) ^ n) d]
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (max x 0) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)) (f' := fun x : ℝ => (max x 0) ^ n)
    (a := d - 1) (b := d) (fun x _ => by simpa using pospow_deriv (n + 1) (by omega) x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [sub_zero, this]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

lemma choose_sum_split (n : ℕ) (a : ℕ → ℝ) :
    ∑ j ∈ Finset.range (n + 2), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * a j =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * a j
      - ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * a (j + 1) := by
  rw [Finset.sum_range_succ']
  have h1 : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1) * ((n + 1).choose (j + 1) : ℝ) * a (j + 1)
      = - ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * a (j + 1)
        + ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1) : ℝ) * a (j + 1) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Nat.choose_succ_succ]; push_cast; ring
  have h2 : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * a j =
      (-1 : ℝ) ^ 0 * (n.choose 0 : ℝ) * a 0 +
      ∑ j ∈ Finset.range n, (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1) : ℝ) * a (j + 1) := by
    rw [Finset.sum_range_succ']
    ring
  have h3 : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1) : ℝ) * a (j + 1) =
      ∑ j ∈ Finset.range n, (-1 : ℝ) ^ (j + 1) * (n.choose (j + 1) : ℝ) * a (j + 1) := by
    rw [Finset.sum_range_succ]; simp
  rw [h1, h3, h2]
  simp
  ring

lemma PP_step (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    ∫ u in (0:ℝ)..1, PP n (t - u) = PP (n + 1) t := by
  unfold PP
  have hc : ∀ j ∈ Finset.range (n + 1), IntervalIntegrable
      (fun u : ℝ => (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - u - j) 0) ^ n) MeasureTheory.volume 0 1 :=
    fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hc]
  have : ∀ j ∈ Finset.range (n + 1),
      ∫ u in (0:ℝ)..1, (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - u - j) 0) ^ n =
      (-1 : ℝ) ^ j * (n.choose j : ℝ) *
        (((max (t - j) 0) ^ (n + 1) - (max (t - (j + 1 : ℕ)) 0) ^ (n + 1)) / ((n : ℝ) + 1)) := by
    intro j _
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h2 : ∫ x in (0:ℝ)..1, (max (t - x - j) 0) ^ n = ∫ x in (0:ℝ)..1, (max ((t - j) - x) 0) ^ n := by
      congr 1; ext x; rw [sub_right_comm]
    rw [h2, int_pospow n hn]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl this]
  have e : ∑ j ∈ Finset.range (n + 1 + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ) * (max (t - j) 0) ^ (n + 1) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - j) 0) ^ (n + 1)
      - ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - (j + 1 : ℕ)) 0) ^ (n + 1) :=
    choose_sum_split n (fun j => (max (t - j) 0) ^ (n + 1))
  have hs : ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) *
      (((max (t - j) 0) ^ (n + 1) - (max (t - (j + 1 : ℕ)) 0) ^ (n + 1)) / ((n : ℝ) + 1)) =
      (∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - j) 0) ^ (n + 1)
      - ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) * (max (t - (j + 1 : ℕ)) 0) ^ (n + 1)) / ((n : ℝ) + 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hs, show n + 1 + 1 = n + 1 + 1 from rfl, e, Nat.factorial_succ]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

def cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 1

noncomputable def gg (n : ℕ) (t : ℝ) : ℝ :=
  (volume ({V : Fin n → ℝ | ∑ i, V i ≤ t} ∩ cube n)).toReal

lemma cube_fin (n : ℕ) : volume (cube n) ≠ ⊤ := by
  unfold cube
  rw [volume_pi_pi]
  exact ENNReal.prod_ne_top (fun _ _ => by simp)

lemma meas_le (n : ℕ) (t : ℝ) : MeasurableSet {V : Fin n → ℝ | ∑ i, V i ≤ t} :=
  measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const

lemma meas_cube (n : ℕ) : MeasurableSet (cube n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma gg_step (n : ℕ) (t : ℝ) :
    gg (n + 1) t = ∫ u in (0:ℝ)..1, gg n (t - u) := by
  set B : Set (ℝ × (Fin n → ℝ)) :=
    (Set.Ico (0:ℝ) 1 ×ˢ cube n) ∩ {p | p.1 + ∑ i, p.2 i ≤ t} with hB
  have hBm : MeasurableSet B :=
    MeasurableSet.inter (MeasurableSet.prod measurableSet_Ico (meas_cube n))
      (measurableSet_le (by fun_prop) measurable_const)
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hpre : {V : Fin (n + 1) → ℝ | ∑ i, V i ≤ t} ∩ cube (n + 1) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹' B := by
    ext V
    simp only [hB, cube, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_prod, Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.succAbove_zero, Fin.sum_univ_succ, Fin.forall_fin_succ]
    tauto
  have h1 : volume ({V : Fin (n + 1) → ℝ | ∑ i, V i ≤ t} ∩ cube (n + 1)) =
      ∫⁻ u, volume (Prod.mk u ⁻¹' B) := by
    rw [hpre, hmp.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_apply hBm]
  have hslice : ∀ u, volume (Prod.mk u ⁻¹' B) ≠ ⊤ := fun u =>
    ne_top_of_le_ne_top (cube_fin n) (measure_mono (fun W hW => hW.1.2))
  unfold gg
  rw [h1, ← integral_toReal (measurable_measure_prodMk_left hBm).aemeasurable
    (Filter.Eventually.of_forall fun u => lt_top_iff_ne_top.2 (hslice u))]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Ico_eq_integral_Ioc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ico (0:ℝ) 1)]
  · refine setIntegral_congr_fun measurableSet_Ico (fun u hu => ?_)
    congr 2
    ext W
    simp [hB, hu, Fin.sum_univ_succ]
    constructor
    · rintro ⟨a, b⟩; exact ⟨by linarith, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, by linarith⟩
  · intro u hu
    have : Prod.mk u ⁻¹' B = ∅ := by
      ext W; simp [hB, hu]
    simp [this]

lemma gg_one (t : ℝ) : gg 1 t = PP 1 t := by
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  have hpre : {V : Fin 1 → ℝ | ∑ i, V i ≤ t} ∩ cube 1 =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' (Set.Ico (0:ℝ) 1 ∩ Set.Iic t) := by
    ext V
    simp [cube, Set.mem_pi]
    tauto
  unfold gg
  rw [hpre]
  erw [hmp.measure_preimage_equiv]
  unfold PP
  simp [Finset.sum_range_succ]
  rcases lt_or_ge t 0 with h0 | h0
  · have : Set.Ico (0:ℝ) 1 ∩ Set.Iic t = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨a, b⟩, c⟩; linarith
    simp [this, max_eq_right h0.le, max_eq_right (by linarith : t - 1 ≤ 0)]
  rcases lt_or_ge t 1 with h1 | h1
  · have : Set.Ico (0:ℝ) 1 ∩ Set.Iic t = Set.Icc 0 t := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Iic, Set.mem_Icc]; constructor
      · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
      · rintro ⟨a, b⟩; exact ⟨⟨a, by linarith⟩, b⟩
    simp [this, max_eq_left h0, max_eq_right (by linarith : t - 1 ≤ 0), h0]
  · have : Set.Ico (0:ℝ) 1 ∩ Set.Iic t = Set.Ico 0 1 := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Iic]; constructor
      · rintro ⟨a, _⟩; exact a
      · intro a; exact ⟨a, by linarith [a.2]⟩
    simp [this, max_eq_left h0, max_eq_left (by linarith : 0 ≤ t - 1)]

lemma gg_eq (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : gg n t = PP n t := by
  induction n, hn using Nat.le_induction generalizing t with
  | base => exact gg_one t
  | succ n hn ih =>
    rw [gg_step, ← PP_step n hn t]
    exact intervalIntegral.integral_congr (fun u _ => ih _)

lemma beta_eq_gg (n : ℕ) (t : ℝ) : beta n t = gg n t - gg n (t - 1) := by
  have hu : unifCube n = volume.restrict (cube n) := rfl
  unfold beta gg
  rw [hu]
  have hfin : ∀ S : Set (Fin n → ℝ), volume (S ∩ cube n) ≠ ⊤ := fun S =>
    ne_top_of_le_ne_top (cube_fin n) (measure_mono Set.inter_subset_right)
  have hm : MeasurableSet {V : Fin n → ℝ | t - 1 < ∑ i, V i ∧ ∑ i, V i ≤ t} :=
    (measurableSet_lt measurable_const (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))).inter (meas_le n t)
  rw [Measure.restrict_apply hm]
  have hsub : {V : Fin n → ℝ | ∑ i, V i ≤ t - 1} ∩ cube n ⊆ {V : Fin n → ℝ | ∑ i, V i ≤ t} ∩ cube n :=
    fun V hV => ⟨by have := hV.1; simp only [Set.mem_setOf_eq] at this ⊢; linarith, hV.2⟩
  have heq : {V : Fin n → ℝ | t - 1 < ∑ i, V i ∧ ∑ i, V i ≤ t} ∩ cube n =
      ({V : Fin n → ℝ | ∑ i, V i ≤ t} ∩ cube n) \ ({V : Fin n → ℝ | ∑ i, V i ≤ t - 1} ∩ cube n) := by
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨⟨b, c⟩, fun h => absurd h.1 (not_le.2 a)⟩
    · rintro ⟨⟨b, c⟩, d⟩; exact ⟨⟨not_le.1 (fun h => d ⟨h, c⟩), b⟩, c⟩
  rw [heq, measure_diff hsub ((meas_le n (t - 1)).inter (meas_cube n)).nullMeasurableSet (hfin _),
    ENNReal.toReal_sub_of_le (measure_mono hsub) (hfin _)]

theorem eq_25' (z : ℕ) (hz : 1 ≤ z) (t : ℝ) :
    beta z t = (1 / (z.factorial : ℝ)) *
      ∑ j ∈ Finset.range (z + 2), (-1 : ℝ) ^ j * ((z + 1).choose j : ℝ) * (max (t - j) 0) ^ z := by
  rw [beta_eq_gg, gg_eq z hz, gg_eq z hz]
  unfold PP
  rw [choose_sum_split z (fun j => (max (t - j) 0) ^ z)]
  rw [← mul_sub]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 3
  push_cast; ring

end RobustKZClust.Main

open RobustKZClust.Main in
theorem solution (z : ℕ) (hz : 1 ≤ z) (t : ℝ) :
    beta z t = (1 / (z.factorial : ℝ)) *
      ∑ j ∈ Finset.range (z + 2), (-1 : ℝ) ^ j * ((z + 1).choose j : ℝ) * (max (t - j) 0) ^ z :=
  eq_25' z hz t
