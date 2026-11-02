-- Prove2me | solution 1 for OffGridStorage.TechChoice.tracking_le_full
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:21:13.984835+00:00
-- url     : https://prove2.me/submissions/b908248f-a4ae-4f6b-a505-654c697e36f2

import Mathlib
import Definitions.Def_OffGridStorage_TechChoice_Model

open MeasureTheory OffGridStorage.TechChoice

namespace OffGridLeFullAux

lemma one_step (p : Params) (hp : Standing p) (K x q : ℝ) (hK : 0 ≤ K) (hx : 0 ≤ x) :
    periodRevenueTR p K x q + nextCharge p K x q ≤
      x + (min q p.DH + min (p.e * pos (q - p.DH)) K) := by
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp
  unfold periodRevenueTR nextCharge afterDay pos
  rcases le_total q p.DH with h | h
  · rw [max_eq_left (by linarith : q - p.DH ≤ 0), max_eq_right (by linarith : 0 ≤ p.DH - q),
      mul_zero, add_zero, min_eq_left hK, min_eq_left h]
    -- a = (x - (DH - q))^+
    set a := max 0 (x - (p.DH - q))
    have ha0 : 0 ≤ a := le_max_left _ _
    have hpos : max 0 (min a K - p.DL) = min a K - min (min a K) p.DL := by
      rcases le_total (min a K) p.DL with h1 | h1
      · rw [min_eq_left h1, max_eq_left (by linarith)]; ring
      · rw [min_eq_right h1, max_eq_right (by linarith)]
    rw [hpos, min_assoc]
    have hmK : min a K ≤ a := min_le_left _ _
    have hd : min (x + q) p.DH + a ≤ x + q := by
      rcases le_total (x + q) p.DH with h1 | h1
      · rw [min_eq_left h1, show a = 0 from max_eq_left (by linarith)]; linarith
      · rw [min_eq_right h1, show a = x - (p.DH - q) from max_eq_right (by linarith)]; linarith
    linarith
  · rw [max_eq_right (by linarith : 0 ≤ q - p.DH), max_eq_left (by linarith : p.DH - q ≤ 0),
      sub_zero, min_eq_right h, min_eq_right (by linarith : p.DH ≤ x + q)]
    have hc : 0 ≤ p.e * (q - p.DH) := mul_nonneg he0.le (by linarith)
    rw [max_eq_right (by linarith : 0 ≤ x + p.e * (q - p.DH))]
    set m := min (x + p.e * (q - p.DH)) K
    have hpos : max 0 (m - p.DL) = m - min m p.DL := by
      rcases le_total m p.DL with h1 | h1
      · rw [min_eq_left h1, max_eq_left (by linarith)]; ring
      · rw [min_eq_right h1, max_eq_right (by linarith)]
    rw [hpos, ← min_assoc]
    have : m ≤ x + min (p.e * (q - p.DH)) K := by
      rcases le_total (p.e * (q - p.DH)) K with h1 | h1
      · rw [min_eq_left h1]; exact min_le_left _ _
      · rw [min_eq_right h1]; exact le_trans (min_le_right _ _) (by linarith)
    linarith

lemma path_le (p : Params) (hp : Standing p) (K : ℝ) (hK : 0 ≤ K) (q : Fin p.T → ℝ) :
    revenueTR p K q ≤ ∑ t : Fin p.T, (min (q t) p.DH + min (p.e * pos (q t - p.DH)) K) := by
  set qq : ℕ → ℝ := fun n => if h : n < p.T then q ⟨n, h⟩ else 0 with hqq
  set F : ℝ → ℝ := fun s => min s p.DH + min (p.e * pos (s - p.DH)) K
  have key : ∀ N : ℕ, ∑ n ∈ Finset.range N, periodRevenueTR p K (charge p K q n) (qq n) +
      charge p K q N ≤ ∑ n ∈ Finset.range N, F (qq n) := by
    intro N
    induction N with
    | zero => simp [charge]
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 := one_step p hp K (charge p K q N) (qq N) hK (by
        cases N with
        | zero => exact le_refl _
        | succ n => exact le_max_left _ _)
      have h2 : charge p K q (N + 1) = nextCharge p K (charge p K q N) (qq N) := rfl
      rw [h2]
      linarith
  have hc0 : 0 ≤ charge p K q p.T := by
    cases hT : p.T with
    | zero => exact le_refl _
    | succ n => exact le_max_left _ _
  have k := key p.T
  have e1 : revenueTR p K q = ∑ n ∈ Finset.range p.T,
      periodRevenueTR p K (charge p K q n) (qq n) := by
    unfold revenueTR
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    simp [hqq, t.isLt]
  have e2 : ∑ t : Fin p.T, F (q t) = ∑ n ∈ Finset.range p.T, F (qq n) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    simp [hqq, t.isLt]
  show revenueTR p K q ≤ ∑ t : Fin p.T, F (q t)
  rw [e1, e2]
  linarith

end OffGridLeFullAux

open OffGridLeFullAux in
theorem solution (p : Params) (hp : Standing p) (Q K : ℝ) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    profitTR p Q K ≤ profitF p Q K := by
  have hp' := hp
  obtain ⟨hDH, hDL, he0, he1, hcQ, hcK, hg, hT⟩ := hp'
  set F : ℝ → ℝ := fun x => min x p.DH + min (p.e * pos (x - p.DH)) K with hFdef
  have hFc : Continuous F := by
    show Continuous (fun x => min x p.DH + min (p.e * max 0 (x - p.DH)) K)
    fun_prop
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩
  have hcube : IsCompact (unitCube p.T) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hint : ∀ t : Fin p.T, ∫ u in unitCube p.T, F (Q * u t) =
      ∫ v in Set.Icc (0:ℝ) 1, F (Q * v) := by
    intro t
    unfold unitCube
    rw [volume_pi, Measure.restrict_pi_pi]
    have hcF : Continuous (fun v : ℝ => F (Q * v)) := hFc.comp (continuous_const.mul continuous_id)
    exact integral_comp_eval (X := fun _ : Fin p.T => ℝ)
      (μ := fun _ : Fin p.T => volume.restrict (Set.Icc (0:ℝ) 1)) (i := t)
      (f := fun v : ℝ => F (Q * v)) hcF.aestronglyMeasurable
  have hsum : ∫ u in unitCube p.T, ∑ t : Fin p.T, F (Q * u t) =
      (p.T : ℝ) * ∫ v in Set.Icc (0:ℝ) 1, F (Q * v) := by
    rw [integral_finset_sum]
    · simp_rw [hint]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · intro t _
      exact ((hFc.comp (continuous_const.mul (continuous_apply t))).continuousOn).integrableOn_compact
        hcube
  -- integrability of the tracking revenue
  have hqn : ∀ n : ℕ, Continuous (fun q : Fin p.T → ℝ => if h : n < p.T then q ⟨n, h⟩ else 0) := by
    intro n
    by_cases h : n < p.T
    · simp only [h, dif_pos]; exact continuous_apply _
    · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const
  have hch : ∀ n : ℕ, Continuous (fun q : Fin p.T → ℝ => charge p K q n) := by
    intro n
    induction n with
    | zero => exact continuous_const
    | succ n ih =>
      have hq := hqn n
      show Continuous (fun q : Fin p.T → ℝ => max 0 (min (max 0 (charge p K q n +
        p.e * max 0 ((if h : n < p.T then q ⟨n, h⟩ else 0) - p.DH) -
        max 0 (p.DH - (if h : n < p.T then q ⟨n, h⟩ else 0)))) K - p.DL))
      fun_prop
  have hrevc : Continuous (fun u : Fin p.T → ℝ => revenueTR p K (fun t => Q * u t)) := by
    unfold revenueTR periodRevenueTR afterDay pos
    have hc : ∀ t : Fin p.T, Continuous
        (fun u : Fin p.T → ℝ => charge p K (fun t => Q * u t) t.val) := by
      intro t
      exact (hch t.val).comp (by fun_prop)
    fun_prop
  have hle : ∫ u in unitCube p.T, revenueTR p K (fun t => Q * u t) ≤
      ∫ u in unitCube p.T, ∑ t : Fin p.T, F (Q * u t) := by
    apply setIntegral_mono_on (hrevc.continuousOn.integrableOn_compact hcube)
    · exact (continuous_finset_sum _ (fun t _ =>
        hFc.comp (continuous_const.mul (continuous_apply t)))).continuousOn.integrableOn_compact hcube
    · exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    · intro u _
      exact path_le p hp K hK (fun t => Q * u t)
  unfold profitTR profitF
  rw [hsum] at hle
  have hg0 : 0 ≤ p.g := by linarith
  have := mul_le_mul_of_nonneg_left hle hg0
  nlinarith
