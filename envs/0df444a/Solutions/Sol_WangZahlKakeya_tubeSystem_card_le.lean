-- Prove2me | solution 1 for WangZahlKakeya.tubeSystem_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:40:14.390009+00:00
-- url     : https://prove2.me/submissions/a7bc194a-ec44-4b65-8d11-57ad0bfb7719

import Mathlib
import Definitions.Def_WangZahlKakeya_wolff

set_option autoImplicit false

namespace WangZahlKakeyaD9085

open MeasureTheory Metric Set WangZahlKakeya

theorem mem_tube_iff {p v x : E3} {δ : ℝ} :
    x ∈ tube p v δ ↔ ∃ t ∈ Icc (0 : ℝ) 1, ‖x - (p + t • v)‖ ≤ δ := by
  unfold tube
  simp only [mem_iUnion, mem_closedBall, dist_eq_norm, exists_prop]

theorem homothety_sub {p v p' v' q q' : E3} {s s' δ : ℝ}
    (hp : p = q + s • v) (hp' : p' = q' + s' • v') (hs : |s| ≤ 2) (hss : |s' - s| ≤ 1/5)
    (hclose : ‖q - q'‖ + 3 * ‖v - v'‖ ≤ δ / 5) :
    ∃ c : E3, AffineMap.homothety c (4/5 : ℝ) '' tube p v δ ⊆
      tube p v δ ∩ tube p' v' δ := by
  set σ := s' - s with hσ
  set t0 : ℝ := if 0 ≤ σ then 1 else 0 with ht0
  refine ⟨p + t0 • v, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_tube_iff] at hx
  obtain ⟨t, ⟨ht0', ht1⟩, hxt⟩ := hx
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) hxt
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  have ht0r : (0 ≤ t0 ∧ t0 ≤ 1) := by
    rw [ht0]; split_ifs <;> norm_num
  set t' : ℝ := (1/5) * t0 + (4/5) * t with ht'
  have key1 : (4/5 : ℝ) • (x - (p + t0 • v)) + (p + t0 • v) - (p + t' • v)
      = (4/5 : ℝ) • (x - (p + t • v)) := by
    rw [ht']; module
  have hn1 : ‖(4/5 : ℝ) • (x - (p + t • v))‖ ≤ (4/5) * δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 4/5)]
    exact mul_le_mul_of_nonneg_left hxt (by norm_num)
  constructor
  · rw [mem_tube_iff]
    refine ⟨t', ⟨by rw [ht']; nlinarith, by rw [ht']; nlinarith⟩, ?_⟩
    rw [key1]; linarith
  · rw [mem_tube_iff]
    refine ⟨t' - σ, ?_, ?_⟩
    · rw [ht']
      have := abs_le.mp hss
      by_cases h0 : 0 ≤ σ
      · have : t0 = 1 := by rw [ht0, if_pos h0]
        rw [this]; constructor <;> linarith
      · have : t0 = 0 := by rw [ht0, if_neg h0]
        rw [this]; constructor <;> linarith
    · have key2 : (4/5 : ℝ) • (x - (p + t0 • v)) + (p + t0 • v) - (p' + (t' - σ) • v')
          = (4/5 : ℝ) • (x - (p + t • v)) + ((q - q') + (s + t') • (v - v')) := by
        rw [hp, hp', hσ]; module
      rw [key2]
      have hst : |s + t'| ≤ 3 := by
        have : 0 ≤ t' ∧ t' ≤ 1 := ⟨by rw [ht']; nlinarith, by rw [ht']; nlinarith⟩
        rw [abs_le] at hs ⊢; constructor <;> linarith
      calc ‖(4/5 : ℝ) • (x - (p + t • v)) + ((q - q') + (s + t') • (v - v'))‖
          ≤ ‖(4/5 : ℝ) • (x - (p + t • v))‖ + (‖q - q'‖ + ‖(s + t') • (v - v')‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ (4/5) * δ + (‖q - q'‖ + 3 * ‖v - v'‖) := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right hst (norm_nonneg _)
        _ ≤ δ := by linarith

theorem vol_inter_ge {p v p' v' q q' : E3} {s s' δ : ℝ}
    (hp : p = q + s • v) (hp' : p' = q' + s' • v') (hs : |s| ≤ 2) (hss : |s' - s| ≤ 1/5)
    (hclose : ‖q - q'‖ + 3 * ‖v - v'‖ ≤ δ / 5) :
    ENNReal.ofReal (64/125) * volume (tube p v δ) ≤ volume (tube p v δ ∩ tube p' v' δ) := by
  obtain ⟨c, hc⟩ := homothety_sub hp hp' hs hss hclose
  have h := measure_mono (μ := (volume : Measure E3)) hc
  rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin] at h
  convert h using 3
  norm_num

theorem norm_le_three (w : E3) (k : Fin 3) :
    ‖w‖ ≤ |w k| + |w (k.succAbove 0)| + |w (k.succAbove 1)| := by
  have h2 := EuclideanSpace.real_norm_sq_eq w
  rw [Fin.sum_univ_succAbove _ k, Fin.sum_univ_two] at h2
  have hn := norm_nonneg w
  have a1 := abs_nonneg (w k)
  have a2 := abs_nonneg (w (k.succAbove 0))
  have a3 := abs_nonneg (w (k.succAbove 1))
  have s1 := sq_abs (w k)
  have s2 := sq_abs (w (k.succAbove 0))
  have s3 := sq_abs (w (k.succAbove 1))
  nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]

theorem coord_le (w : E3) (i : Fin 3) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  rwa [Real.norm_eq_abs] at this

theorem close_of_cell {a b : E3} {h : ℝ} (k : Fin 3) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hak : 1/2 ≤ |a k|) (hbk : 1/2 ≤ |b k|) (hsign : 0 < a k ↔ 0 < b k)
    (h0 : |a (k.succAbove 0) - b (k.succAbove 0)| ≤ h)
    (h1 : |a (k.succAbove 1) - b (k.succAbove 1)| ≤ h) :
    ‖a - b‖ ≤ 6 * h := by
  have hA := EuclideanSpace.real_norm_sq_eq a
  have hB := EuclideanSpace.real_norm_sq_eq b
  rw [Fin.sum_univ_succAbove _ k, Fin.sum_univ_two, ha] at hA
  rw [Fin.sum_univ_succAbove _ k, Fin.sum_univ_two, hb] at hB
  have ca1 := (coord_le a (k.succAbove 0)).trans ha.le
  have ca2 := (coord_le a (k.succAbove 1)).trans ha.le
  have cb1 := (coord_le b (k.succAbove 0)).trans hb.le
  have cb2 := (coord_le b (k.succAbove 1)).trans hb.le
  have hh : 0 ≤ h := le_trans (abs_nonneg _) h0
  have hw := norm_le_three (a - b) k
  simp only [PiLp.sub_apply] at hw
  generalize a k = a0 at *
  generalize b k = b0 at *
  generalize a (k.succAbove 0) = a1 at *
  generalize a (k.succAbove 1) = a2 at *
  generalize b (k.succAbove 0) = b1 at *
  generalize b (k.succAbove 1) = b2 at *
  have hprod : (a0 - b0) * (a0 + b0) = (b1 - a1) * (b1 + a1) + (b2 - a2) * (b2 + a2) := by
    linear_combination (1:ℝ) * hB - (1:ℝ) * hA
  have hS : 1 ≤ |a0 + b0| := by
    by_cases hpos : 0 < a0
    · have hb0 := hsign.1 hpos
      rw [abs_of_pos hpos] at hak; rw [abs_of_pos hb0] at hbk
      rw [abs_of_pos (by linarith)]; linarith
    · have hb0 : ¬ 0 < b0 := fun h' => hpos (hsign.2 h')
      push Not at hpos hb0
      rw [abs_of_nonpos hpos] at hak; rw [abs_of_nonpos hb0] at hbk
      rw [abs_of_nonpos (by linarith)]; linarith
  have e1 : |(b1 - a1) * (b1 + a1)| ≤ h * 2 := by
    rw [abs_mul]
    apply mul_le_mul (by rwa [abs_sub_comm]) _ (abs_nonneg _) hh
    exact (abs_add_le _ _).trans (by linarith)
  have e2 : |(b2 - a2) * (b2 + a2)| ≤ h * 2 := by
    rw [abs_mul]
    apply mul_le_mul (by rwa [abs_sub_comm]) _ (abs_nonneg _) hh
    exact (abs_add_le _ _).trans (by linarith)
  have e3 : |a0 - b0| * |a0 + b0| ≤ 4 * h := by
    rw [← abs_mul, hprod]
    exact (abs_add_le _ _).trans (by linarith)
  have e4 : |a0 - b0| ≤ 4 * h := by nlinarith [abs_nonneg (a0 - b0)]
  linarith

theorem close_of_floor {x y h : ℝ} (hh : 0 < h) (e : ⌊x / h⌋ = ⌊y / h⌋) : |x - y| ≤ h := by
  have := Int.abs_sub_lt_one_of_floor_eq_floor e
  rw [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at this
  exact this.le

theorem floor_mem_Icc {x R h : ℝ} (hh : 0 < h) (hx : |x| ≤ R) :
    ⌊x / h⌋ ∈ Finset.Icc (-⌈R / h⌉) ⌈R / h⌉ := by
  rw [Finset.mem_Icc]
  rw [abs_le] at hx
  constructor
  · rw [Int.le_floor]
    push_cast
    have : -(R / h) ≤ x / h := by
      rw [← neg_div]; gcongr; linarith
    linarith [Int.le_ceil (R / h)]
  · have : x / h ≤ R / h := by gcongr; linarith
    exact (Int.floor_le_ceil _).trans (Int.ceil_mono this)

theorem card_Icc_le {y : ℝ} (hy : 0 ≤ y) :
    ((Finset.Icc (-⌈y⌉) ⌈y⌉).card : ℝ) ≤ 2 * y + 3 := by
  have h1 : (0:ℤ) ≤ ⌈y⌉ := Int.ceil_nonneg hy
  have h2 : ((Finset.Icc (-⌈y⌉) ⌈y⌉).card : ℤ) = 2 * ⌈y⌉ + 1 := by
    simp only [Int.card_Icc]; omega
  have h3 : ((Finset.Icc (-⌈y⌉) ⌈y⌉).card : ℝ) = 2 * ((⌈y⌉ : ℤ) : ℝ) + 1 := by
    exact_mod_cast h2
  have h4 : ((⌈y⌉ : ℤ) : ℝ) < y + 1 := Int.ceil_lt_add_one y
  linarith

theorem ennreal_contra {a b I : ENNReal} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hb0 : b ≠ 0)
    (hbt : b ≠ ⊤) (hA : ENNReal.ofReal (64/125) * a ≤ I) (hB : ENNReal.ofReal (64/125) * b ≤ I)
    (hD : I ≤ (a ⊔ b) / 2) : False := by
  have key : ∀ c : ENNReal, c ≠ 0 → c ≠ ⊤ → ENNReal.ofReal (64/125) * c ≤ c / 2 → False := by
    intro c hc0 hct h
    have h' := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct)
      (ENNReal.div_ne_top hct (by norm_num))).2 h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_div] at h'
    have hp := ENNReal.toReal_pos hc0 hct
    norm_num at h'
    linarith
  rcases le_total a b with hab | hab
  · rw [sup_eq_right.2 hab] at hD
    exact key b hb0 hbt (hB.trans hD)
  · rw [sup_eq_left.2 hab] at hD
    exact key a ha0 hat (hA.trans hD)

theorem main_bound : ∃ C > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y → (n : ℝ) ≤ C * δ ^ (-(4 : ℝ)) := by
  refine ⟨6 * 41 * 203 ^ 2 * 603 ^ 2, by norm_num, ?_⟩
  intro δ n p v Y hT
  obtain ⟨hδ, hv, hsub, hdist, -, -⟩ := hT
  have hrpow : δ ^ (-(4:ℝ)) = (δ ^ 4)⁻¹ := by
    rw [Real.rpow_neg hδ.le]; norm_cast
  rw [hrpow]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp only [CharP.cast_eq_zero]; positivity
  have hball : ∀ i, closedBall (p i) δ ⊆ tube (p i) (v i) δ := by
    intro i x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    exact mem_tube_iff.2 ⟨0, ⟨le_rfl, zero_le_one⟩, by rwa [zero_smul, add_zero]⟩
  have hp1 : ∀ i, ‖p i‖ ≤ 1 := by
    intro i
    have := hsub i (hball i (mem_closedBall_self hδ.le))
    rwa [mem_closedBall, dist_zero_right] at this
  have hδ1 : δ ≤ 1 := by
    let i : Fin n := ⟨0, hn⟩
    have m1 : p i - δ • v i ∈ tube (p i) (v i) δ := mem_tube_iff.2 ⟨0, ⟨le_rfl, zero_le_one⟩, by
      rw [zero_smul, add_zero, sub_sub_cancel_left, norm_neg, norm_smul, hv i, Real.norm_eq_abs,
        abs_of_pos hδ, mul_one]⟩
    have m2 : p i + v i + δ • v i ∈ tube (p i) (v i) δ := mem_tube_iff.2 ⟨1, ⟨zero_le_one, le_rfl⟩, by
      rw [one_smul, add_sub_cancel_left, norm_smul, hv i, Real.norm_eq_abs, abs_of_pos hδ,
        mul_one]⟩
    have b1 := hsub i m1
    have b2 := hsub i m2
    rw [mem_closedBall, dist_zero_right] at b1 b2
    have e : (p i + v i + δ • v i) - (p i - δ • v i) = (1 + 2 * δ) • v i := by module
    have := norm_sub_le (p i + v i + δ • v i) (p i - δ • v i)
    rw [e, norm_smul, hv i, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith
  have hvol0 : ∀ i, volume (tube (p i) (v i) δ) ≠ 0 :=
    fun i => (lt_of_lt_of_le (measure_closedBall_pos volume (p i) hδ)
      (measure_mono (hball i))).ne'
  have hvolt : ∀ i, volume (tube (p i) (v i) δ) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top (measure_closedBall_lt_top (x := (0 : E3)) (r := 1)).ne
      (measure_mono (hsub i))
  have hdom : ∀ i, ∃ k : Fin 3, 1/2 ≤ |v i k| := by
    intro i
    by_contra hcon
    push Not at hcon
    have h2 := EuclideanSpace.real_norm_sq_eq (v i)
    rw [hv i, Fin.sum_univ_three] at h2
    have c0 := hcon 0
    have c1 := hcon 1
    have c2 := hcon 2
    nlinarith [sq_abs (v i 0), sq_abs (v i 1), sq_abs (v i 2), abs_nonneg (v i 0),
      abs_nonneg (v i 1), abs_nonneg (v i 2)]
  choose kf hkf using hdom
  set hh := δ / 100 with hhdef
  have hhpos : 0 < hh := by positivity
  set s : Fin n → ℝ := fun i => p i (kf i) / v i (kf i) with hsdef
  set q : Fin n → E3 := fun i => p i - s i • v i with hqdef
  have hvk0 : ∀ i, v i (kf i) ≠ 0 := by
    intro i h0; have := hkf i; rw [h0, abs_zero] at this; linarith
  have hs2 : ∀ i, |s i| ≤ 2 := by
    intro i
    simp only [hsdef]
    rw [abs_div, div_le_iff₀ (abs_pos.2 (hvk0 i))]
    have := (coord_le (p i) (kf i)).trans (hp1 i)
    linarith [hkf i]
  have hq3 : ∀ i, ‖q i‖ ≤ 3 := by
    intro i
    simp only [hqdef]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, hv i, Real.norm_eq_abs, mul_one]
    linarith [hp1 i, hs2 i]
  have hqk : ∀ i, q i (kf i) = 0 := by
    intro i
    simp only [hqdef, hsdef, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hvk0 i]
    ring
  have hpq : ∀ i, p i = q i + s i • v i := by
    intro i; simp only [hqdef]; abel
  set N1 := ⌈1 / hh⌉ with hN1
  set N2 := ⌈3 / hh⌉ with hN2
  let key : Fin n → Fin 3 × Bool × (Fin 2 → ℤ) × (Fin 2 → ℤ) × ℤ := fun i =>
    (kf i, decide (0 < v i (kf i)), fun m => ⌊v i ((kf i).succAbove m) / hh⌋,
      fun m => ⌊q i ((kf i).succAbove m) / hh⌋, ⌊10 * s i⌋)
  let S : Finset (Fin 3 × Bool × (Fin 2 → ℤ) × (Fin 2 → ℤ) × ℤ) :=
    Finset.univ ×ˢ Finset.univ ×ˢ Fintype.piFinset (fun _ => Finset.Icc (-N1) N1) ×ˢ
      Fintype.piFinset (fun _ => Finset.Icc (-N2) N2) ×ˢ Finset.Icc (-20) 20
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), key i ∈ S := by
    intro i _
    simp only [S, key, Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun m => floor_mem_Icc hhpos ((coord_le _ _).trans (hv i).le),
      fun m => floor_mem_Icc hhpos ((coord_le _ _).trans (hq3 i)), ?_⟩
    have := abs_le.mp (hs2 i)
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]; push_cast; linarith
    · rw [Int.floor_le_iff]; push_cast; linarith
  have hinj : Set.InjOn key (Finset.univ : Finset (Fin n)) := by
    intro i _ j _ hij
    by_contra hne
    simp only [key, Prod.mk.injEq] at hij
    obtain ⟨hk, hb, hvf, hqf, hsf⟩ := hij
    have hkj := hkf j
    have hqkj := hqk j
    rw [← hk] at hb hvf hqf hkj hqkj
    have hsign : 0 < v i (kf i) ↔ 0 < v j (kf i) := by
      simpa using hb
    have hvc : ‖v i - v j‖ ≤ 6 * hh :=
      close_of_cell (kf i) (hv i) (hv j) (hkf i) hkj hsign
        (close_of_floor hhpos (congrFun hvf 0)) (close_of_floor hhpos (congrFun hvf 1))
    have hqc : ‖q i - q j‖ ≤ 2 * hh := by
      have hw := norm_le_three (q i - q j) (kf i)
      simp only [PiLp.sub_apply] at hw
      rw [hqk i, hqkj, sub_zero, abs_zero] at hw
      have := close_of_floor hhpos (congrFun hqf 0)
      have := close_of_floor hhpos (congrFun hqf 1)
      linarith
    have hsc0 : |10 * s i - 10 * s j| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor hsf
    have hsc : |s j - s i| ≤ 1/5 := by
      rw [abs_lt] at hsc0; rw [abs_le]; constructor <;> linarith
    have hsc' : |s i - s j| ≤ 1/5 := by rwa [abs_sub_comm]
    have hclose : ‖q i - q j‖ + 3 * ‖v i - v j‖ ≤ δ / 5 := by
      rw [hhdef] at hvc hqc; linarith
    have hclose' : ‖q j - q i‖ + 3 * ‖v j - v i‖ ≤ δ / 5 := by
      rw [norm_sub_rev (q j), norm_sub_rev (v j)]; exact hclose
    have A := vol_inter_ge (hpq i) (hpq j) (hs2 i) hsc hclose
    have B := vol_inter_ge (hpq j) (hpq i) (hs2 j) hsc' hclose'
    rw [inter_comm] at B
    exact ennreal_contra (hvol0 i) (hvolt i) (hvol0 j) (hvolt j) A B (hdist i j hne)
  have hcard := Finset.card_le_card_of_injOn key hmaps hinj
  have h41 : (Finset.Icc (-20 : ℤ) 20).card = 41 := by simp
  have hS : (S.card : ℝ) = 6 * ((Finset.Icc (-N1) N1).card : ℝ) ^ 2 *
      ((Finset.Icc (-N2) N2).card : ℝ) ^ 2 * 41 := by
    simp only [S, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Fintype.card_bool, h41]
    push_cast; ring
  have hn' : (n : ℝ) ≤ S.card := by
    have := hcard
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have c1 : ((Finset.Icc (-N1) N1).card : ℝ) ≤ 203 / δ := by
    have := card_Icc_le (y := 1 / hh) (by positivity)
    rw [hhdef] at this
    have e : 2 * (1 / (δ / 100)) + 3 ≤ 203 / δ := by
      have e3 : 3 ≤ 3 / δ := by rw [le_div_iff₀ hδ]; nlinarith
      have e2 : 2 * (1 / (δ / 100)) = 200 / δ := by field_simp; ring
      have e4 : 203 / δ = 200 / δ + 3 / δ := by ring
      linarith
    rw [hN1, hhdef]; linarith
  have c2 : ((Finset.Icc (-N2) N2).card : ℝ) ≤ 603 / δ := by
    have := card_Icc_le (y := 3 / hh) (by positivity)
    rw [hhdef] at this
    have e : 2 * (3 / (δ / 100)) + 3 ≤ 603 / δ := by
      have e3 : 3 ≤ 3 / δ := by rw [le_div_iff₀ hδ]; nlinarith
      have e2 : 2 * (3 / (δ / 100)) = 600 / δ := by field_simp; ring
      have e4 : 603 / δ = 600 / δ + 3 / δ := by ring
      linarith
    rw [hN2, hhdef]; linarith
  have hfin : ∀ A B : ℝ, 0 ≤ A → A ≤ 203 / δ → 0 ≤ B → B ≤ 603 / δ →
      6 * A ^ 2 * B ^ 2 * 41 ≤ 6 * (203 / δ) ^ 2 * (603 / δ) ^ 2 * 41 := by
    intro A B hA hA' hB hB'; gcongr
  calc (n : ℝ) ≤ S.card := hn'
    _ = 6 * ((Finset.Icc (-N1) N1).card : ℝ) ^ 2 *
      ((Finset.Icc (-N2) N2).card : ℝ) ^ 2 * 41 := hS
    _ ≤ 6 * (203 / δ) ^ 2 * (603 / δ) ^ 2 * 41 := hfin _ _ (Nat.cast_nonneg _) c1 (Nat.cast_nonneg _) c2
    _ = 6 * 41 * 203 ^ 2 * 603 ^ 2 * (δ ^ 4)⁻¹ := by field_simp

end WangZahlKakeyaD9085

open WangZahlKakeya in
theorem solution :
    ∃ C > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y → (n : ℝ) ≤ C * δ ^ (-(4 : ℝ)) := by
  exact WangZahlKakeyaD9085.main_bound
