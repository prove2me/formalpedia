-- Prove2me | solution 2 for OfflineCensoredPricing.Identifiability.theorem_2
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:44:58.851155+00:00
-- url     : https://prove2.me/submissions/ccffc3f4-30f2-47bc-b1d0-bb05f617206c

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

set_option autoImplicit false

namespace DpThm2

open MeasureTheory Set OfflineCensoredPricing.Identifiability

/-- Sample size at each historical price. -/
def N0 : ℕ := 10 ^ 14

/-- Atom mass at 4: `1 / (2 N₀)`. -/
noncomputable def m : ℝ := 1 / (2 * (N0 : ℝ))

lemma m_pos : 0 < m := by
  unfold m N0; positivity

lemma m_le_half : m ≤ 1 / 2 := by
  unfold m N0; norm_num

lemma one_sub_m_nonneg : 0 ≤ 1 - m := by
  linarith [m_le_half]

lemma one_sub_m_pos : 0 < 1 - m := by
  linarith [m_le_half]

/-- Base demand law: atom at `4` with mass `m`, atom at `5` with mass `1 - m`. -/
noncomputable def μ0 : Measure ℝ :=
  ENNReal.ofReal m • Measure.dirac (4 : ℝ) +
    ENNReal.ofReal (1 - m) • Measure.dirac (5 : ℝ)

lemma μ0_apply (s : Set ℝ) :
    μ0 s = ENNReal.ofReal m * s.indicator 1 4 +
      ENNReal.ofReal (1 - m) * s.indicator 1 5 := by
  simp only [μ0, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

theorem μ0_prob : IsProbabilityMeasure μ0 := by
  constructor
  rw [μ0_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add m_pos.le one_sub_m_nonneg]
  simp

attribute [local instance] μ0_prob

lemma μ0_four : μ0 {4} = ENNReal.ofReal m := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

lemma μ0_five : μ0 {5} = ENNReal.ofReal (1 - m) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

lemma μ0_full (s : Set ℝ) (h4 : (4 : ℝ) ∈ s) (h5 : (5 : ℝ) ∈ s) : μ0 s = 1 := by
  rw [μ0_apply, Set.indicator_of_mem h4, Set.indicator_of_mem h5]
  simp only [Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add m_pos.le one_sub_m_nonneg]
  simp

lemma μ0_Iic4 : μ0 (Iic 4) = ENNReal.ofReal m := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

/-- Counterexample instance: `K = 2`, prices `1, 3` in `[1, 4]`, historical inventories `7/2, 3`,
inventory `y = 6`, true `b = 1` in `[1/2, 1]`, `g = 1/2`. -/
noncomputable def I0 : Instance 2 where
  y := 6
  plo := 1
  phi := 4
  blo := 1 / 2
  bhi := 1
  p := ![1, 3]
  yh := ![7 / 2, 3]
  b := 1
  μξ := μ0
  g := 1 / 2

theorem μ0_prob_I0 : IsProbabilityMeasure I0.μξ := μ0_prob

attribute [local instance] μ0_prob_I0

lemma lam_I0 : lam I0 = 6 := by
  unfold lam
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    fin_cases i <;> simp [I0] <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove 1 ?_
    simp [I0]; norm_num

lemma lamBar_I0 : lamBar I0 = 6 := by
  unfold lamBar
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    fin_cases i <;> simp [I0] <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove 1 ?_
    simp [I0]; norm_num

lemma standing_I0 : I0.Standing := by
  refine ⟨μ0_prob, by norm_num [I0], by norm_num [I0], by norm_num [I0], by norm_num [I0],
    by norm_num [I0], by norm_num [I0], le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [I0]
  · intro i; fin_cases i <;> (simp [I0]; try norm_num)
  · intro i; fin_cases i <;> (simp [I0]; try norm_num)
  · show μ0 (Iio (1 * 4)) = 0
    rw [μ0_apply]; norm_num [Set.indicator_apply]
  · intro i
    unfold gammaI
    rw [measureReal_def]
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    apply ne_of_gt
    calc (0 : ENNReal) < μ0 {4} := by rw [μ0_four]; exact ENNReal.ofReal_pos.2 m_pos
      _ ≤ μ0 (Iio (I0.yh i + I0.b * I0.p i)) := by
        apply measure_mono
        rw [Set.singleton_subset_iff]
        fin_cases i <;> (simp [I0]; norm_num)
  · refine ⟨by norm_num [I0], Or.inl ⟨2, ![4, 5], by norm_num, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro a b h
      fin_cases a <;> fin_cases b <;> (simp_all; try norm_num)
    · intro k; rw [lam_I0]; fin_cases k <;> norm_num
    · intro k
      show 0 < μ0 _
      fin_cases k
      · simp [μ0_four, ENNReal.ofReal_pos.2 m_pos]
      · simp [μ0_five, ENNReal.ofReal_pos.2 one_sub_m_pos]
    · show μ0 (Iio (lam I0)) = _
      rw [lam_I0, Fin.sum_univ_two]
      show μ0 (Iio 6) = μ0 {(![4, 5] : Fin 2 → ℝ) 0} + μ0 {(![4, 5] : Fin 2 → ℝ) 1}
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [μ0_four, μ0_five, μ0_full _ (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add m_pos.le one_sub_m_nonneg]
      simp
    · intro k hk
      obtain rfl : k = 0 := by omega
      have e1 : (![4, 5] : Fin 2 → ℝ) ⟨0 + 1, hk⟩ = 5 := rfl
      have e0 : (![4, 5] : Fin 2 → ℝ) ⟨0, by omega⟩ = 4 := rfl
      rw [e1, e0]
      show (1 / 2 : ℝ) ≤ _
      rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, measureReal_def,
        measureReal_def]
      show (1 / 2 : ℝ) ≤ ((μ0 (Iic 5)).toReal - (μ0 (Iic 4)).toReal) / (5 - 4)
      rw [μ0_full _ (by norm_num) (by norm_num), μ0_Iic4, ENNReal.toReal_ofReal m_pos.le]
      simp only [ENNReal.toReal_one]
      linarith [m_le_half]

/-- Because `μ0` puts full mass on `[4, 5] ⊂ (-∞, 6) = (-∞, λ)`, the ambiguity set is `{μ0}`. -/
lemma Amb_I0 : Amb I0 = {μ0} := by
  ext μ
  simp only [Amb, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hprob, hcdf⟩
    have : IsProbabilityMeasure μ := hprob
    apply Measure.ext_of_Iic μ μ0
    intro a
    by_cases ha : a < 6
    · exact hcdf a (by rw [lam_I0]; exact ha)
    · push Not at ha
      have h5 : μ (Iic 5) = 1 := by
        rw [hcdf 5 (by rw [lam_I0]; norm_num)]
        exact μ0_full _ (by norm_num) (by norm_num)
      have hμa : μ (Iic a) = 1 := by
        apply le_antisymm
        · exact prob_le_one
        · calc (1 : ENNReal) = μ (Iic 5) := h5.symm
            _ ≤ μ (Iic a) := measure_mono (Iic_subset_Iic.2 (by linarith))
      have h0a : μ0 (Iic a) = 1 :=
        μ0_full _ (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 (by linarith))
      rw [hμa, h0a]
  · rintro rfl
    exact ⟨μ0_prob, fun _ _ => rfl⟩

lemma Rmax_I0 : Rmax I0 = RF I0 μ0 := by
  funext q
  unfold Rmax
  rw [Amb_I0, Set.image_singleton, csSup_singleton]

lemma Rmin_I0 : Rmin I0 = RF I0 μ0 := by
  funext q
  unfold Rmin
  rw [Amb_I0, Set.image_singleton, csInf_singleton]

lemma pStar_eq_I0 : pStarMax I0 = pStarMin I0 := by
  unfold pStarMax pStarMin
  rw [Rmax_I0, Rmin_I0]

lemma RF_I0 (q : ℝ) (hq : q ∈ Icc (1 : ℝ) 4) : RF I0 μ0 q = q * (5 - m - q) := by
  unfold RF
  have h1 : Integrable (fun ξ : ℝ => min (ξ - I0.b * q) I0.y)
      (ENNReal.ofReal m • Measure.dirac (4 : ℝ)) :=
    (integrable_dirac (a := (4 : ℝ)) enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have h2 : Integrable (fun ξ : ℝ => min (ξ - I0.b * q) I0.y)
      (ENNReal.ofReal (1 - m) • Measure.dirac (5 : ℝ)) :=
    (integrable_dirac (a := (5 : ℝ)) enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hint : ∫ ξ, min (ξ - I0.b * q) I0.y ∂μ0 = 5 - m - q := by
    rw [μ0, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac]
    simp only [smul_eq_mul, ENNReal.toReal_ofReal m_pos.le,
      ENNReal.toReal_ofReal one_sub_m_nonneg, I0]
    rw [min_eq_left (by linarith [hq.1]), min_eq_left (by linarith [hq.1])]
    ring
  rw [hint]

lemma worstLoss_I0_seven_halves : (1 : ℝ) < worstLoss I0 (7 / 2) := by
  unfold worstLoss
  rw [Amb_I0, Set.image_singleton, csSup_singleton]
  have hbdd : BddAbove (RF I0 μ0 '' Icc I0.plo I0.phi) := by
    refine ⟨25, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ Icc (1 : ℝ) 4 := hq
    rw [RF_I0 q hq']
    nlinarith [hq'.1, hq'.2, m_pos]
  have hmem : RF I0 μ0 (5 / 2) ∈ RF I0 μ0 '' Icc I0.plo I0.phi :=
    ⟨5 / 2, ⟨by norm_num [I0], by norm_num [I0]⟩, rfl⟩
  have hsup : RF I0 μ0 (5 / 2) ≤ sSup (RF I0 μ0 '' Icc I0.plo I0.phi) :=
    le_csSup hbdd hmem
  have h52 : RF I0 μ0 (5 / 2) = (5 / 2) * (5 - m - 5 / 2) :=
    RF_I0 (5 / 2) ⟨by norm_num, by norm_num⟩
  have h72 : RF I0 μ0 (7 / 2) = (7 / 2) * (5 - m - 7 / 2) :=
    RF_I0 (7 / 2) ⟨by norm_num, by norm_num⟩
  linarith [m_pos]

/-- Sample sizes: `N0` at both historical prices. -/
abbrev Nv0 : Fin 2 → ℕ := fun _ => N0

lemma Nmin_Nv0 : Nmin Nv0 = N0 := by
  unfold Nmin Nv0; exact ciInf_const

lemma priceVar_I0 : priceVar I0.toPublic = 1 := by
  unfold priceVar
  simp [I0, Fin.sum_univ_two]; norm_num

lemma C1_I0 : C1 I0 = 5264 := by
  unfold C1
  rw [lamBar_I0]
  show (5 : ℝ) * 4 ^ 2 + (2 * 6 + 3 * 1 * 4 + 2 * 6) ^ 2 / (1 / 2) ^ 2 = 5264
  norm_num

lemma C2_I0 : C2 I0 = 64 := by
  unfold C2
  rw [lamBar_I0]
  show (4 : ℝ) * (6 + 6 + 4 * 1) = 64
  norm_num

lemma Cthm2_I0 : Cthm2 I0 = 63843139584 := by
  unfold Cthm2
  rw [priceVar_I0, C1_I0, C2_I0, lamBar_I0]
  show max (max (576 * (6 + 1 * 4) ^ 2 * 4 ^ 2) (576 * 5264 ^ 2 / (1 * (1 / 2) ^ 2)))
      (max (288 * 64 ^ 2) (288 * 4 ^ 2 * 6 ^ 2)) = 63843139584
  norm_num

lemma hN_I0 : Cthm2 I0 * (1 / (1 : ℝ) ^ 2) * Real.log (8 * ((2 : ℕ) : ℝ) / (1 / 10)) ≤
    (Nmin Nv0 : ℝ) := by
  rw [Cthm2_I0, Nmin_Nv0]
  have hlog : Real.log (8 * ((2 : ℕ) : ℝ) / (1 / 10)) ≤ 159 := by
    have := Real.log_le_sub_one_of_pos (x := (160 : ℝ)) (by norm_num)
    have h160 : 8 * ((2 : ℕ) : ℝ) / (1 / 10) = 160 := by norm_num
    rw [h160]; linarith
  have hN0 : (N0 : ℝ) = 10 ^ 14 := by unfold N0; norm_num
  rw [hN0]
  nlinarith

/-- Event on a single arm: all draws in `{4, 5}`. -/
def S45 : Set (Fin N0 → ℝ) := Set.univ.pi (fun _ => ({4, 5} : Set ℝ))

/-- Event on a single arm: all draws equal to `5`. -/
def S5 : Set (Fin N0 → ℝ) := Set.univ.pi (fun _ => ({5} : Set ℝ))

/-- Event at price `0`: all draws in `{4, 5}`, and at least one draw is `4`. -/
def A0 : Set (Fin N0 → ℝ) := S45 \ S5

/-- Bad product event: at price `0` draws lie in `{4, 5}` with at least one `4`; at price `1` all
draws equal `5`. -/
def badEvent : Set (Sample 2 Nv0) :=
  Set.univ.pi (fun i : Fin 2 => if i = 0 then A0 else S5)

section OnBadEvent

variable {ω : Sample 2 Nv0} (hω : ω ∈ badEvent)

lemma mem_zero_vals (hω : ω ∈ badEvent) (j : Fin N0) : ω 0 j = 4 ∨ ω 0 j = 5 := by
  have h0 : ω 0 ∈ A0 := by
    have := hω 0 (Set.mem_univ _)
    simpa [badEvent] using this
  have := h0.1 j (Set.mem_univ _)
  simpa using this

lemma exists_zero_four (hω : ω ∈ badEvent) : ∃ j : Fin N0, ω 0 j = 4 := by
  have h0 : ω 0 ∈ A0 := by
    have := hω 0 (Set.mem_univ _)
    simpa [badEvent] using this
  by_contra hall
  push Not at hall
  apply h0.2
  intro j _
  rcases mem_zero_vals hω j with h4 | h5
  · exact absurd h4 (hall j)
  · simpa using h5

lemma mem_one_five (hω : ω ∈ badEvent) (j : Fin N0) : ω 1 j = 5 := by
  have h1 : ω 1 ∈ S5 := by
    have := hω 1 (Set.mem_univ _)
    simpa [badEvent] using this
  have := h1 j (Set.mem_univ _)
  simpa using this

lemma sales_zero_eq (hω : ω ∈ badEvent) (j : Fin N0) :
    sales I0 ω 0 j = if ω 0 j = 4 then 3 else 7 / 2 := by
  rcases mem_zero_vals hω j with h | h
  · simp [sales, I0, h]; norm_num
  · simp [sales, I0, h]; norm_num

lemma sales_one_eq (hω : ω ∈ badEvent) (j : Fin N0) : sales I0 ω 1 j = 2 := by
  simp [sales, I0, mem_one_five hω j]; norm_num

lemma N0_pos : 0 < N0 := by unfold N0; positivity

lemma gammaHat_pos_of_mem (hω : ω ∈ badEvent) (i : Fin 2) :
    0 < gammaHat I0.toPublic (sales I0 ω) i := by
  unfold gammaHat
  apply div_pos _ (by exact_mod_cast N0_pos)
  rw [Nat.cast_pos, Finset.card_pos]
  fin_cases i
  · obtain ⟨j0, hj0⟩ := exists_zero_four hω
    refine ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    show sales I0 ω 0 j0 < 7 / 2
    rw [sales_zero_eq hω j0, if_pos hj0]; norm_num
  · refine ⟨⟨0, N0_pos⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    show sales I0 ω 1 ⟨0, N0_pos⟩ < 3
    rw [sales_one_eq hω]; norm_num

lemma gammaHat_le_one_of_mem (i : Fin 2) :
    gammaHat I0.toPublic (sales I0 ω) i ≤ 1 := by
  unfold gammaHat
  rw [div_le_one (by exact_mod_cast N0_pos)]
  have := Finset.card_le_univ (Finset.univ.filter
    (fun j => sales I0 ω i j < I0.toPublic.yh i))
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

lemma gammaHat_one_of_mem (hω : ω ∈ badEvent) :
    gammaHat I0.toPublic (sales I0 ω) 1 = 1 := by
  unfold gammaHat
  have hfilt : Finset.univ.filter (fun j => sales I0 ω 1 j < I0.toPublic.yh 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [sales_one_eq hω]
    show (2 : ℝ) < 3
    norm_num
  rw [hfilt, Finset.card_univ, Fintype.card_fin]
  have hne : (N0 : ℝ) ≠ 0 := by exact_mod_cast N0_pos.ne'
  exact div_self hne

lemma gammaHatMax_of_mem (hω : ω ∈ badEvent) :
    gammaHatMax I0.toPublic (sales I0 ω) = 1 := by
  unfold gammaHatMax
  apply le_antisymm
  · exact ciSup_le gammaHat_le_one_of_mem
  · exact le_ciSup_of_le (Set.finite_range _).bddAbove 1 (le_of_eq (gammaHat_one_of_mem hω).symm)

def hd : Fin 2 → ℝ := ![3, 2]

lemma breakpts_ne_of_mem (i : Fin 2) : (breakpts (sales I0 ω) i).length ≠ 0 := by
  unfold breakpts
  rw [Finset.length_sort]
  apply Finset.card_ne_zero.2
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, N0_pos⟩)⟩

lemma breakpts_head_of_mem (hω : ω ∈ badEvent) (i : Fin 2) :
    (breakpts (sales I0 ω) i).getD 0 0 = hd i := by
  have hlen : 0 < (breakpts (sales I0 ω) i).length := Nat.pos_of_ne_zero (breakpts_ne_of_mem i)
  rw [List.getD_eq_getElem _ _ hlen]
  have hne : (Finset.univ.image (sales I0 ω i)).Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, N0_pos⟩)⟩
  have key : (breakpts (sales I0 ω) i)[0] = (Finset.univ.image (sales I0 ω i)).min' hne :=
    Finset.sorted_zero_eq_min' (h := by rw [Finset.length_sort]; exact Finset.card_pos.2 hne)
  rw [key]
  apply le_antisymm
  · apply Finset.min'_le
    fin_cases i
    · obtain ⟨j0, hj0⟩ := exists_zero_four hω
      show hd 0 ∈ Finset.univ.image (sales I0 ω 0)
      refine Finset.mem_image.2 ⟨j0, Finset.mem_univ j0, ?_⟩
      show sales I0 ω 0 j0 = 3
      rw [sales_zero_eq hω j0, if_pos hj0]
    · show hd 1 ∈ Finset.univ.image (sales I0 ω 1)
      refine Finset.mem_image.2 ⟨⟨0, N0_pos⟩, Finset.mem_univ _, ?_⟩
      show sales I0 ω 1 ⟨0, N0_pos⟩ = 2
      rw [sales_one_eq hω]
  · apply Finset.le_min'
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    fin_cases i
    · show (3 : ℝ) ≤ sales I0 ω 0 j
      rw [sales_zero_eq hω j]; split_ifs <;> norm_num
    · show (2 : ℝ) ≤ sales I0 ω 1 j
      rw [sales_one_eq hω]

lemma quantMod_head {K : ℕ} {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) (x : ℝ)
    (hne : (breakpts S i).length ≠ 0)
    (hx : x ≤ ecdfS S i ((breakpts S i).getD 0 0)) :
    quantMod S i x = (breakpts S i).getD 0 0 := by
  unfold quantMod
  dsimp only
  rw [if_neg hne, if_pos hx]

lemma dHat_of_mem (hω : ω ∈ badEvent) (i : Fin 2) :
    dHat I0.toPublic (sales I0 ω) i = hd i := by
  unfold dHat
  rw [quantMod_head _ _ _ (breakpts_ne_of_mem i), breakpts_head_of_mem hω]
  rw [breakpts_head_of_mem hω]
  have hmin : gammaHatMin I0.toPublic (sales I0 ω) ≤ gammaHat I0.toPublic (sales I0 ω) 0 :=
    ciInf_le (Set.finite_range _).bddBelow 0
  refine le_trans hmin ?_
  fin_cases i
  · show gammaHat I0.toPublic (sales I0 ω) 0 ≤ ecdfS (sales I0 ω) 0 3
    unfold gammaHat ecdfS
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.2
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have h2 := hj.2
    have hy : I0.toPublic.yh 0 = 7 / 2 := rfl
    rw [hy, sales_zero_eq hω j] at h2
    rw [sales_zero_eq hω j]
    split_ifs at h2 ⊢
    · norm_num
    · norm_num at h2
  · show gammaHat I0.toPublic (sales I0 ω) 0 ≤ ecdfS (sales I0 ω) 1 2
    have h1 : ecdfS (sales I0 ω) 1 2 = 1 := by
      unfold ecdfS
      have hfilt : Finset.univ.filter (fun j => sales I0 ω 1 j ≤ 2) = Finset.univ := by
        ext j; simp [sales_one_eq hω]
      rw [hfilt, Finset.card_univ, Fintype.card_fin]
      exact div_self (by exact_mod_cast N0_pos.ne')
    rw [h1]
    exact gammaHat_le_one_of_mem 0

lemma bHat_of_mem (hω : ω ∈ badEvent) : bHat I0.toPublic (sales I0 ω) = 1 / 2 := by
  have hb : bDagger I0.toPublic (sales I0 ω) = 1 / 2 := by
    unfold bDagger
    simp only [dHat_of_mem hω, Fin.sum_univ_two]
    norm_num [hd, I0]
  unfold bHat
  rw [hb]
  show max (1 / 2 : ℝ) (min 1 (1 / 2)) = 1 / 2
  norm_num

lemma iStar_of_mem (hω : ω ∈ badEvent) : iStar I0.toPublic (sales I0 ω) = 1 := by
  have hmem : iStar I0.toPublic (sales I0 ω) ∈ iStarSet I0.toPublic (sales I0 ω) :=
    Finset.min'_mem _ _
  have h0 : (0 : Fin 2) ∉ iStarSet I0.toPublic (sales I0 ω) := by
    simp only [iStarSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_le]
    refine ⟨1, ?_⟩
    rw [bHat_of_mem hω]
    show (7 / 2 : ℝ) + 1 / 2 * 1 < 3 + 1 / 2 * 3
    norm_num
  revert hmem
  generalize iStar I0.toPublic (sales I0 ω) = k
  fin_cases k
  · intro h; exact absurd h h0
  · intro _; rfl

lemma lamHat_of_mem (hω : ω ∈ badEvent) : lamHat I0.toPublic (sales I0 ω) = 9 / 2 := by
  unfold lamHat
  rw [iStar_of_mem hω, bHat_of_mem hω]
  show (3 : ℝ) + 1 / 2 * 3 = 9 / 2
  norm_num

lemma pTildeHat_of_mem (hω : ω ∈ badEvent) : pTildeHat I0.toPublic (sales I0 ω) = -3 := by
  unfold pTildeHat
  rw [lamHat_of_mem hω, bHat_of_mem hω]
  show ((9 / 2 : ℝ) - 6) / (1 / 2) = -3
  norm_num

lemma shiftedMean_of_mem (hω : ω ∈ badEvent) : shiftedMean I0.toPublic (sales I0 ω) = 7 / 2 := by
  unfold shiftedMean
  rw [iStar_of_mem hω, bHat_of_mem hω]
  simp only [sales_one_eq hω]
  show (∑ _j : Fin N0, ((2 : ℝ) + 1 / 2 * 3)) / (N0 : ℝ) = 7 / 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hne : (N0 : ℝ) ≠ 0 := by exact_mod_cast N0_pos.ne'
  field_simp
  norm_num

lemma RHatMax_of_mem (hω : ω ∈ badEvent) {q : ℝ} (hq : q ∈ Icc (1 : ℝ) 4) :
    RHatMax I0.toPublic (sales I0 ω) q = -(1 / 2) * q ^ 2 + (7 / 2) * q := by
  unfold RHatMax
  rw [if_neg (by rw [pTildeHat_of_mem hω]; linarith [hq.1])]
  unfold R1Hat
  rw [gammaHatMax_of_mem hω, bHat_of_mem hω, shiftedMean_of_mem hω, lamHat_of_mem hω]
  show q * (-(1 : ℝ) * (1 / 2) * q + 7 / 2 + (1 - 1) * (6 - 9 / 2)) = _
  ring

lemma RHatMin_of_mem (hω : ω ∈ badEvent) {q : ℝ} (hq : q ∈ Icc (1 : ℝ) 4) :
    RHatMin I0.toPublic (sales I0 ω) q = -(1 / 2) * q ^ 2 + (7 / 2) * q := by
  unfold RHatMin
  rw [if_neg (by rw [pTildeHat_of_mem hω]; linarith [hq.1])]
  unfold R2Hat
  rw [bHat_of_mem hω, shiftedMean_of_mem hω]
  show q * (-(1 / 2 : ℝ) * q + 7 / 2) = _
  ring

lemma argmax_quad {f : ℝ → ℝ}
    (hf : ∀ q ∈ Icc (1 : ℝ) 4, f q = -(1 / 2) * q ^ 2 + (7 / 2) * q) :
    argmaxIcc 1 4 f = 7 / 2 := by
  unfold argmaxIcc
  have hset : {q ∈ Icc (1 : ℝ) 4 | ∀ q' ∈ Icc 1 4, f q' ≤ f q} = {7 / 2} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq, hmax⟩
      have hle := hmax (7 / 2) ⟨by norm_num, by norm_num⟩
      rw [hf q hq, hf (7 / 2) ⟨by norm_num, by norm_num⟩] at hle
      nlinarith
    · rintro rfl
      refine ⟨⟨by norm_num, by norm_num⟩, fun q' hq' => ?_⟩
      rw [hf q' hq', hf (7 / 2) ⟨by norm_num, by norm_num⟩]
      nlinarith [sq_nonneg (q' - 7 / 2)]
  rw [hset, csSup_singleton]

lemma pHatMax_of_mem (hω : ω ∈ badEvent) : pHatMax I0.toPublic (sales I0 ω) = 7 / 2 :=
  argmax_quad (fun _ hq => RHatMax_of_mem hω hq)

lemma pHatMin_of_mem (hω : ω ∈ badEvent) : pHatMin I0.toPublic (sales I0 ω) = 7 / 2 :=
  argmax_quad (fun _ hq => RHatMin_of_mem hω hq)

lemma d2acd_of_mem (hω : ω ∈ badEvent) :
    d2acd I0.toPublic Nv0 (sales I0 ω) = 7 / 2 := by
  unfold d2acd
  have hne : ¬ ∃ i, Nv0 i = 0 := by
    push Not; intro _; exact N0_pos.ne'
  rw [if_neg hne]
  unfold pD2ACD
  have hW : ∀ q ∈ Icc (1 : ℝ) 4,
      max (WHatMax I0.toPublic (sales I0 ω) q) (WHatMin I0.toPublic (sales I0 ω) q) =
        (1 / 2) * (q - 7 / 2) ^ 2 := by
    intro q hq
    unfold WHatMax WHatMin
    rw [pHatMax_of_mem hω, pHatMin_of_mem hω,
      RHatMax_of_mem hω ⟨by norm_num, by norm_num⟩, RHatMax_of_mem hω hq,
      RHatMin_of_mem hω ⟨by norm_num, by norm_num⟩, RHatMin_of_mem hω hq, max_self]
    ring
  have hset : pD2ACDSet I0.toPublic (sales I0 ω) = {7 / 2} := by
    ext q
    simp only [pD2ACDSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hq, hmin⟩
      have hle := hmin (7 / 2) ⟨by norm_num [I0], by norm_num [I0]⟩
      rw [hW q hq, hW (7 / 2) ⟨by norm_num, by norm_num⟩] at hle
      nlinarith
    · rintro rfl
      refine ⟨⟨by norm_num [I0], by norm_num [I0]⟩, fun q' hq' => ?_⟩
      rw [hW (7 / 2) ⟨by norm_num, by norm_num⟩, hW q' hq']
      nlinarith [sq_nonneg (q' - 7 / 2)]
  rw [hset]
  simp

end OnBadEvent

lemma badEvent_subset :
    badEvent ⊆ {ω | (1 : ℝ) < worstLoss I0 (d2acd I0.toPublic Nv0 (sales I0 ω)) ∧
      ∀ i, 0 < gammaHat I0.toPublic (sales I0 ω) i} := by
  intro ω hω
  refine ⟨?_, gammaHat_pos_of_mem hω⟩
  rw [d2acd_of_mem hω]
  exact worstLoss_I0_seven_halves

lemma badEvent_measure :
    dataLaw I0 Nv0 badEvent =
      ENNReal.ofReal ((1 - (1 - m) ^ N0) * (1 - m) ^ N0) := by
  have hS5_meas : MeasurableSet S5 :=
    MeasurableSet.univ_pi (fun _ => measurableSet_singleton 5)
  have hS5_sub : S5 ⊆ S45 := fun v hv j hj => by
    have := hv j hj
    simp only [Set.mem_singleton_iff] at this
    simp [this]
  have hμS45 : Measure.pi (fun _ : Fin N0 => μ0) S45 = 1 := by
    unfold S45
    rw [Measure.pi_pi]
    have h45 : μ0 {4, 5} = 1 := μ0_full _ (by simp) (by simp)
    simp [h45]
  have hμS5 : Measure.pi (fun _ : Fin N0 => μ0) S5 = ENNReal.ofReal ((1 - m) ^ N0) := by
    unfold S5
    rw [Measure.pi_pi]
    simp only [μ0_five, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← ENNReal.ofReal_pow one_sub_m_nonneg]
  have hμA0 : Measure.pi (fun _ : Fin N0 => μ0) A0 = ENNReal.ofReal (1 - (1 - m) ^ N0) := by
    unfold A0
    rw [measure_sdiff hS5_sub hS5_meas.nullMeasurableSet (measure_ne_top _ _), hμS45, hμS5]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (pow_nonneg one_sub_m_nonneg _)]
  unfold dataLaw badEvent
  rw [Measure.pi_pi, Fin.prod_univ_two]
  have hI : I0.μξ = μ0 := rfl
  have h01 : (1 : Fin 2) ≠ 0 := by decide
  simp only [hI, if_true, if_neg h01]
  rw [hμA0, hμS5, ← ENNReal.ofReal_mul]
  have hle1 : (1 - m) ^ N0 ≤ 1 := pow_le_one₀ one_sub_m_nonneg (by linarith [m_pos])
  linarith

lemma prob_lower_bound :
    (1 : ℝ) / 10 < (1 - (1 - m) ^ N0) * (1 - m) ^ N0 := by
  have hNm : (N0 : ℝ) * m = 1 / 2 := by
    unfold m
    have hne : (N0 : ℝ) ≠ 0 := by exact_mod_cast N0_pos.ne'
    field_simp
  have hlow : (1 : ℝ) / 2 ≤ (1 - m) ^ N0 := by
    have h1 := one_add_mul_le_pow (a := -m) (by linarith [m_le_half]) N0
    have h2 : 1 + (N0 : ℝ) * (-m) = 1 / 2 := by linarith
    have h3 : 1 + -m = 1 - m := by ring
    rw [h2, h3] at h1
    exact h1
  have hup_aux : (3 : ℝ) / 2 ≤ (1 + m) ^ N0 := by
    have h1 := one_add_mul_le_pow (a := m) (by linarith [m_pos]) N0
    have h2 : 1 + (N0 : ℝ) * m = 3 / 2 := by linarith
    rw [h2] at h1
    exact h1
  have hprod : (1 - m) ^ N0 * (1 + m) ^ N0 ≤ 1 := by
    rw [← mul_pow]
    have hsq : (1 - m) * (1 + m) = 1 - m ^ 2 := by ring
    rw [hsq]
    apply pow_le_one₀
    · nlinarith [m_pos, m_le_half]
    · nlinarith [m_pos]
  have hup : (1 - m) ^ N0 ≤ 2 / 3 := by
    nlinarith [pow_nonneg one_sub_m_nonneg N0]
  nlinarith

end DpThm2

open MeasureTheory Set in
open OfflineCensoredPricing.Identifiability in
theorem solution : ¬ (∀ {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing)
    (heq : pStarMax I = pStarMin I) {ε δ : ℝ} (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Nv : Fin K → ℕ) (hN : Cthm2 I * (1 / ε ^ 2) * Real.log (8 * K / δ) ≤ (Nmin Nv : ℝ)),
    dataLaw I Nv {ω | ε < worstLoss I (d2acd I.toPublic Nv (sales I ω)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤ ENNReal.ofReal δ) := by
  intro h
  have h1 := h DpThm2.I0 DpThm2.standing_I0 DpThm2.pStar_eq_I0 (ε := 1) (δ := 1 / 10)
    (by norm_num) (by norm_num) (by norm_num) DpThm2.Nv0 DpThm2.hN_I0
  refine absurd h1 (not_le.2 ?_)
  refine lt_of_lt_of_le ?_ (measure_mono DpThm2.badEvent_subset)
  rw [DpThm2.badEvent_measure]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [DpThm2.prob_lower_bound])).2
    DpThm2.prob_lower_bound
