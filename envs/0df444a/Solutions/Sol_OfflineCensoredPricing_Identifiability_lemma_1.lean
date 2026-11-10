-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-09T19:39:30.450856+00:00
-- url     : https://prove2.me/submissions/e4cbf64b-2fc7-4e58-873e-35b0dbe7cdbb

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

set_option autoImplicit false

namespace DpAc72

open MeasureTheory Set OfflineCensoredPricing.Identifiability

/-- Base demand: atom at 2 with mass 1/2400, atom at 3 with mass 2399/2400. -/
noncomputable def μ0 : Measure ℝ :=
  ENNReal.ofReal (1 / 2400) • Measure.dirac (2 : ℝ) + ENNReal.ofReal (2399 / 2400) • Measure.dirac (3 : ℝ)

lemma μ0_apply (s : Set ℝ) :
    μ0 s = ENNReal.ofReal (1 / 2400) * s.indicator 1 2 +
      ENNReal.ofReal (2399 / 2400) * s.indicator 1 3 := by
  simp only [μ0, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

theorem μ0_prob : IsProbabilityMeasure μ0 := by
  constructor
  rw [μ0_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

attribute [local instance] μ0_prob

lemma μ0_two : μ0 {2} = ENNReal.ofReal (1 / 2400) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

lemma μ0_three : μ0 {3} = ENNReal.ofReal (2399 / 2400) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

lemma μ0_full (s : Set ℝ) (h2 : (2 : ℝ) ∈ s) (h3 : (3 : ℝ) ∈ s) : μ0 s = 1 := by
  rw [μ0_apply, Set.indicator_of_mem h2, Set.indicator_of_mem h3]
  simp only [Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma μ0_Iic2 : μ0 (Iic 2) = ENNReal.ofReal (1 / 2400) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

/-- The instance: prices 1, 2; inventories 3/2, 2; true b = 1; b ∈ [1/100, 1]. -/
noncomputable def I0 : Instance 2 where
  y := 0
  plo := 1
  phi := 2
  blo := 1 / 100
  bhi := 1
  p := ![1, 2]
  yh := ![3 / 2, 2]
  b := 1
  μξ := μ0
  g := 99 / 100

theorem μ0_prob_I0 : IsProbabilityMeasure I0.μξ := μ0_prob

attribute [local instance] μ0_prob_I0

lemma lam_I0 : lam I0 = 4 := by
  unfold lam
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
  · intro i; fin_cases i <;> simp [I0] <;> norm_num
  · intro i; fin_cases i <;> simp [I0] <;> norm_num
  · show μ0 (Iio (1 * 2)) = 0
    rw [μ0_apply]; norm_num [Set.indicator_apply]
  · intro i
    unfold gammaI
    rw [measureReal_def]
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    apply ne_of_gt
    calc (0 : ENNReal) < μ0 {2} := by rw [μ0_two]; norm_num
      _ ≤ μ0 (Iio (I0.yh i + I0.b * I0.p i)) := by
        apply measure_mono
        rw [Set.singleton_subset_iff]
        fin_cases i <;> simp [I0] <;> norm_num
  · refine ⟨by norm_num [I0], Or.inl ⟨2, ![2, 3], by norm_num, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro a b h
      fin_cases a <;> fin_cases b <;> simp_all <;> norm_num
    · intro k; rw [lam_I0]; fin_cases k <;> norm_num
    · intro k
      show 0 < μ0 _
      fin_cases k
      · simp [μ0_two]
      · simp [μ0_three]
    · show μ0 (Iio (lam I0)) = _
      rw [lam_I0, Fin.sum_univ_two]
      show μ0 (Iio 4) = μ0 {(![2, 3] : Fin 2 → ℝ) 0} + μ0 {(![2, 3] : Fin 2 → ℝ) 1}
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [μ0_two, μ0_three, μ0_full _ (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    · intro k hk
      obtain rfl : k = 0 := by omega
      have e1 : (![2, 3] : Fin 2 → ℝ) ⟨0 + 1, hk⟩ = 3 := rfl
      have e0 : (![2, 3] : Fin 2 → ℝ) ⟨0, by omega⟩ = 2 := rfl
      rw [e1, e0]
      show (99 / 100 : ℝ) ≤ _
      rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, measureReal_def,
        measureReal_def]
      show (99 / 100 : ℝ) ≤ ((μ0 (Iic 3)).toReal - (μ0 (Iic 2)).toReal) / (3 - 2)
      rw [μ0_full _ (by norm_num) (by norm_num), μ0_Iic2, ENNReal.toReal_ofReal (by norm_num)]
      norm_num

/-- Sample sizes: 600 at both prices. -/
def Nv0 : Fin 2 → ℕ := fun _ => 600

lemma Nmin_Nv0 : Nmin Nv0 = 600 := by
  unfold Nmin Nv0; exact ciInf_const

/-- The base demands: one observation of the atom 2 (first sample at price 1), every other
observation is the atom 3. -/
noncomputable def ωs : Sample 2 Nv0 := fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 2 else 3

lemma sales_zero (j : Fin (Nv0 0)) :
    sales I0 ωs 0 j = if (j : ℕ) = 0 then 1 else 3 / 2 := by
  unfold sales ωs
  split_ifs with h1 h2 h2 <;> simp_all [I0] <;> norm_num

lemma sales_one (j : Fin (Nv0 1)) : sales I0 ωs 1 j = 1 := by
  unfold sales ωs
  simp [I0]; norm_num

lemma j0_mem (i : Fin 2) : 0 < Nv0 i := by simp [Nv0]

lemma gammaHat_pos (i : Fin 2) : 0 < gammaHat I0.toPublic (sales I0 ωs) i := by
  unfold gammaHat
  apply div_pos _ (by simp [Nv0])
  rw [Nat.cast_pos, Finset.card_pos]
  refine ⟨⟨0, j0_mem i⟩, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  fin_cases i
  · show sales I0 ωs 0 ⟨0, _⟩ < 3 / 2
    rw [sales_zero]; norm_num
  · show sales I0 ωs 1 ⟨0, _⟩ < 2
    rw [sales_one]; norm_num

lemma sales_ge (i : Fin 2) (j : Fin (Nv0 i)) : 1 ≤ sales I0 ωs i j := by
  fin_cases i
  · show 1 ≤ sales I0 ωs 0 j
    rw [sales_zero]; split_ifs <;> norm_num
  · show 1 ≤ sales I0 ωs 1 j
    rw [sales_one]

lemma sales_j0 (i : Fin 2) : sales I0 ωs i ⟨0, j0_mem i⟩ = 1 := by
  fin_cases i
  · show sales I0 ωs 0 ⟨0, _⟩ = 1
    rw [sales_zero]; simp
  · show sales I0 ωs 1 ⟨0, _⟩ = 1
    rw [sales_one]

lemma breakpts_ne (i : Fin 2) : (breakpts (sales I0 ωs) i).length ≠ 0 := by
  unfold breakpts
  rw [Finset.length_sort]
  apply Finset.card_ne_zero.2
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, j0_mem i⟩)⟩

lemma breakpts_head (i : Fin 2) : (breakpts (sales I0 ωs) i).getD 0 0 = 1 := by
  have hlen : 0 < (breakpts (sales I0 ωs) i).length := Nat.pos_of_ne_zero (breakpts_ne i)
  rw [List.getD_eq_getElem _ _ hlen]
  have hne : (Finset.univ.image (sales I0 ωs i)).Nonempty :=
    ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, j0_mem i⟩)⟩
  have key : (breakpts (sales I0 ωs) i)[0] = (Finset.univ.image (sales I0 ωs i)).min' hne :=
    Finset.sorted_zero_eq_min' (h := by rw [Finset.length_sort]; exact Finset.card_pos.2 hne)
  rw [key]
  apply le_antisymm
  · apply Finset.min'_le
    rw [← sales_j0 i]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · apply Finset.le_min'
    intro y hy
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    exact sales_ge i j

lemma quantMod_head {K : ℕ} {Nv : Fin K → ℕ} (S : Sample K Nv) (i : Fin K) (x : ℝ)
    (hne : (breakpts S i).length ≠ 0)
    (hx : x ≤ ecdfS S i ((breakpts S i).getD 0 0)) :
    quantMod S i x = (breakpts S i).getD 0 0 := by
  unfold quantMod
  dsimp only
  rw [if_neg hne, if_pos hx]

lemma gammaHatMin_le : gammaHatMin I0.toPublic (sales I0 ωs) ≤ gammaHat I0.toPublic (sales I0 ωs) 0 :=
  ciInf_le (Set.finite_range _).bddBelow 0

lemma gammaHat_le_one (i : Fin 2) : gammaHat I0.toPublic (sales I0 ωs) i ≤ 1 := by
  unfold gammaHat
  rw [div_le_one (by simp [Nv0])]
  have := Finset.card_le_univ (Finset.univ.filter
    (fun j => sales I0 ωs i j < I0.toPublic.yh i))
  simp only [Fintype.card_fin] at this
  exact_mod_cast this

lemma dHat_eq (i : Fin 2) : dHat I0.toPublic (sales I0 ωs) i = 1 := by
  unfold dHat
  rw [quantMod_head _ _ _ (breakpts_ne i), breakpts_head]
  rw [breakpts_head]
  refine le_trans gammaHatMin_le ?_
  fin_cases i
  · show gammaHat I0.toPublic (sales I0 ωs) 0 ≤ ecdfS (sales I0 ωs) 0 1
    unfold gammaHat ecdfS
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.2
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have h2 := hj.2
    have hy : I0.toPublic.yh 0 = 3 / 2 := rfl
    rw [hy, sales_zero] at h2
    rw [sales_zero]
    split_ifs at h2 ⊢
    · norm_num
    · norm_num at h2
  · show gammaHat I0.toPublic (sales I0 ωs) 0 ≤ ecdfS (sales I0 ωs) 1 1
    have h1 : ecdfS (sales I0 ωs) 1 1 = 1 := by
      unfold ecdfS
      have : Finset.univ.filter (fun j => sales I0 ωs 1 j ≤ 1) = Finset.univ := by
        ext j; simp [sales_one]
      rw [this, Finset.card_univ, Fintype.card_fin]
      simp [Nv0]
    rw [h1]
    exact gammaHat_le_one 0

lemma bHat_eq : bHat I0.toPublic (sales I0 ωs) = 1 / 100 := by
  have hb : bDagger I0.toPublic (sales I0 ωs) = 0 := by
    unfold bDagger
    simp only [dHat_eq, Fin.sum_univ_two]
    norm_num
  unfold bHat
  rw [hb]
  show max (1 / 100 : ℝ) (min 1 0) = 1 / 100
  norm_num

lemma event_mem : (19 / 20 : ℝ) < |bHat I0.toPublic (sales I0 ωs) - I0.b| ∧
    ∀ i, 0 < gammaHat I0.toPublic (sales I0 ωs) i := by
  refine ⟨?_, gammaHat_pos⟩
  rw [bHat_eq]
  show (19 / 20 : ℝ) < |1 / 100 - 1|
  rw [abs_of_neg (by norm_num)]
  norm_num

lemma pi_measure :
    dataLaw I0 Nv0 (Set.univ.pi (fun i => Set.univ.pi (fun j => ({ωs i j} : Set ℝ)))) =
      ENNReal.ofReal ((1 / 2400) * (2399 / 2400) ^ 1199) := by
  unfold dataLaw
  rw [Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fin.prod_univ_two]
  have hI : I0.μξ = μ0 := rfl
  rw [hI]
  have h1 : ∀ j : Fin (Nv0 1), ωs 1 j = 3 := fun j => by simp [ωs]
  simp only [h1, μ0_three, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : (∏ j : Fin (Nv0 0), μ0 {ωs 0 j}) =
      ENNReal.ofReal (1 / 2400) * ENNReal.ofReal (2399 / 2400) ^ 599 := by
    show (∏ j : Fin (599 + 1), μ0 {ωs 0 j}) = _
    rw [Fin.prod_univ_succ]
    have e0 : ωs 0 (0 : Fin (599 + 1)) = 2 := by simp [ωs]
    have es : ∀ j : Fin 599, ωs 0 (Fin.succ j : Fin (599 + 1)) = 3 := fun j => by
      simp [ωs, Fin.val_succ]
    rw [e0, μ0_two]
    simp only [es, μ0_three, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h0]
  show ENNReal.ofReal (1 / 2400) * ENNReal.ofReal (2399 / 2400) ^ 599 *
    ENNReal.ofReal (2399 / 2400) ^ 600 = _
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  rw [mul_assoc, ← pow_add]

lemma real_gap : 4 * Real.exp (-14) < (1 / 2400) * (2399 / 2400 : ℝ) ^ 1199 := by
  have hb : (1 : ℝ) / 2 ≤ (2399 / 2400 : ℝ) ^ 1199 := by
    have e : (1 : ℝ) + (-1 / 2400) = 2399 / 2400 := by norm_num
    calc (1 : ℝ) / 2 ≤ 1 + ((1199 : ℕ) : ℝ) * (-1 / 2400) := by norm_num
      _ ≤ (1 + (-1 / 2400)) ^ 1199 := one_add_mul_le_pow (by norm_num) 1199
      _ = (2399 / 2400 : ℝ) ^ 1199 := by rw [e]
  generalize (2399 / 2400 : ℝ) ^ 1199 = q at hb ⊢
  have he : (2.7 : ℝ) ^ 14 < Real.exp 14 := by
    have h := Real.exp_one_pow 14
    push_cast at h
    rw [← h]
    exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by norm_num)
  have hpos : 0 < Real.exp 14 := Real.exp_pos _
  rw [Real.exp_neg]
  have : 4 * (Real.exp 14)⁻¹ < 1 / 4800 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
    norm_num at he ⊢
    linarith
  linarith

end DpAc72

open MeasureTheory Set in
open OfflineCensoredPricing.Identifiability in
theorem solution : ¬ (∀ {K : ℕ} (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ) {α : ℝ} (hα : 0 < α),
    dataLaw I Nv {ω | α < |bHat I.toPublic (sales I ω) - I.b| ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤
      ENNReal.ofReal (2 * K * Real.exp (-(1 / (9 * (K : ℝ)) *
        (∑ i, (I.p i - (1 / (K : ℝ)) * ∑ j, I.p j) ^ 2) * I.g ^ 2 * (Nmin Nv : ℝ) * α ^ 2)))) := by
  intro h
  have h1 := h DpAc72.I0 DpAc72.standing_I0 DpAc72.Nv0 (α := 19 / 20) (by norm_num)
  refine absurd h1 (not_le.2 ?_)
  refine lt_of_le_of_lt (b := ENNReal.ofReal (4 * Real.exp (-14))) ?_ ?_
  · apply ENNReal.ofReal_le_ofReal
    rw [DpAc72.Nmin_Nv0]
    have hs : (∑ i, (DpAc72.I0.p i - (1 / ((2 : ℕ) : ℝ)) * ∑ j, DpAc72.I0.p j) ^ 2) = 1 / 2 := by
      simp [DpAc72.I0, Fin.sum_univ_two]; norm_num
    rw [hs]
    have hg : DpAc72.I0.g = 99 / 100 := rfl
    rw [hg]
    have hexp : Real.exp (-(1 / (9 * ((2 : ℕ) : ℝ)) * (1 / 2) * (99 / 100) ^ 2 * ((600 : ℕ) : ℝ) *
        (19 / 20) ^ 2)) ≤ Real.exp (-14) := by
      apply Real.exp_le_exp.2
      norm_num
    have : (2 : ℝ) * ((2 : ℕ) : ℝ) = 4 := by norm_num
    rw [this]
    linarith
  · refine lt_of_lt_of_le ?_ (measure_mono (s := Set.univ.pi
        (fun i => Set.univ.pi (fun j => ({DpAc72.ωs i j} : Set ℝ)))) ?_)
    · rw [DpAc72.pi_measure]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 DpAc72.real_gap
    · intro ω hω
      have hω' : ω = DpAc72.ωs := by
        funext i j
        have := hω i (Set.mem_univ _) j (Set.mem_univ _)
        simpa using this
      subst hω'
      exact DpAc72.event_mem
