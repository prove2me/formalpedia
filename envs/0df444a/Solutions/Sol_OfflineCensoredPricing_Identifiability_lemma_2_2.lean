-- Prove2me | solution 2 for OfflineCensoredPricing.Identifiability.lemma_2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T23:09:09.23593+00:00
-- url     : https://prove2.me/submissions/01eb4fe5-dd64-40bb-9699-4f91341c3ab1

import Mathlib
import Definitions.Def_OfflineCensoredPricing_Identifiability_Model
import Definitions.Def_OfflineCensoredPricing_Identifiability_D2ACD

set_option autoImplicit false

namespace DpA61f

open MeasureTheory Set OfflineCensoredPricing.Identifiability

/-- Base demand: atom at 4 with mass 1/1200000000, atom at 5 with the rest. -/
noncomputable def μ0 : Measure ℝ :=
  ENNReal.ofReal (1 / 1200000000) • Measure.dirac (4 : ℝ) +
    ENNReal.ofReal (1199999999 / 1200000000) • Measure.dirac (5 : ℝ)

lemma μ0_apply (s : Set ℝ) :
    μ0 s = ENNReal.ofReal (1 / 1200000000) * s.indicator 1 4 +
      ENNReal.ofReal (1199999999 / 1200000000) * s.indicator 1 5 := by
  simp only [μ0, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

theorem μ0_prob : IsProbabilityMeasure μ0 := by
  constructor
  rw [μ0_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

attribute [local instance] μ0_prob

lemma μ0_four : μ0 {4} = ENNReal.ofReal (1 / 1200000000) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

lemma μ0_five : μ0 {5} = ENNReal.ofReal (1199999999 / 1200000000) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

lemma μ0_full (s : Set ℝ) (h4 : (4 : ℝ) ∈ s) (h5 : (5 : ℝ) ∈ s) : μ0 s = 1 := by
  rw [μ0_apply, Set.indicator_of_mem h4, Set.indicator_of_mem h5]
  simp only [Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

lemma μ0_Iic4 : μ0 (Iic 4) = ENNReal.ofReal (1 / 1200000000) := by
  rw [μ0_apply]; norm_num [Set.indicator_apply]

/-- The instance: prices 1, 4; inventories 4, 3/2; y = 2; true b = 1; b ∈ [2/3, 1]. -/
noncomputable def I0 : Instance 2 where
  y := 2
  plo := 1
  phi := 4
  blo := 2 / 3
  bhi := 1
  p := ![1, 4]
  yh := ![4, 3 / 2]
  b := 1
  μξ := μ0
  g := 99 / 100

theorem μ0_prob_I0 : IsProbabilityMeasure I0.μξ := μ0_prob

attribute [local instance] μ0_prob_I0

lemma lam_I0 : lam I0 = 11 / 2 := by
  unfold lam
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    fin_cases i <;> simp [I0] <;> norm_num
  · refine le_ciSup_of_le (Set.finite_range _).bddAbove 1 ?_
    simp [I0]; norm_num

lemma lamBar_I0 : lamBar I0 = 11 / 2 := by
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
  · intro i; fin_cases i <;> simp [I0] <;> norm_num
  · intro i; fin_cases i <;> simp [I0] <;> norm_num
  · show μ0 (Iio (1 * 4)) = 0
    rw [μ0_apply]; norm_num [Set.indicator_apply]
  · intro i
    unfold gammaI
    rw [measureReal_def]
    apply ENNReal.toReal_pos _ (measure_ne_top _ _)
    apply ne_of_gt
    calc (0 : ENNReal) < μ0 {4} := by rw [μ0_four]; norm_num
      _ ≤ μ0 (Iio (I0.yh i + I0.b * I0.p i)) := by
        apply measure_mono
        rw [Set.singleton_subset_iff]
        fin_cases i <;> simp [I0] <;> norm_num
  · refine ⟨by norm_num [I0], Or.inl ⟨2, ![4, 5], by norm_num, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro a b h
      fin_cases a <;> fin_cases b <;> simp_all <;> norm_num
    · intro k; rw [lam_I0]; fin_cases k <;> norm_num
    · intro k
      show 0 < μ0 _
      fin_cases k
      · simp [μ0_four]
      · simp [μ0_five]
    · show μ0 (Iio (lam I0)) = _
      rw [lam_I0, Fin.sum_univ_two]
      show μ0 (Iio (11 / 2)) = μ0 {(![4, 5] : Fin 2 → ℝ) 0} + μ0 {(![4, 5] : Fin 2 → ℝ) 1}
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [μ0_four, μ0_five, μ0_full _ (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    · intro k hk
      obtain rfl : k = 0 := by omega
      have e1 : (![4, 5] : Fin 2 → ℝ) ⟨0 + 1, hk⟩ = 5 := rfl
      have e0 : (![4, 5] : Fin 2 → ℝ) ⟨0, by omega⟩ = 4 := rfl
      rw [e1, e0]
      show (99 / 100 : ℝ) ≤ _
      rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real, measureReal_def,
        measureReal_def]
      show (99 / 100 : ℝ) ≤ ((μ0 (Iic 5)).toReal - (μ0 (Iic 4)).toReal) / (5 - 4)
      rw [μ0_full _ (by norm_num) (by norm_num), μ0_Iic4, ENNReal.toReal_ofReal (by norm_num)]
      norm_num

/-- Sample sizes: 300000000 at both prices. -/
def Nv0 : Fin 2 → ℕ := fun _ => 300000000

lemma Nmin_Nv0 : Nmin Nv0 = 300000000 := by
  unfold Nmin Nv0; exact ciInf_const

/-- The base demands: one observation of the atom 4 (first sample at price 1), every other
observation is the atom 5. -/
noncomputable def ωs : Sample 2 Nv0 := fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 4 else 5

lemma sales_zero (j : Fin (Nv0 0)) :
    sales I0 ωs 0 j = if (j : ℕ) = 0 then 3 else 4 := by
  unfold sales ωs
  split_ifs with h1 h2 h2 <;> simp_all [I0] <;> norm_num

lemma sales_one (j : Fin (Nv0 1)) : sales I0 ωs 1 j = 1 := by
  unfold sales ωs
  simp [I0]; norm_num

/-- The smallest sales value at each price. -/
def hd : Fin 2 → ℝ := ![3, 1]

lemma j0_mem (i : Fin 2) : 0 < Nv0 i := by simp [Nv0]

lemma gammaHat_pos (i : Fin 2) : 0 < gammaHat I0.toPublic (sales I0 ωs) i := by
  unfold gammaHat
  apply div_pos _ (by simp [Nv0])
  rw [Nat.cast_pos, Finset.card_pos]
  refine ⟨⟨0, j0_mem i⟩, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  fin_cases i
  · show sales I0 ωs 0 ⟨0, _⟩ < 4
    rw [sales_zero]; norm_num
  · show sales I0 ωs 1 ⟨0, _⟩ < 3 / 2
    rw [sales_one]; norm_num

lemma sales_ge (i : Fin 2) (j : Fin (Nv0 i)) : hd i ≤ sales I0 ωs i j := by
  fin_cases i
  · show (3 : ℝ) ≤ sales I0 ωs 0 j
    rw [sales_zero]; split_ifs <;> norm_num
  · show (1 : ℝ) ≤ sales I0 ωs 1 j
    rw [sales_one]

lemma sales_j0 (i : Fin 2) : sales I0 ωs i ⟨0, j0_mem i⟩ = hd i := by
  fin_cases i
  · show sales I0 ωs 0 ⟨0, _⟩ = 3
    rw [sales_zero]; simp
  · show sales I0 ωs 1 ⟨0, _⟩ = 1
    rw [sales_one]

lemma breakpts_ne (i : Fin 2) : (breakpts (sales I0 ωs) i).length ≠ 0 := by
  unfold breakpts
  rw [Finset.length_sort]
  apply Finset.card_ne_zero.2
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, j0_mem i⟩)⟩

lemma breakpts_head (i : Fin 2) : (breakpts (sales I0 ωs) i).getD 0 0 = hd i := by
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

lemma gammaHat_one : gammaHat I0.toPublic (sales I0 ωs) 1 = 1 := by
  unfold gammaHat
  have : Finset.univ.filter (fun j => sales I0 ωs 1 j < I0.toPublic.yh 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [sales_one]
    show (1 : ℝ) < 3 / 2
    norm_num
  rw [this, Finset.card_univ, Fintype.card_fin]
  simp [Nv0]

lemma gammaHatMax_eq : gammaHatMax I0.toPublic (sales I0 ωs) = 1 := by
  unfold gammaHatMax
  apply le_antisymm
  · exact ciSup_le gammaHat_le_one
  · exact le_ciSup_of_le (Set.finite_range _).bddAbove 1 (le_of_eq gammaHat_one.symm)

lemma dHat_eq (i : Fin 2) : dHat I0.toPublic (sales I0 ωs) i = hd i := by
  unfold dHat
  rw [quantMod_head _ _ _ (breakpts_ne i), breakpts_head]
  rw [breakpts_head]
  refine le_trans gammaHatMin_le ?_
  fin_cases i
  · show gammaHat I0.toPublic (sales I0 ωs) 0 ≤ ecdfS (sales I0 ωs) 0 3
    unfold gammaHat ecdfS
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.2
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_⟩
    have h2 := hj.2
    have hy : I0.toPublic.yh 0 = 4 := rfl
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

lemma bHat_eq : bHat I0.toPublic (sales I0 ωs) = 2 / 3 := by
  have hb : bDagger I0.toPublic (sales I0 ωs) = 2 / 3 := by
    unfold bDagger
    simp only [dHat_eq, Fin.sum_univ_two]
    norm_num [hd, I0]
  unfold bHat
  rw [hb]
  show max (2 / 3 : ℝ) (min 1 (2 / 3)) = 2 / 3
  norm_num

lemma iStar_eq : iStar I0.toPublic (sales I0 ωs) = 0 := by
  have hmem : iStar I0.toPublic (sales I0 ωs) ∈ iStarSet I0.toPublic (sales I0 ωs) :=
    Finset.min'_mem _ _
  have h1 : (1 : Fin 2) ∉ iStarSet I0.toPublic (sales I0 ωs) := by
    simp only [iStarSet, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_le]
    refine ⟨0, ?_⟩
    rw [bHat_eq]
    show (3 / 2 : ℝ) + 2 / 3 * 4 < 4 + 2 / 3 * 1
    norm_num
  revert hmem
  generalize iStar I0.toPublic (sales I0 ωs) = k
  fin_cases k
  · intro _; rfl
  · intro h; exact absurd h h1

lemma lamHat_eq : lamHat I0.toPublic (sales I0 ωs) = 14 / 3 := by
  unfold lamHat
  rw [iStar_eq, bHat_eq]
  show (4 : ℝ) + 2 / 3 * 1 = 14 / 3
  norm_num

lemma pTildeHat_eq : pTildeHat I0.toPublic (sales I0 ωs) = 4 := by
  unfold pTildeHat
  rw [lamHat_eq, bHat_eq]
  show ((14 / 3 : ℝ) - 2) / (2 / 3) = 4
  norm_num

lemma shiftedMean_eq : shiftedMean I0.toPublic (sales I0 ωs) =
    (3 + 2 / 3 + (299999999 : ℝ) * (4 + 2 / 3)) / 300000000 := by
  unfold shiftedMean
  rw [iStar_eq, bHat_eq]
  simp only [sales_zero]
  show (∑ j : Fin (299999999 + 1), ((if (j : ℕ) = 0 then (3 : ℝ) else 4) + 2 / 3 * 1)) /
      ((300000000 : ℕ) : ℝ) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, if_pos, Nat.add_one_ne_zero, if_false,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

lemma RHatMax_eq : RHatMax I0.toPublic (sales I0 ωs) 4 =
    4 * (-(1 : ℝ) * (2 / 3) * 4 + (3 + 2 / 3 + (299999999 : ℝ) * (4 + 2 / 3)) / 300000000 +
      (1 - 1) * (2 - 14 / 3)) := by
  unfold RHatMax
  rw [if_neg (by rw [pTildeHat_eq]; norm_num)]
  unfold R1Hat
  rw [gammaHatMax_eq, bHat_eq, shiftedMean_eq, lamHat_eq]
  rfl

lemma RF_le (μ : Measure ℝ) (hμ : μ ∈ Amb I0) : RF I0 μ 4 ≤ 4 := by
  obtain ⟨hp, hc⟩ := hμ
  have h5 : μ (Iic 5) = 1 := by
    rw [hc 5 (by rw [lam_I0]; norm_num)]
    exact μ0_full _ (by norm_num) (by norm_num)
  have hcompl : μ (Iic 5)ᶜ = 0 := (prob_compl_eq_zero_iff measurableSet_Iic).2 h5
  have hae : ∀ᵐ ξ ∂μ, min (ξ - I0.b * 4) I0.y ≤ 1 := by
    rw [ae_iff]
    refine measure_mono_null (fun ξ hξ => ?_) hcompl
    simp only [Set.mem_setOf_eq] at hξ
    intro h
    apply hξ
    simp only [Set.mem_Iic] at h
    show min (ξ - 1 * 4) 2 ≤ 1
    exact min_le_of_left_le (by linarith)
  unfold RF
  have hi : ∫ ξ, min (ξ - I0.b * 4) I0.y ∂μ ≤ 1 := by
    by_cases hint : Integrable (fun ξ => min (ξ - I0.b * 4) I0.y) μ
    · calc _ ≤ ∫ _ξ, (1 : ℝ) ∂μ := integral_mono_ae hint (integrable_const 1) hae
        _ = 1 := by simp
    · rw [integral_undef hint]; norm_num
  linarith

lemma Rmax_le : Rmax I0 4 ≤ 4 := by
  unfold Rmax
  apply Real.sSup_le _ (by norm_num)
  rintro x ⟨μ, hμ, rfl⟩
  exact RF_le μ hμ

lemma event_mem : ((∃ q ∈ Icc I0.plo I0.phi,
      (3 : ℝ) < |RHatMax I0.toPublic (sales I0 ωs) q - Rmax I0 q|) ∨
    (∃ q ∈ Icc I0.plo I0.phi, (3 : ℝ) < |RHatMin I0.toPublic (sales I0 ωs) q - Rmin I0 q|)) ∧
    ∀ i, 0 < gammaHat I0.toPublic (sales I0 ωs) i := by
  refine ⟨Or.inl ⟨4, ⟨by norm_num [I0], by norm_num [I0]⟩, ?_⟩, gammaHat_pos⟩
  refine lt_of_lt_of_le ?_ (le_abs_self _)
  rw [RHatMax_eq]
  have := Rmax_le
  norm_num
  linarith

lemma pi_measure :
    dataLaw I0 Nv0 (Set.univ.pi (fun i => Set.univ.pi (fun j => ({ωs i j} : Set ℝ)))) =
      ENNReal.ofReal ((1 / 1200000000) * (1199999999 / 1200000000) ^ 599999999) := by
  unfold dataLaw
  rw [Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fin.prod_univ_two]
  have hI : I0.μξ = μ0 := rfl
  rw [hI]
  have h1 : ∀ j : Fin (Nv0 1), ωs 1 j = 5 := fun j => by simp [ωs]
  simp only [h1, μ0_five, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : (∏ j : Fin (Nv0 0), μ0 {ωs 0 j}) =
      ENNReal.ofReal (1 / 1200000000) * ENNReal.ofReal (1199999999 / 1200000000) ^ 299999999 := by
    show (∏ j : Fin (299999999 + 1), μ0 {ωs 0 j}) = _
    rw [Fin.prod_univ_succ]
    have e0 : ωs 0 (0 : Fin (299999999 + 1)) = 4 := by simp [ωs]
    have es : ∀ j : Fin 299999999, ωs 0 (Fin.succ j : Fin (299999999 + 1)) = 5 := fun j => by
      simp [ωs, Fin.val_succ]
    rw [e0, μ0_four]
    simp only [es, μ0_five, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h0]
  show ENNReal.ofReal (1 / 1200000000) * ENNReal.ofReal (1199999999 / 1200000000) ^ 299999999 *
    ENNReal.ofReal (1199999999 / 1200000000) ^ 300000000 = _
  rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  rw [mul_assoc, ← pow_add]

lemma real_gap :
    16 * Real.exp (-40) < (1 / 1200000000) * (1199999999 / 1200000000 : ℝ) ^ 599999999 := by
  have hb : (1 : ℝ) / 2 ≤ (1199999999 / 1200000000 : ℝ) ^ 599999999 := by
    have e : (1 : ℝ) + (-1 / 1200000000) = 1199999999 / 1200000000 := by norm_num
    calc (1 : ℝ) / 2 ≤ 1 + ((599999999 : ℕ) : ℝ) * (-1 / 1200000000) := by norm_num
      _ ≤ (1 + (-1 / 1200000000)) ^ 599999999 := one_add_mul_le_pow (by norm_num) 599999999
      _ = (1199999999 / 1200000000 : ℝ) ^ 599999999 := by rw [e]
  generalize (1199999999 / 1200000000 : ℝ) ^ 599999999 = q at hb ⊢
  have he : (2.7 : ℝ) ^ 40 < Real.exp 40 := by
    have h := Real.exp_one_pow 40
    push_cast at h
    rw [← h]
    exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by norm_num)
  have hpos : 0 < Real.exp 40 := Real.exp_pos _
  rw [Real.exp_neg]
  have : 16 * (Real.exp 40)⁻¹ < 1 / 2400000000 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
    norm_num at he ⊢
    linarith
  have hq : (1 : ℝ) / 2400000000 ≤ 1 / 1200000000 * q := by linarith
  linarith

lemma priceVar_I0 : priceVar I0.toPublic = 9 / 4 := by
  unfold priceVar
  simp [I0, Fin.sum_univ_two]; norm_num

lemma C1_I0 : C1 I0 = 6881 / 4 := by
  unfold C1
  rw [lamBar_I0]
  show (5 : ℝ) * 4 ^ 2 + (2 * 2 + 3 * 1 * 4 + 2 * (11 / 2)) ^ 2 / (2 / 3) ^ 2 = 6881 / 4
  norm_num

lemma C2_I0 : C2 I0 = 46 := by
  unfold C2
  rw [lamBar_I0]
  show (4 : ℝ) * (2 + 11 / 2 + 4 * 1) = 46
  norm_num

lemma rhs_le :
    2 * ((2 : ℕ) : ℝ) * Real.exp (-((Nmin Nv0 : ℝ) * 3 ^ 2 /
        (36 * (I0.y + I0.bhi * I0.phi) ^ 2 * I0.phi ^ 2))) +
      2 * ((2 : ℕ) : ℝ) * Real.exp (-(priceVar I0.toPublic * I0.g ^ 2 / (36 * C1 I0 ^ 2) *
        (Nmin Nv0 : ℝ) * 3 ^ 2)) +
      2 * ((2 : ℕ) : ℝ) * Real.exp (-((Nmin Nv0 : ℝ) * 3 ^ 2 / (18 * C2 I0 ^ 2))) +
      2 * ((2 : ℕ) : ℝ) * Real.exp (-((Nmin Nv0 : ℝ) * 3 ^ 2 / (18 * I0.phi ^ 2 * lamBar I0 ^ 2)))
      ≤ 16 * Real.exp (-40) := by
  rw [Nmin_Nv0, priceVar_I0, C1_I0, C2_I0, lamBar_I0]
  have hy : I0.y = 2 := rfl
  have hb : I0.bhi = 1 := rfl
  have hp : I0.phi = 4 := rfl
  have hg : I0.g = 99 / 100 := rfl
  rw [hy, hb, hp, hg]
  have e1 : Real.exp (-(((300000000 : ℕ) : ℝ) * 3 ^ 2 / (36 * (2 + 1 * 4) ^ 2 * 4 ^ 2))) ≤
      Real.exp (-40) := Real.exp_le_exp.2 (by norm_num)
  have e2 : Real.exp (-(9 / 4 * (99 / 100) ^ 2 / (36 * (6881 / 4) ^ 2) *
      ((300000000 : ℕ) : ℝ) * 3 ^ 2)) ≤ Real.exp (-40) := Real.exp_le_exp.2 (by norm_num)
  have e3 : Real.exp (-(((300000000 : ℕ) : ℝ) * 3 ^ 2 / (18 * 46 ^ 2))) ≤ Real.exp (-40) :=
    Real.exp_le_exp.2 (by norm_num)
  have e4 : Real.exp (-(((300000000 : ℕ) : ℝ) * 3 ^ 2 / (18 * 4 ^ 2 * (11 / 2) ^ 2))) ≤
      Real.exp (-40) := Real.exp_le_exp.2 (by norm_num)
  have : (2 : ℝ) * ((2 : ℕ) : ℝ) = 4 := by norm_num
  rw [this]
  linarith

end DpA61f

open MeasureTheory Set in
open OfflineCensoredPricing.Identifiability in
theorem solution : ¬ (∀ {K : ℕ} [NeZero K] (I : Instance K) (hI : I.Standing) (Nv : Fin K → ℕ)
    {α : ℝ} (hα : 0 < α),
    dataLaw I Nv {ω | ((∃ q ∈ Icc I.plo I.phi, α < |RHatMax I.toPublic (sales I ω) q - Rmax I q|) ∨
          (∃ q ∈ Icc I.plo I.phi, α < |RHatMin I.toPublic (sales I ω) q - Rmin I q|)) ∧
        ∀ i, 0 < gammaHat I.toPublic (sales I ω) i} ≤
      ENNReal.ofReal
        (2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (36 * (I.y + I.bhi * I.phi) ^ 2 * I.phi ^ 2))) +
          2 * K * Real.exp (-(priceVar I.toPublic * I.g ^ 2 / (36 * C1 I ^ 2) *
            (Nmin Nv : ℝ) * α ^ 2)) +
          2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * C2 I ^ 2))) +
          2 * K * Real.exp (-((Nmin Nv : ℝ) * α ^ 2 / (18 * I.phi ^ 2 * lamBar I ^ 2))))) := by
  intro h
  have h1 := h DpA61f.I0 DpA61f.standing_I0 DpA61f.Nv0 (α := 3) (by norm_num)
  refine absurd h1 (not_le.2 ?_)
  refine lt_of_le_of_lt (b := ENNReal.ofReal (16 * Real.exp (-40))) ?_ ?_
  · apply ENNReal.ofReal_le_ofReal
    exact DpA61f.rhs_le
  · refine lt_of_lt_of_le ?_ (measure_mono (s := Set.univ.pi
        (fun i => Set.univ.pi (fun j => ({DpA61f.ωs i j} : Set ℝ)))) ?_)
    · rw [DpA61f.pi_measure]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 DpA61f.real_gap
    · intro ω hω
      have hω' : ω = DpA61f.ωs := by
        funext i j
        have := hω i (Set.mem_univ _) j (Set.mem_univ _)
        simpa using this
      subst hω'
      exact DpA61f.event_mem
