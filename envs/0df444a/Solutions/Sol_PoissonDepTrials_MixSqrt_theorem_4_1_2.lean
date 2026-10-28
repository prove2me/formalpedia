-- Prove2me | solution 2 for PoissonDepTrials.MixSqrt.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:41.282797+00:00
-- url     : https://prove2.me/submissions/c274244d-a975-45f2-a6d2-bc807fe63b7a

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting
import Theorems.Thm_PoissonDepTrials_MixSqrt_identity_2_6
import Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_3_3
import Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_3_4
import Theorems.Thm_PoissonDepTrials_MixSqrt_lemma_4_5

-- carved verbatim out of submission d366b67a-e59e-4992-8bc8-3bb5a049791c, lines 1726-1737

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem cs410_card_le (n m i : ℕ) :
    ((Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m)).card ≤ 2 * m + 1 := by
  have h := Finset.card_le_card_of_injOn (fun j : ℕ => (j : ℤ))
    (s := (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m))
    (t := Finset.Icc ((i : ℤ) - m) ((i : ℤ) + m)) ?_ ?_
  · rw [Int.card_Icc] at h
    omega
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_Icc, Set.mem_Icc]
    have := abs_le.mp hj.2
    constructor <;> linarith [this.1, this.2]
  · intro a _ b _ hab
    simpa using hab

theorem cs410_real (n m : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m, f i * f j
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, f i ^ 2 := by
  set S : ℕ → Finset ℕ := fun i =>
    (Finset.Icc 1 n).filter (fun j : ℕ => |(i : ℤ) - ((j : ℕ) : ℤ)| ≤ m) with hS
  have hA : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2
      ≤ (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, f i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hc : (S i).card ≤ 2 * m + 1 := cs410_card_le n m i
    exact_mod_cast hc
  have hB : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f j ^ 2
      = ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2 := by
    simp only [hS, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_sub_comm]
  have hpt : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i * f j
      ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, (f i ^ 2 + f j ^ 2) / 2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    nlinarith [sq_nonneg (f i - f j)]
  have hsplit : ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, (f i ^ 2 + f j ^ 2) / 2
      = (∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i ^ 2
         + ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f j ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  show ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ S i, f i * f j ≤ _
  linarith [hpt, hsplit, hA, hB]

end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open PoissonDepTrials.MixSqrt

theorem measurable_X_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i : ℕ) :
    Measurable (fun ω => (X i ω : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (hX.1 i)

theorem X_le_one_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i : ℕ) :
    ∀ᵐ ω ∂P, (X i ω : ℝ) ≤ 1 := by
  filter_upwards [hX.2.2 i] with ω hω
  exact_mod_cast hω

theorem integrable_X {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i : ℕ) :
    Integrable (fun ω => (X i ω : ℝ)) P := by
  refine Integrable.of_bound (measurable_X_real hX i).aestronglyMeasurable 1 ?_
  filter_upwards [X_le_one_real hX i] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact hω

theorem integrable_XX {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : ℕ → Ω → ℕ} (hX : IsBernoulliTrials P n X) (i j : ℕ) :
    Integrable (fun ω => (X i ω : ℝ) * X j ω) P := by
  refine Integrable.of_bound
    ((measurable_X_real hX i).mul (measurable_X_real hX j)).aestronglyMeasurable 1 ?_
  filter_upwards [X_le_one_real hX i, X_le_one_real hX j] with ω hi hj
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 : (0 : ℝ) ≤ X j ω := Nat.cast_nonneg _
  nlinarith

theorem integral_X_eq_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (j : ℕ) :
    ∫ ω, (X j ω : ℝ) ∂P = prob P X j := by
  have hms : MeasurableSet {ω | X j ω = 1} := (hX.1 j) (measurableSet_singleton 1)
  have hae : (fun ω => (X j ω : ℝ)) =ᵐ[P] {ω | X j ω = 1}.indicator 1 := by
    filter_upwards [hX.2.2 j] with ω hω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [integral_congr_ae hae, integral_indicator_one hms]
  rfl

theorem prob_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ) (i : ℕ) :
    0 ≤ prob P X i := measureReal_nonneg

theorem abs_integral_mul_delta_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ) (hF0 : ∀ ω, 0 ≤ F ω) (hF : Integrable F P) (g : ℕ → ℝ) (C : ℝ)
    (hg : ∀ w : ℕ, 1 ≤ w → |g w| ≤ C) (G : Ω → ℕ) :
    |∫ ω, F ω * g (G ω + 1) ∂P| ≤ C * ∫ ω, F ω ∂P := by
  rw [← integral_const_mul]
  have := norm_integral_le_of_norm_le (hF.const_mul C) (μ := P)
    (f := fun ω => F ω * g (G ω + 1)) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hF0 ω), mul_comm C]
      exact mul_le_mul_of_nonneg_left (hg _ (by omega)) (hF0 ω))
  rwa [Real.norm_eq_abs] at this

theorem sigmaIcc_le {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] {X : ℕ → Ω → β}
    (hXm : ∀ i, Measurable (X i)) (a b : ℕ) : sigmaIcc X a b ≤ mΩ :=
  iSup₂_le fun i _ => (hXm i).comap_le

theorem sigmaIci_le {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] {X : ℕ → Ω → β}
    (hXm : ∀ i, Measurable (X i)) (a : ℕ) : sigmaIci X a ≤ mΩ :=
  iSup₂_le fun i _ => (hXm i).comap_le

theorem meas_sigmaIcc {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a b i : ℕ)
    (hi : i ∈ Finset.Icc a b) : Measurable[sigmaIcc X a b] (X i) :=
  Measurable.mono (comap_measurable (X i))
    (le_iSup₂ (f := fun i (_ : i ∈ Finset.Icc a b) => MeasurableSpace.comap (X i) inferInstance)
      i hi) le_rfl

theorem meas_sigmaIci {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a i : ℕ)
    (hi : a ≤ i) : Measurable[sigmaIci X a] (X i) :=
  Measurable.mono (comap_measurable (X i))
    (le_iSup₂ (f := fun i (_ : i ∈ Set.Ici a) => MeasurableSpace.comap (X i) inferInstance)
      i (Set.mem_Ici.mpr hi)) le_rfl

theorem mix_cov {Ω β : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → β) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (U : Ω → ℝ)
    (hU : StronglyMeasurable[sigmaIcc X 1 j] U) (hU0 : ∀ ω, 0 ≤ U ω) (C : ℝ)
    (hUC : ∀ ω, U ω ≤ C) (B : Set Ω) (hB : MeasurableSet[sigmaIci X (j + k)] B) :
    |∫ ω, U ω * B.indicator (fun _ => (1 : ℝ)) ω ∂P - (∫ ω, U ω ∂P) * P.real B|
      ≤ φ k * ∫ ω, U ω ∂P := by
  have hle := sigmaIcc_le hXm 1 j
  have hBm : MeasurableSet B := sigmaIci_le hXm (j + k) B hB
  have hb := hφ.2.2 j k hj hk B hB
  set g : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hg
  have hg1 : ∀ ω, |g ω| ≤ 1 := fun ω => by
    rw [hg]; unfold Set.indicator; split_ifs <;> simp
  have hgi : Integrable g P := (integrable_const (1 : ℝ)).indicator hBm
  have hUm : StronglyMeasurable U := hU.mono hle
  have hUi : Integrable U P := Integrable.of_bound hUm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 ω)]; exact hUC ω)
  have hUgi : Integrable (U * g) P := by
    refine Integrable.of_bound (hUm.mul (stronglyMeasurable_const.indicator hBm)).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (hU0 ω)]
    nlinarith [hU0 ω, hUC ω, hg1 ω, abs_nonneg (g ω)]
  have hce := condExp_mul_of_stronglyMeasurable_left hU hUgi hgi
  have hci : Integrable (fun ω => U ω * (P[g | sigmaIcc X 1 j]) ω) P :=
    integrable_condExp.congr hce
  have h1 : ∫ ω, U ω * g ω ∂P = ∫ ω, U ω * (P[g | sigmaIcc X 1 j]) ω ∂P := by
    rw [← integral_condExp hle (f := fun ω => U ω * g ω)]
    exact integral_congr_ae hce
  have h2 : ∫ ω, U ω * (P[g | sigmaIcc X 1 j]) ω ∂P - (∫ ω, U ω ∂P) * P.real B
      = ∫ ω, U ω * ((P[g | sigmaIcc X 1 j]) ω - P.real B) ∂P := by
    rw [← integral_mul_const, ← integral_sub hci (hUi.mul_const _)]
    congr 1
    ext ω
    ring
  rw [h1, h2, ← integral_const_mul]
  have := norm_integral_le_of_norm_le (hUi.const_mul (φ k))
    (f := fun ω => U ω * ((P[g | sigmaIcc X 1 j]) ω - P.real B)) (hb.mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU0 ω), mul_comm (φ k)]
      exact mul_le_mul_of_nonneg_left hω (hU0 ω))
  rwa [Real.norm_eq_abs] at this

theorem ind_abs_le_one {Ω : Type*} (S : Set Ω) (ω : Ω) :
    |S.indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
  unfold Set.indicator; split_ifs <;> simp

theorem ind_nonneg {Ω : Type*} (S : Set Ω) (ω : Ω) : 0 ≤ S.indicator (fun _ => (1 : ℝ)) ω :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) ω

theorem ind_le_one {Ω : Type*} (S : Set Ω) (ω : Ω) : S.indicator (fun _ => (1 : ℝ)) ω ≤ 1 :=
  (le_abs_self _).trans (ind_abs_le_one S ω)

theorem sum_ind_eq {Ω : Type*} (Z : Ω → ℕ) (S : Finset ℕ) (ω : Ω) :
    ∑ b ∈ S, {ω | Z ω = b}.indicator (fun _ => (1 : ℝ)) ω
      = (Z ⁻¹' (S : Set ℕ)).indicator (fun _ => (1 : ℝ)) ω := by
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_ite_eq]
  unfold Set.indicator
  split_ifs <;> simp_all

theorem sum_ind_le_one {Ω : Type*} (Z : Ω → ℕ) (S : Finset ℕ) (ω : Ω) :
    ∑ b ∈ S, {ω | Z ω = b}.indicator (fun _ => (1 : ℝ)) ω ≤ 1 := by
  rw [sum_ind_eq]; exact ind_le_one _ ω

theorem int_mul_ind {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : Ω → ℝ} (hUm : StronglyMeasurable U) (hU0 : ∀ ω, 0 ≤ U ω) (C : ℝ) (hUC : ∀ ω, U ω ≤ C)
    (S : Set Ω) (hS : MeasurableSet S) :
    Integrable (fun ω => U ω * S.indicator (fun _ => (1 : ℝ)) ω) P := by
  refine Integrable.of_bound (hUm.mul (stronglyMeasurable_const.indicator hS)).aestronglyMeasurable
    C (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hU0 ω)]
  nlinarith [hU0 ω, hUC ω, ind_abs_le_one S ω, abs_nonneg (S.indicator (fun _ => (1 : ℝ)) ω)]

theorem mix_cov_fun {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℕ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (U : Ω → ℝ) (hU : StronglyMeasurable[sigmaIcc X 1 j] U)
    (hU0 : ∀ ω, 0 ≤ U ω) (C : ℝ) (hUC : ∀ ω, U ω ≤ C)
    (Z : Ω → ℕ) (hZ : Measurable[sigmaIci X (j + k)] Z) (N : ℕ) (hZN : ∀ᵐ ω ∂P, Z ω ≤ N)
    (g : ℕ → ℝ) (M : ℝ) (hg : ∀ b, |g b| ≤ M) :
    |∫ ω, U ω * g (Z ω) ∂P - (∫ ω, U ω ∂P) * ∫ ω, g (Z ω) ∂P|
      ≤ 2 * M * (φ k * ∫ ω, U ω ∂P) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hg 0)
  have hZm : Measurable Z := hZ.mono (sigmaIci_le hXm _) le_rfl
  have hUm : StronglyMeasurable U := hU.mono (sigmaIcc_le hXm 1 j)
  have hUi : Integrable U P := Integrable.of_bound hUm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hU0 ω)]; exact hUC ω)
  set R := Finset.range (N + 1) with hR
  set I : ℕ → Ω → ℝ := fun b => {ω | Z ω = b}.indicator (fun _ => (1 : ℝ)) with hI
  have hIm : ∀ b, MeasurableSet {ω | Z ω = b} := fun b => hZm (measurableSet_singleton b)
  have hIi : ∀ b, Integrable (I b) P := fun b => (integrable_const (1 : ℝ)).indicator (hIm b)
  have hUIi : ∀ b, Integrable (fun ω => U ω * I b ω) P := fun b =>
    int_mul_ind hUm hU0 C hUC _ (hIm b)
  have hdec : ∀ᵐ ω ∂P, g (Z ω) = ∑ b ∈ R, g b * I b ω := by
    filter_upwards [hZN] with ω hω
    simp only [hI, Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hω))]
  have hdecU : ∀ᵐ ω ∂P, U ω * g (Z ω) = ∑ b ∈ R, g b * (U ω * I b ω) := by
    filter_upwards [hdec] with ω hω
    rw [hω, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e1 : ∫ ω, U ω * g (Z ω) ∂P = ∑ b ∈ R, g b * ∫ ω, U ω * I b ω ∂P := by
    rw [integral_congr_ae hdecU, integral_finset_sum _ fun b _ => (hUIi b).const_mul (g b)]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  have e2 : ∫ ω, g (Z ω) ∂P = ∑ b ∈ R, g b * ∫ ω, I b ω ∂P := by
    rw [integral_congr_ae hdec, integral_finset_sum _ fun b _ => (hIi b).const_mul (g b)]
    exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _
  set c : ℕ → ℝ := fun b => ∫ ω, U ω * I b ω ∂P - (∫ ω, U ω ∂P) * ∫ ω, I b ω ∂P with hc
  have e3 : ∫ ω, U ω * g (Z ω) ∂P - (∫ ω, U ω ∂P) * ∫ ω, g (Z ω) ∂P = ∑ b ∈ R, g b * c b := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by simp only [hc]; ring
  have hS : ∀ S : Finset ℕ, |∑ b ∈ S, c b| ≤ φ k * ∫ ω, U ω ∂P := by
    intro S
    have hB : MeasurableSet[sigmaIci X (j + k)] (Z ⁻¹' (S : Set ℕ)) :=
      hZ (Set.Finite.measurableSet S.finite_toSet)
    have hBm : MeasurableSet (Z ⁻¹' (S : Set ℕ)) := hZm (Set.Finite.measurableSet S.finite_toSet)
    have key := mix_cov P X hXm φ hφ j k hj hk U hU hU0 C hUC _ hB
    have s1 : ∑ b ∈ S, ∫ ω, U ω * I b ω ∂P
        = ∫ ω, U ω * (Z ⁻¹' (S : Set ℕ)).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      rw [← integral_finset_sum _ fun b _ => hUIi b]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only
      rw [← Finset.mul_sum, sum_ind_eq]
    have s2 : ∑ b ∈ S, ∫ ω, I b ω ∂P = P.real (Z ⁻¹' (S : Set ℕ)) := by
      rw [← integral_finset_sum _ fun b _ => hIi b, ← integral_indicator_one hBm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hI]
      rw [sum_ind_eq]
      rfl
    have : ∑ b ∈ S, c b = ∫ ω, U ω * (Z ⁻¹' (S : Set ℕ)).indicator (fun _ => (1 : ℝ)) ω ∂P
        - (∫ ω, U ω ∂P) * P.real (Z ⁻¹' (S : Set ℕ)) := by
      simp only [hc]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, s1, s2]
    rw [this]; exact key
  have habs : ∑ b ∈ R, |c b| ≤ 2 * (φ k * ∫ ω, U ω ∂P) := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun b => 0 ≤ c b)]
    have h1 : ∑ b ∈ R with 0 ≤ c b, |c b| = ∑ b ∈ R with 0 ≤ c b, c b :=
      Finset.sum_congr rfl fun b hb => abs_of_nonneg (Finset.mem_filter.mp hb).2
    have h2 : ∑ b ∈ R with ¬ 0 ≤ c b, |c b| = -∑ b ∈ R with ¬ 0 ≤ c b, c b := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b hb => abs_of_neg (not_le.mp (Finset.mem_filter.mp hb).2)
    rw [h1, h2]
    have a1 := hS (R.filter (fun b => 0 ≤ c b))
    have a2 := hS (R.filter (fun b => ¬ 0 ≤ c b))
    have := le_abs_self (∑ b ∈ R with 0 ≤ c b, c b)
    have := neg_abs_le (∑ b ∈ R with ¬ 0 ≤ c b, c b)
    linarith
  rw [e3]
  calc |∑ b ∈ R, g b * c b| ≤ ∑ b ∈ R, |g b * c b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ R, M * |c b| := Finset.sum_le_sum fun b _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hg b) (abs_nonneg _)
    _ = M * ∑ b ∈ R, |c b| := by rw [Finset.mul_sum]
    _ ≤ M * (2 * (φ k * ∫ ω, U ω ∂P)) := mul_le_mul_of_nonneg_left habs hM0
    _ = 2 * M * (φ k * ∫ ω, U ω ∂P) := by ring

theorem V_split {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (ω : Ω) :
    V n m X i ω = ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k + m < i), X k ω
      + ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => i + m < k), X k ω := by
  simp only [V]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 n).filter (fun k : ℕ => m < Int.natAbs ((k : ℤ) - i))) (fun k => k + m < i)]
  congr 1
  · rw [Finset.filter_filter]
    exact Finset.sum_congr (Finset.filter_congr fun k _ => by omega) fun _ _ => rfl
  · rw [Finset.filter_filter]
    exact Finset.sum_congr (Finset.filter_congr fun k _ => by omega) fun _ _ => rfl

theorem sum_filter_le_n {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) (q : ℕ → Prop) [DecidablePred q]
    (ω : Ω) (hω : ∀ k, X k ω ≤ 1) :
    ∑ k ∈ (Finset.Icc 1 n).filter q, X k ω ≤ n := by
  calc ∑ k ∈ (Finset.Icc 1 n).filter q, X k ω ≤ ∑ k ∈ (Finset.Icc 1 n).filter q, 1 :=
        Finset.sum_le_sum fun k _ => hω k
    _ = ((Finset.Icc 1 n).filter q).card := by simp
    _ ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem per_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M)
    (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
    |∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P| ≤ 6 * M * φ (m + 1) := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hφ0 : ∀ k, 0 ≤ φ k := fun k => hφ.1.le_of_tendsto hφ.2.1 k
  have hb : ∀ᵐ ω ∂P, ∀ k, X k ω ≤ 1 := ae_all_iff.mpr hX.2.2
  have hp0 := prob_nonneg P X i
  have hp1 : prob P X i ≤ 1 := measureReal_le_one
  set A : Ω → ℕ := fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => k + m < i), X k ω with hA
  set B : Ω → ℕ := fun ω => ∑ k ∈ (Finset.Icc 1 n).filter (fun k : ℕ => i + m < k), X k ω with hB
  set U : Ω → ℝ := {ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) with hU
  have hV : ∀ ω, V n m X i ω = A ω + B ω := fun ω => V_split n m X i ω
  have hUa : (fun ω => (X i ω : ℝ)) =ᵐ[P] U := by
    filter_upwards [hX.2.2 i] with ω hω
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hω with h | h <;> simp [hU, h]
  have hEU : ∫ ω, U ω ∂P = prob P X i := by
    rw [← integral_congr_ae hUa]; exact integral_X_eq_prob P n X hX i
  have hUms : MeasurableSet {ω | X i ω = 1} := (hX.1 i) (measurableSet_singleton 1)
  have hUsm : StronglyMeasurable[sigmaIcc X 1 i] U :=
    (stronglyMeasurable_const.indicator
      ((meas_sigmaIcc X 1 i i (Finset.mem_Icc.mpr ⟨hi1, le_rfl⟩)) (measurableSet_singleton 1)))
  have hBm : Measurable[sigmaIci X (i + (m + 1))] B :=
    Finset.measurable_sum _ fun k hk => meas_sigmaIci X _ k (by
      have := (Finset.mem_filter.mp hk).2; omega)
  have hBN : ∀ᵐ ω ∂P, B ω ≤ n := hb.mono fun ω hω => sum_filter_le_n n X _ ω hω
  have hAN : ∀ᵐ ω ∂P, A ω ≤ n := hb.mono fun ω hω => sum_filter_le_n n X _ ω hω
  have hAm' : ∀ J, i ≤ J + m + 1 → Measurable[sigmaIcc X 1 J] A := fun J hJ =>
    Finset.measurable_sum _ fun k hk => meas_sigmaIcc X 1 J k (by
      have h1 := Finset.mem_filter.mp hk
      have h2 := Finset.mem_Icc.mp h1.1
      exact Finset.mem_Icc.mpr ⟨h2.1, by omega⟩)
  have hAm : Measurable A := (hAm' i (by omega)).mono (sigmaIcc_le hX.1 1 i) le_rfl
  have hBmm : Measurable B := hBm.mono (sigmaIci_le hX.1 _) le_rfl
  have hfV : Measurable (fun ω => f (A ω + B ω + 1)) :=
    (measurable_of_countable (fun k : ℕ => f (k + 1))).comp (hAm.add hBmm)
  have hfVi : Integrable (fun ω => f (A ω + B ω + 1)) P :=
    Integrable.of_bound hfV.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM _)
  have hUf : Integrable (fun ω => U ω * f (A ω + B ω + 1)) P := by
    refine Integrable.of_bound ((stronglyMeasurable_const.indicator hUms).mul
      hfV.stronglyMeasurable).aestronglyMeasurable M (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [ind_abs_le_one {ω | X i ω = 1} ω, abs_nonneg (f (A ω + B ω + 1)), hM (A ω + B ω + 1),
      abs_nonneg ({ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) ω)]
  -- rewrite the integral
  have hmain : ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P
      = ∫ ω, U ω * f (A ω + B ω + 1) ∂P - (∫ ω, U ω ∂P) * ∫ ω, f (A ω + B ω + 1) ∂P := by
    rw [hEU, ← integral_const_mul, ← integral_sub hUf (hfVi.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [hUa] with ω hω
    rw [hV ω, ← hω]
    ring
  rw [hmain]
  have hU01 : ∀ ω, 0 ≤ U ω ∧ U ω ≤ 1 := fun ω => ⟨ind_nonneg _ ω, ind_le_one _ ω⟩
  have hUsm' : StronglyMeasurable U := stronglyMeasurable_const.indicator hUms
  have hUi : Integrable U P := (integrable_const (1 : ℝ)).indicator hUms
  have hMφ : 0 ≤ M * φ (m + 1) := mul_nonneg hM0 (hφ0 _)
  rcases le_or_gt i (m + 1) with hsmall | hbig
  · have hA0 : ∀ ω, A ω = 0 := fun ω => by
      simp only [hA]
      apply Finset.sum_eq_zero
      intro k hk
      have h1 := Finset.mem_filter.mp hk
      have h2 := Finset.mem_Icc.mp h1.1
      exfalso; omega
    simp only [hA0, zero_add]
    have h := mix_cov_fun P X hX.1 φ hφ i (m + 1) hi1 (by omega) U hUsm (fun ω => (hU01 ω).1) 1
      (fun ω => (hU01 ω).2) B hBm n hBN (fun b => f (b + 1)) M (fun b => hM _)
    calc _ ≤ 2 * M * (φ (m + 1) * ∫ ω, U ω ∂P) := h
      _ = 2 * M * (φ (m + 1) * prob P X i) := by rw [hEU]
      _ ≤ 6 * M * φ (m + 1) := by nlinarith [mul_le_mul_of_nonneg_left hp1 hMφ]
  · obtain ⟨J, hJ⟩ : ∃ J, i = J + m + 1 := ⟨i - m - 1, by omega⟩
    have hJ1 : 1 ≤ J := by omega
    set R := Finset.range (n + 1) with hR
    set I : ℕ → Ω → ℝ := fun a => {ω | A ω = a}.indicator (fun _ => (1 : ℝ)) with hI
    have hI01 : ∀ a ω, 0 ≤ I a ω ∧ I a ω ≤ 1 := fun a ω => ⟨ind_nonneg _ ω, ind_le_one _ ω⟩
    have hIm : ∀ a, MeasurableSet {ω | A ω = a} := fun a => hAm (measurableSet_singleton a)
    have hIsm : ∀ a, StronglyMeasurable[sigmaIcc X 1 J] (I a) := fun a =>
      stronglyMeasurable_const.indicator ((hAm' J (by omega)) (measurableSet_singleton a))
    have hIsmi : ∀ a, StronglyMeasurable[sigmaIcc X 1 i] (I a) := fun a =>
      stronglyMeasurable_const.indicator ((hAm' i (by omega)) (measurableSet_singleton a))
    have hIsm' : ∀ a, StronglyMeasurable (I a) := fun a =>
      stronglyMeasurable_const.indicator (hIm a)
    have hIi : ∀ a, Integrable (I a) P := fun a => (integrable_const (1 : ℝ)).indicator (hIm a)
    have hgB : ∀ a : ℕ, Measurable (fun ω => f (a + B ω + 1)) := fun a =>
      (measurable_of_countable (fun b : ℕ => f (a + b + 1))).comp hBmm
    have hIg : ∀ a, Integrable (fun ω => I a ω * f (a + B ω + 1)) P := fun a => by
      refine Integrable.of_bound ((hIsm' a).mul (hgB a).stronglyMeasurable).aestronglyMeasurable M
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hI01 a ω).1]
      nlinarith [hI01 a ω, hM (a + B ω + 1), abs_nonneg (f (a + B ω + 1))]
    have hUIg : ∀ a, Integrable (fun ω => U ω * I a ω * f (a + B ω + 1)) P := fun a => by
      refine Integrable.of_bound ((hUsm'.mul (hIsm' a)).mul
        (hgB a).stronglyMeasurable).aestronglyMeasurable M (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hU01 ω).1 (hI01 a ω).1)]
      have h01 : U ω * I a ω ≤ 1 := by nlinarith [hU01 ω, hI01 a ω]
      nlinarith [mul_nonneg (hU01 ω).1 (hI01 a ω).1, hM (a + B ω + 1), abs_nonneg (f (a + B ω + 1))]
    have hUIi : ∀ a, Integrable (fun ω => U ω * I a ω) P := fun a =>
      int_mul_ind hUsm' (fun ω => (hU01 ω).1) 1 (fun ω => (hU01 ω).2) _ (hIm a)
    have hdec : ∀ᵐ ω ∂P, f (A ω + B ω + 1) = ∑ a ∈ R, I a ω * f (a + B ω + 1) := by
      filter_upwards [hAN] with ω hω
      simp only [hI, Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hω))]
    have hT1 : ∫ ω, U ω * f (A ω + B ω + 1) ∂P
        = ∑ a ∈ R, ∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P := by
      rw [← integral_finset_sum _ fun a _ => hUIg a]
      refine integral_congr_ae ?_
      filter_upwards [hdec] with ω hω
      rw [hω, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have hT2 : ∫ ω, f (A ω + B ω + 1) ∂P = ∑ a ∈ R, ∫ ω, I a ω * f (a + B ω + 1) ∂P := by
      rw [← integral_finset_sum _ fun a _ => hIg a]
      exact integral_congr_ae hdec
    set α : ℕ → ℝ := fun a => ∫ ω, U ω * I a ω ∂P with hα
    set β : ℕ → ℝ := fun a => ∫ ω, I a ω ∂P with hβ
    set G : ℕ → ℝ := fun a => ∫ ω, f (a + B ω + 1) ∂P with hG
    have hG1 : ∀ a, |G a| ≤ M := fun a => by
      have := norm_integral_le_of_norm_le (integrable_const M) (μ := P)
        (f := fun ω => f (a + B ω + 1))
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hM (a + B ω + 1))
      simpa [Real.norm_eq_abs] using this
    have hα0 : ∀ a, 0 ≤ α a := fun a =>
      integral_nonneg fun ω => mul_nonneg (hU01 ω).1 (hI01 a ω).1
    have hβ0 : ∀ a, 0 ≤ β a := fun a => integral_nonneg fun ω => (hI01 a ω).1
    have e1 : ∀ a, |∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P - α a * G a|
        ≤ 2 * M * (φ (m + 1) * α a) := fun a =>
      mix_cov_fun P X hX.1 φ hφ i (m + 1) hi1 (by omega) (fun ω => U ω * I a ω)
        (hUsm.mul (hIsmi a)) (fun ω => mul_nonneg (hU01 ω).1 (hI01 a ω).1) 1
        (fun ω => by nlinarith [hU01 ω, hI01 a ω])
        B hBm n hBN (fun b => f (a + b + 1)) M (fun b => hM _)
    have hBm2 : Measurable[sigmaIci X (J + (2 * m + 2))] B := by
      rw [show J + (2 * m + 2) = i + (m + 1) by omega]; exact hBm
    have e3 : ∀ a, |∫ ω, I a ω * f (a + B ω + 1) ∂P - β a * G a|
        ≤ 2 * M * (φ (m + 1) * β a) := fun a => by
      have h := mix_cov_fun P X hX.1 φ hφ J (2 * m + 2) hJ1 (by omega) (I a) (hIsm a)
        (fun ω => (hI01 a ω).1) 1 (fun ω => (hI01 a ω).2) B hBm2 n hBN
        (fun b => f (a + b + 1)) M (fun b => hM _)
      have hφa : φ (2 * m + 2) ≤ φ (m + 1) := hφ.1 (by omega)
      calc _ ≤ 2 * M * (φ (2 * m + 2) * β a) := h
        _ ≤ 2 * M * (φ (m + 1) * β a) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφa (hβ0 a)) (by linarith)
    have hXi_meas : MeasurableSet[sigmaIci X (J + (m + 1))] {ω | X i ω = 1} :=
      meas_sigmaIci X (J + (m + 1)) i (by omega) (measurableSet_singleton 1)
    have e2 : ∀ a, |α a - prob P X i * β a| ≤ φ (m + 1) * β a := fun a => by
      have h := mix_cov P X hX.1 φ hφ J (m + 1) hJ1 (by omega) (I a) (hIsm a)
        (fun ω => (hI01 a ω).1) 1 (fun ω => (hI01 a ω).2) _ hXi_meas
      have h1 : ∫ ω, I a ω * {ω | X i ω = 1}.indicator (fun _ => (1 : ℝ)) ω ∂P = α a :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
      have h2 : P.real {ω | X i ω = 1} = prob P X i := rfl
      rw [h1, h2] at h
      calc |α a - prob P X i * β a| = |α a - β a * prob P X i| := by rw [mul_comm (prob P X i)]
        _ ≤ φ (m + 1) * β a := h
    have hsα : ∑ a ∈ R, α a ≤ prob P X i := by
      rw [← hEU, ← integral_finset_sum _ fun a _ => hUIi a]
      refine integral_mono (integrable_finsetSum _ fun a _ => hUIi a) hUi fun ω => ?_
      show ∑ a ∈ R, U ω * I a ω ≤ U ω
      rw [← Finset.mul_sum]
      have := sum_ind_le_one A R ω
      nlinarith [hU01 ω]
    have hsβ : ∑ a ∈ R, β a ≤ 1 := by
      rw [← integral_finset_sum _ fun a _ => hIi a]
      have := integral_mono (integrable_finsetSum _ fun a _ => hIi a) (integrable_const (1 : ℝ))
        (μ := P) fun ω => sum_ind_le_one A R ω
      simpa using this
    rw [hT1, hT2, hEU, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have per : ∀ a ∈ R, |∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P
        - prob P X i * ∫ ω, I a ω * f (a + B ω + 1) ∂P|
        ≤ M * φ (m + 1) * β a + 2 * M * φ (m + 1) * α a
          + 2 * M * φ (m + 1) * prob P X i * β a := by
      intro a _
      have h1 := e1 a
      have h2 := e2 a
      have h3 := e3 a
      have hg := hG1 a
      set P1 := ∫ ω, U ω * I a ω * f (a + B ω + 1) ∂P
      set Q1 := ∫ ω, I a ω * f (a + B ω + 1) ∂P
      have eq : P1 - prob P X i * Q1 = (α a - prob P X i * β a) * G a + (P1 - α a * G a)
          - prob P X i * (Q1 - β a * G a) := by ring
      rw [eq]
      have k1 : |(α a - prob P X i * β a) * G a| ≤ φ (m + 1) * β a * M := by
        rw [abs_mul]
        exact mul_le_mul h2 hg (abs_nonneg _) (mul_nonneg (hφ0 _) (hβ0 a))
      have k3 : |prob P X i * (Q1 - β a * G a)| ≤ prob P X i * (2 * M * (φ (m + 1) * β a)) := by
        rw [abs_mul, abs_of_nonneg hp0]
        exact mul_le_mul_of_nonneg_left h3 hp0
      have t1 := abs_sub ((α a - prob P X i * β a) * G a + (P1 - α a * G a))
        (prob P X i * (Q1 - β a * G a))
      have t2 := abs_add_le ((α a - prob P X i * β a) * G a) (P1 - α a * G a)
      nlinarith
    calc _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ R, (M * φ (m + 1) * β a + 2 * M * φ (m + 1) * α a
          + 2 * M * φ (m + 1) * prob P X i * β a) := Finset.sum_le_sum per
      _ = M * φ (m + 1) * ∑ a ∈ R, β a + 2 * M * φ (m + 1) * ∑ a ∈ R, α a
          + 2 * M * φ (m + 1) * prob P X i * ∑ a ∈ R, β a := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]
      _ ≤ 6 * M * φ (m + 1) := by
          have hsβ0 : 0 ≤ ∑ a ∈ R, β a := Finset.sum_nonneg fun a _ => hβ0 a
          nlinarith [mul_le_mul_of_nonneg_left hsβ hMφ, mul_le_mul_of_nonneg_left hsα hMφ,
            mul_le_mul_of_nonneg_left (mul_le_mul hp1 hsβ hsβ0 zero_le_one) hMφ,
            mul_le_mul_of_nonneg_left hp1 hMφ]

theorem lemma_4_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) :
    |∑ i ∈ Finset.Icc 1 n, ∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P|
      ≤ 6 * M * n * φ (m + 1) := by
  calc _ ≤ ∑ i ∈ Finset.Icc 1 n, |∫ ω, ((X i ω : ℝ) - prob P X i) * f (V n m X i ω + 1) ∂P| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 n, 6 * M * φ (m + 1) :=
        Finset.sum_le_sum fun i hi => per_i P n X hX φ hφ m f M hM i hi
    _ = 6 * M * n * φ (m + 1) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

theorem main_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1)
    (hpos : 0 < lam P n X) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h|
      ≤ 6 * min (1 / Real.sqrt (lam P n X)) 1 * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (lam P n X + 1) * n * φ (m + 1)) := by
  set L := lam P n X with hL
  set μ := min (1 / Real.sqrt L) 1 with hμ
  have hμ0 : 0 ≤ μ := le_min (by positivity) zero_le_one
  have h34 := PoissonDepTrials.MixSqrt.lemma_3_4 L hpos h 1 hh
  have h33 := PoissonDepTrials.MixSqrt.lemma_3_3 L hpos h 1 hh
  have hid := PoissonDepTrials.MixSqrt.identity_2_6 P n X hX hpos m h 1 hh
  rw [hid]
  set T1 := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          ∫ ω, (X i ω : ℝ) * X j ω * delta (stein L h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P with hT1
  set T2 := ∑ i ∈ Finset.Icc 1 n,
          ∫ ω, ((X i ω : ℝ) - prob P X i) * stein L h (V n m X i ω + 1) ∂P with hT2
  set T3 := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein L h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P with hT3
  set S11 := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
        ∫ ω, (X i ω : ℝ) * X j ω ∂P with hS11
  set Spp := ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
        prob P X i * prob P X j with hSpp
  -- T1
  have b1 : |T1| ≤ 6 * μ * S11 := by
    calc |T1| ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          |∫ ω, (X i ω : ℝ) * X j ω * delta (stein L h) (Y' n m X i ((j : ℤ) - 1) ω + 1) ∂P| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with 0 < |(i : ℤ) - (j : ℕ)| ∧ |(i : ℤ) - (j : ℕ)| ≤ m,
          6 * μ * ∫ ω, (X i ω : ℝ) * X j ω ∂P := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have := abs_integral_mul_delta_le P (fun ω => (X i ω : ℝ) * X j ω)
            (fun ω => by positivity) (integrable_XX hX i j) (delta (stein L h)) (6 * 1 * μ) h34
            (Y' n m X i ((j : ℤ) - 1))
          simpa using this
      _ = 6 * μ * S11 := by
          rw [hS11, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  -- T3
  have b3 : |T3| ≤ 6 * μ * Spp := by
    calc |T3| ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          |prob P X i * ∫ ω, (X j ω : ℝ) * delta (stein L h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 n with |(i : ℤ) - (j : ℕ)| ≤ m,
          6 * μ * (prob P X i * prob P X j) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have := abs_integral_mul_delta_le P (fun ω => (X j ω : ℝ))
            (fun ω => by positivity) (integrable_X hX j) (delta (stein L h)) (6 * 1 * μ) h34
            (Y n m X i ((j : ℤ) - 1))
          rw [integral_X_eq_prob P n X hX j] at this
          rw [abs_mul, abs_of_nonneg (prob_nonneg P X i)]
          calc prob P X i * |∫ ω, (X j ω : ℝ) * delta (stein L h) (Y n m X i ((j : ℤ) - 1) ω + 1) ∂P|
              ≤ prob P X i * (6 * 1 * μ * prob P X j) :=
                mul_le_mul_of_nonneg_left this (prob_nonneg P X i)
            _ = 6 * μ * (prob P X i * prob P X j) := by ring
      _ = 6 * μ * Spp := by
          rw [hSpp, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  -- T2
  have hS : ∀ k, |stein L h k| ≤ 4 * μ := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [stein, Finset.range_zero, Finset.sum_empty, mul_zero, neg_zero, abs_zero]
      positivity
    · calc |stein L h k| ≤ 4 * 1 * μ := h33 k hk
        _ = 4 * μ := by ring
  have b2 : |T2| ≤ 6 * (4 * μ) * n * φ (m + 1) :=
    lemma_4_6 P n X hX φ hφ m (stein L h) (4 * μ) hS
  have h45 := PoissonDepTrials.MixSqrt.lemma_4_5 P n X hX φ hφ m
  have hcs := cs410_real n m (prob P X)
  have c45 := mul_le_mul_of_nonneg_left h45 (by positivity : (0 : ℝ) ≤ 6 * μ)
  have ccs := mul_le_mul_of_nonneg_left hcs (by positivity : (0 : ℝ) ≤ 6 * μ)
  have e : poissonExp L h + T1 + T2 - T3 - poissonExp L h = T1 + T2 - T3 := by ring
  rw [e]
  calc |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
        have := abs_add_le (T1 + T2) (-T3)
        have := abs_add_le T1 T2
        rw [sub_eq_add_neg]
        rw [abs_neg] at *
        linarith
    _ ≤ 6 * μ * S11 + 6 * (4 * μ) * n * φ (m + 1) + 6 * μ * Spp := by linarith
    _ ≤ 6 * μ * (Var[fun ω => (W n X ω : ℝ); P] - L + (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2
          + 4 * L * n * φ (m + 1)) + 6 * (4 * μ) * n * φ (m + 1)
          + 6 * μ * ((2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2) := by linarith
    _ = 6 * μ * (Var[fun ω => (W n X ω : ℝ); P] - L
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (L + 1) * n * φ (m + 1)) := by
        ring

theorem main_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (h : ℕ → ℝ)
    (hl : lam P n X = 0) :
    ∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h = 0 := by
  have hs : ∑ i ∈ Finset.Icc 1 n, prob P X i = 0 := hl
  have hXi : ∀ i ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, X i ω = 0 := by
    intro i hi
    have hp : prob P X i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => prob_nonneg P X i)).mp hs i hi
    have hz : P {ω | X i ω = 1} = 0 := (measureReal_eq_zero_iff (μ := P) (s := {ω | X i ω = 1})).mp hp
    have hne : ∀ᵐ ω ∂P, X i ω ≠ 1 := by
      rw [ae_iff]
      simpa using hz
    filter_upwards [hne, hX.2.2 i] with ω h1 h2
    omega
  have hW : ∀ᵐ ω ∂P, W n X ω = 0 := by
    have := (Filter.eventually_all_finset _).mpr hXi
    filter_upwards [this] with ω hω
    simp only [W]
    exact Finset.sum_eq_zero hω
  have hI : ∫ ω, h (W n X ω) ∂P = h 0 := by
    rw [integral_congr_ae (hW.mono fun ω hω => by simp only [hω] : (fun ω => h (W n X ω)) =ᵐ[P] fun _ => h 0)]
    simp
  have hP : poissonExp 0 h = h 0 := by
    rw [poissonExp, tsum_eq_single 0]
    · simp
    · intro b hb
      simp [zero_pow hb]
  rw [hI, hl, hP, sub_self]

end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

open MeasureTheory ProbabilityTheory PoissonDepTrials.MixSqrt in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (φ : ℕ → ℝ)
    (hφ : IbragimovMixing P X φ) (m : ℕ) (h : ℕ → ℝ) (hh : ∀ k, |h k| ≤ 1) :
    |∫ ω, h (W n X ω) ∂P - poissonExp (lam P n X) h|
      ≤ 6 * min (1 / Real.sqrt (lam P n X)) 1 * (Var[fun ω => (W n X ω : ℝ); P] - lam P n X
        + 2 * (2 * m + 1) * ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 + 4 * (lam P n X + 1) * n * φ (m + 1)) := by
  rcases (show 0 ≤ lam P n X from Finset.sum_nonneg fun i _ => prob_nonneg P X i).eq_or_lt
    with h0 | hpos
  · rw [main_zero P n X hX h h0.symm, abs_zero, ← h0]
    simp
  · exact main_pos P n X hX φ hφ m h hh hpos

end
