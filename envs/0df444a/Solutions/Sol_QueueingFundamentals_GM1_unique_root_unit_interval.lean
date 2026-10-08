-- Prove2me | solution 1 for QueueingFundamentals.GM1.unique_root_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:04:05.543034+00:00
-- url     : https://prove2.me/submissions/c5bf5454-cba3-4089-ae80-7b686fdecbb8

import Mathlib
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain



namespace QueueingFundamentals.GM1

open MeasureTheory

noncomputable def gmK (mu : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-mu * t) * (mu * t) ^ n / (Nat.factorial n : ℝ)

lemma gm_exp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

lemma gmK_hasSum (mu t : ℝ) : HasSum (fun n => gmK mu n t) 1 := by
  have := (gm_exp_hasSum (mu * t)).mul_left (Real.exp (-mu * t))
  rw [← Real.exp_add, show -mu * t + mu * t = 0 by ring, Real.exp_zero] at this
  have e : (fun n => gmK mu n t) = fun i => Real.exp (-mu * t) * ((mu * t) ^ i / ↑i.factorial) := by
    funext n; simp [gmK, mul_div_assoc]
  rw [e]; exact this

lemma gmK_nat_hasSum (mu t : ℝ) : HasSum (fun n : ℕ => (n : ℝ) * gmK mu n t) (mu * t) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  have := (gmK_hasSum mu t).mul_left (mu * t)
  rw [mul_one] at this
  have e : (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * gmK mu (n + 1) t) = fun i => mu * t * gmK mu i t := by
    funext n
    simp only [gmK, Nat.factorial_succ, Nat.cast_mul, pow_succ]; push_cast
    field_simp
  rw [e]; exact this

lemma gmK_nonneg (mu : ℝ) (hmu : 0 < mu) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gmK mu n t := by
  unfold gmK; have : 0 ≤ mu * t := mul_nonneg hmu.le ht; positivity

lemma gmK_le_one (mu : ℝ) (hmu : 0 < mu) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : gmK mu n t ≤ 1 :=
  le_hasSum (gmK_hasSum mu t) n fun m _ => gmK_nonneg mu hmu m ht

lemma gmK_cont (mu : ℝ) (n : ℕ) : Continuous (gmK mu n) := by
  unfold gmK; fun_prop

lemma ae_nonneg_of (A : Measure ℝ) (lam : ℝ) (hA : IsInterarrivalLaw A lam) :
    ∀ᵐ t ∂A, 0 ≤ t := by
  have h := measure_eq_zero_iff_ae_notMem.mp hA.nonneg
  filter_upwards [h] with t ht; simpa using ht

lemma restrict_eq (A : Measure ℝ) (lam : ℝ) (hA : IsInterarrivalLaw A lam) :
    A.restrict (Set.Ici 0) = A :=
  Measure.restrict_eq_self_of_ae_mem (by filter_upwards [ae_nonneg_of A lam hA] with t ht using ht)

lemma serviceProb_eq (A : Measure ℝ) (lam mu : ℝ) (hA : IsInterarrivalLaw A lam) (n : ℕ) :
    serviceProb A mu n = ∫ t, gmK mu n t ∂A := by
  unfold serviceProb; rw [restrict_eq A lam hA]; rfl

lemma gmK_integrable (A : Measure ℝ) (lam mu : ℝ) (hmu : 0 < mu) (hA : IsInterarrivalLaw A lam)
    (n : ℕ) : Integrable (gmK mu n) A := by
  have := hA.isProbability
  refine Integrable.mono' (integrable_const (1 : ℝ)) (gmK_cont mu n).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of A lam hA] with t ht
  rw [Real.norm_of_nonneg (gmK_nonneg mu hmu n ht)]; exact gmK_le_one mu hmu n ht

lemma b_nonneg (A : Measure ℝ) (lam mu : ℝ) (hmu : 0 < mu) (hA : IsInterarrivalLaw A lam) (n : ℕ) :
    0 ≤ serviceProb A mu n := by
  rw [serviceProb_eq A lam mu hA]
  exact integral_nonneg_of_ae (by filter_upwards [ae_nonneg_of A lam hA] with t ht using gmK_nonneg mu hmu n ht)

lemma b_hasSum (A : Measure ℝ) (lam mu : ℝ) (hmu : 0 < mu) (hA : IsInterarrivalLaw A lam) :
    HasSum (fun n => serviceProb A mu n) 1 := by
  have := hA.isProbability
  simp_rw [serviceProb_eq A lam mu hA]
  have h := hasSum_integral_of_dominated_convergence (μ := A) (F := fun n t => gmK mu n t)
    (f := fun _ => (1 : ℝ)) (fun n t => gmK mu n t)
    (fun n => (gmK_cont mu n).aestronglyMeasurable)
    (fun n => by filter_upwards [ae_nonneg_of A lam hA] with t ht
                 rw [Real.norm_of_nonneg (gmK_nonneg mu hmu n ht)])
    (Filter.Eventually.of_forall fun t => (gmK_hasSum mu t).summable)
    (by simp_rw [(gmK_hasSum mu _).tsum_eq]; exact integrable_const _)
    (Filter.Eventually.of_forall fun t => gmK_hasSum mu t)
  simpa using h

lemma nb_hasSum (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) :
    HasSum (fun n : ℕ => (n : ℝ) * serviceProb A mu n) (mu / lam) := by
  simp_rw [serviceProb_eq A lam mu hA, ← integral_const_mul]
  have hint : Integrable (fun t => mu * t) A := hA.integrable.const_mul mu
  have h := hasSum_integral_of_dominated_convergence (μ := A)
    (F := fun (n : ℕ) t => (n : ℝ) * gmK mu n t)
    (f := fun t => mu * t) (fun (n : ℕ) t => (n : ℝ) * gmK mu n t)
    (fun n => ((gmK_cont mu n).const_smul (n : ℝ)).aestronglyMeasurable)
    (fun n => by filter_upwards [ae_nonneg_of A lam hA] with t ht
                 rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (gmK_nonneg mu hmu n ht))])
    (Filter.Eventually.of_forall fun t => (gmK_nat_hasSum mu t).summable)
    (by simp_rw [(gmK_nat_hasSum mu _).tsum_eq]; exact hint)
    (Filter.Eventually.of_forall fun t => gmK_nat_hasSum mu t)
  have e : ∫ a, mu * a ∂A = mu / lam := by rw [integral_const_mul, hA.mean]; field_simp
  rw [e] at h; exact h

lemma b_pos (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (n : ℕ) : 0 < serviceProb A mu n := by
  have := hA.isProbability
  rw [serviceProb_eq A lam mu hA]
  have hpos : 0 < A (Set.Ioi 0) := by
    by_contra hc
    have h0 : A (Set.Ioi 0) = 0 := by simpa using hc
    have hae : (fun t : ℝ => t) =ᵐ[A] 0 := by
      have h1 : ∀ᵐ t ∂A, t ∉ Set.Ioi (0:ℝ) := measure_eq_zero_iff_ae_notMem.mp h0
      filter_upwards [h1, ae_nonneg_of A lam hA] with t h1 h2
      simp only [Set.mem_Ioi, not_lt] at h1; simp; linarith
    have := hA.mean
    rw [integral_congr_ae hae] at this
    simp at this; exact absurd this.symm (by positivity)
  rw [integral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_nonneg_of A lam hA] with t ht using gmK_nonneg mu hmu n ht)
    (gmK_integrable A lam mu hmu hA n)]
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  intro t ht
  simp only [Set.mem_Ioi] at ht
  simp only [Function.mem_support, gmK]
  have : 0 < mu * t := mul_pos hmu ht
  positivity

lemma S_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range n, x ^ k :=
  Finset.sum_nonneg fun k _ => pow_nonneg hx k

lemma S_le {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (n : ℕ) : ∑ k ∈ Finset.range n, x ^ k ≤ n := by
  calc ∑ k ∈ Finset.range n, x ^ k ≤ ∑ k ∈ Finset.range n, (1:ℝ) :=
        Finset.sum_le_sum fun k _ => pow_le_one₀ hx.1 hx.2
    _ = n := by simp

set_option linter.unusedSectionVars false
section PartB
variable (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hA : IsInterarrivalLaw A lam)
include hlam hmu hA

noncomputable def br (A : Measure ℝ) (mu x : ℝ) : ℝ := ∑' n : ℕ, serviceProb A mu n * x ^ n

noncomputable def gG (A : Measure ℝ) (mu x : ℝ) : ℝ :=
  ∑' n : ℕ, serviceProb A mu n * ∑ k ∈ Finset.range n, x ^ k

omit hlam hmu hA in
lemma beta_ofReal (x : ℝ) : beta A mu (x : ℂ) = (br A mu x : ℂ) := by
  unfold beta br; rw [Complex.ofReal_tsum]; push_cast; rfl

lemma br_summable {x : ℝ} (hx : |x| ≤ 1) : Summable fun n : ℕ => serviceProb A mu n * x ^ n := by
  refine Summable.of_norm_bounded (b_hasSum A lam mu hmu hA).summable fun n => ?_
  rw [norm_mul, Real.norm_of_nonneg (b_nonneg A lam mu hmu hA n), norm_pow, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (b_nonneg A lam mu hmu hA n) (pow_le_one₀ (abs_nonneg _) hx)

lemma bc_summable {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => (serviceProb A mu n : ℂ) * z ^ n := by
  refine Summable.of_norm_bounded (b_hasSum A lam mu hmu hA).summable fun n => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b_nonneg A lam mu hmu hA n), norm_pow]
  exact mul_le_of_le_one_right (b_nonneg A lam mu hmu hA n) (pow_le_one₀ (norm_nonneg _) hz)

lemma gG_summable {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    Summable fun n : ℕ => serviceProb A mu n * ∑ k ∈ Finset.range n, x ^ k := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (b_nonneg A lam mu hmu hA n) (S_nonneg hx.1 n))
    (fun n => ?_) (nb_hasSum A lam mu hlam hmu hA).summable
  rw [mul_comm (n:ℝ)]
  exact mul_le_mul_of_nonneg_left (S_le hx n) (b_nonneg A lam mu hmu hA n)

lemma key_identity {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : 1 - br A mu x = (1 - x) * gG A mu x := by
  have h1 := (b_hasSum A lam mu hmu hA).sub
    (br_summable A lam mu hlam hmu hA (x := x) (by rw [abs_of_nonneg hx.1]; exact hx.2)).hasSum
  have h2 := (gG_summable A lam mu hlam hmu hA hx).hasSum.mul_left (1 - x)
  refine h1.unique ?_
  have e : (fun n => (1 - x) * (serviceProb A mu n * ∑ k ∈ Finset.range n, x ^ k)) =
      fun n => serviceProb A mu n - serviceProb A mu n * x ^ n := by
    funext n
    have := geom_sum_mul x n
    linear_combination (-serviceProb A mu n) * this
  rw [e] at h2; exact h2

lemma gG_lt {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : x < y) :
    gG A mu x < gG A mu y := by
  unfold gG
  refine Summable.tsum_lt_tsum_of_nonneg (i := 2)
    (fun n => mul_nonneg (b_nonneg A lam mu hmu hA n) (S_nonneg hx.1 n)) (fun n => ?_) ?_
    (gG_summable A lam mu hlam hmu hA hy)
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (b_nonneg A lam mu hmu hA n)
    exact pow_le_pow_left₀ hx.1 hxy.le k
  · refine mul_lt_mul_of_pos_left ?_ (b_pos A lam mu hlam hmu hA 2)
    simp [Finset.sum_range_succ]; exact hxy

lemma gG_le_of_le {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : x ≤ y) :
    gG A mu x ≤ gG A mu y := by
  rcases hxy.lt_or_eq with h | h
  · exact (gG_lt A lam mu hlam hmu hA hx hy h).le
  · rw [h]

lemma gG_one : gG A mu 1 = mu / lam := by
  unfold gG
  rw [← (nb_hasSum A lam mu hlam hmu hA).tsum_eq]
  congr 1; funext n; simp [mul_comm]

omit hlam hmu hA in
lemma br_zero (A : Measure ℝ) (mu : ℝ) : br A mu 0 = serviceProb A mu 0 := by
  unfold br; rw [tsum_eq_single 0]; · simp
  intro n hn; simp [zero_pow hn]

lemma gG_zero_lt : gG A mu 0 < 1 := by
  have := key_identity A lam mu hlam hmu hA (x := 0) ⟨le_rfl, zero_le_one⟩
  rw [br_zero A mu] at this
  have := b_pos A lam mu hlam hmu hA 0
  linarith

lemma gG_cont : ContinuousOn (gG A mu) (Set.Icc 0 1) := by
  unfold gG
  refine continuousOn_tsum (fun n => by fun_prop) (nb_hasSum A lam mu hlam hmu hA).summable ?_
  intro n x hx
  rw [Real.norm_of_nonneg (mul_nonneg (b_nonneg A lam mu hmu hA n) (S_nonneg hx.1 n)), mul_comm (n:ℝ)]
  exact mul_le_mul_of_nonneg_left (S_le hx n) (b_nonneg A lam mu hmu hA n)

lemma root_iff {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) : br A mu x = x ↔ gG A mu x = 1 := by
  have := key_identity A lam mu hlam hmu hA (x := x) ⟨hx.1, hx.2.le⟩
  have h1 : 0 < 1 - x := by linarith [hx.2]
  constructor
  · intro h; rw [h] at this; field_simp at this ⊢; nlinarith
  · intro h; rw [h] at this; linarith

lemma ge_iff {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) : x ≤ br A mu x ↔ gG A mu x ≤ 1 := by
  have := key_identity A lam mu hlam hmu hA (x := x) ⟨hx.1, hx.2.le⟩
  have h1 : 0 < 1 - x := by linarith [hx.2]
  constructor
  · intro h; by_contra hc; push_neg at hc; nlinarith
  · intro h; nlinarith

lemma root_unique {r s : ℝ} (hr : r ∈ Set.Ico (0:ℝ) 1) (hs : s ∈ Set.Ico (0:ℝ) 1)
    (hr' : br A mu r = r) (hs' : br A mu s = s) : r = s := by
  rw [root_iff A lam mu hlam hmu hA hr] at hr'
  rw [root_iff A lam mu hlam hmu hA hs] at hs'
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · linarith [gG_lt A lam mu hlam hmu hA ⟨hr.1, hr.2.le⟩ ⟨hs.1, hs.2.le⟩ h]
  · linarith [gG_lt A lam mu hlam hmu hA ⟨hs.1, hs.2.le⟩ ⟨hr.1, hr.2.le⟩ h]

lemma root_exists_iff : (∃ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ br A mu r = r) ↔ lam / mu < 1 := by
  constructor
  · rintro ⟨r, hr, hr'⟩
    rw [root_iff A lam mu hlam hmu hA ⟨hr.1.le, hr.2⟩] at hr'
    have := gG_lt A lam mu hlam hmu hA ⟨hr.1.le, hr.2.le⟩ ⟨zero_le_one, le_rfl⟩ hr.2
    rw [gG_one A lam mu hlam hmu hA, hr'] at this
    rw [div_lt_one hmu]; rw [lt_div_iff₀ hlam] at this; linarith
  · intro h
    have h1 : 1 < gG A mu 1 := by
      rw [gG_one A lam mu hlam hmu hA, lt_div_iff₀ hlam]; rw [div_lt_one hmu] at h; linarith
    obtain ⟨c, hc, hc1⟩ := intermediate_value_Icc zero_le_one (gG_cont A lam mu hlam hmu hA)
      ⟨(gG_zero_lt A lam mu hlam hmu hA).le, h1.le⟩
    have hc0 : c ≠ 0 := by rintro rfl; linarith [gG_zero_lt A lam mu hlam hmu hA]
    have hc1' : c ≠ 1 := by rintro rfl; linarith
    have hcI : c ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hc.1 (Ne.symm hc0), lt_of_le_of_ne hc.2 hc1'⟩
    exact ⟨c, hcI, (root_iff A lam mu hlam hmu hA ⟨hcI.1.le, hcI.2⟩).mpr hc1⟩

theorem unique_root_unit_interval_core :
    (∀ r s : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (r : ℂ) = (r : ℂ) →
        s ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (s : ℂ) = (s : ℂ) → r = s) ∧
      ((∃ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r : ℂ) = (r : ℂ)) ↔ lam / mu < 1) := by
  simp only [beta_ofReal, Complex.ofReal_inj]
  exact ⟨fun r s hr hr' hs hs' => root_unique A lam mu hlam hmu hA ⟨hr.1.le, hr.2⟩ ⟨hs.1.le, hs.2⟩ hr' hs',
    root_exists_iff A lam mu hlam hmu hA⟩

end PartB

end QueueingFundamentals.GM1

open QueueingFundamentals.GM1
open QueueingFundamentals.GM1 MeasureTheory

theorem solution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) :
    (∀ r s : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (r : ℂ) = (r : ℂ) →
        s ∈ Set.Ioo (0 : ℝ) 1 → beta A mu (s : ℂ) = (s : ℂ) → r = s) ∧
      ((∃ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r : ℂ) = (r : ℂ)) ↔ lam / mu < 1) := by
  exact unique_root_unit_interval_core A lam mu hlam hmu hA
