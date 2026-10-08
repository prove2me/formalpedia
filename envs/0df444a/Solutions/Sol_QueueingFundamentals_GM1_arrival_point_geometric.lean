-- Prove2me | solution 1 for QueueingFundamentals.GM1.arrival_point_geometric
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:18:25.280167+00:00
-- url     : https://prove2.me/submissions/4a6c0d31-23d7-4020-8654-6e2196e37aa3

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

lemma re_eq_norm_imp {z : ℂ} (h : z.re = ‖z‖) : z = ((‖z‖ : ℝ) : ℂ) := by
  have h2 := Complex.re_eq_norm.mp h
  rw [Complex.nonneg_iff] at h2
  apply Complex.ext <;> simp [h, h2.2.symm]

lemma disk_root_eq (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0:ℝ) 1) (hroot : br A mu r0 = r0)
    (z : ℂ) (hz : ‖z‖ < 1) (hzr : beta A mu z = z) : z = (r0 : ℂ) := by
  set a := ‖z‖ with ha_def
  have ha0 : 0 ≤ a := norm_nonneg z
  have hbeta : HasSum (fun n => (serviceProb A mu n : ℂ) * z ^ n) z := by
    have := (bc_summable A lam mu hlam hmu hA hz.le).hasSum
    unfold beta at hzr; rwa [hzr] at this
  have hbr_a : HasSum (fun n : ℕ => serviceProb A mu n * a ^ n) (br A mu a) :=
    (br_summable A lam mu hlam hmu hA (x := a) (by rw [abs_of_nonneg ha0]; exact hz.le)).hasSum
  have hnorm : a ≤ br A mu a := by
    have h1 : ‖z‖ ≤ ∑' n, ‖(serviceProb A mu n : ℂ) * z ^ n‖ := by
      conv_lhs => rw [← hbeta.tsum_eq]
      refine norm_tsum_le_tsum_norm ?_
      refine hbr_a.summable.congr fun n => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b_nonneg A lam mu hmu hA n), norm_pow]
    refine h1.trans (le_of_eq ?_)
    unfold br; congr 1; funext n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b_nonneg A lam mu hmu hA n), norm_pow]
  have haI : a ∈ Set.Ico (0:ℝ) 1 := ⟨ha0, hz⟩
  have hr0I : r0 ∈ Set.Icc (0:ℝ) 1 := ⟨hr0.1.le, hr0.2.le⟩
  have hGr0 : gG A mu r0 = 1 := (root_iff A lam mu hlam hmu hA ⟨hr0.1.le, hr0.2⟩).mp hroot
  have ha_le : a ≤ r0 := by
    by_contra hc; push_neg at hc
    have h1 := (ge_iff A lam mu hlam hmu hA haI).mp hnorm
    have h2 := gG_lt A lam mu hlam hmu hA hr0I ⟨ha0, hz.le⟩ hc
    linarith
  have hre : z.re = a := by
    rcases ha_le.lt_or_eq with hlt | heq
    · -- a < r0
      have hzc : z ≠ (r0 : ℂ) := by
        intro h; rw [h] at ha_def; simp [abs_of_pos hr0.1] at ha_def; linarith
      have hc : HasSum (fun n => (serviceProb A mu n : ℂ) * (r0 : ℂ) ^ n) (r0 : ℂ) := by
        have := (bc_summable A lam mu hlam hmu hA (z := (r0:ℂ))
          (by simp [abs_of_pos hr0.1]; exact hr0.2.le)).hasSum
        have e := beta_ofReal A mu r0
        rw [hroot] at e; unfold beta at e; rwa [e] at this
      have hw := ((hbeta.sub hc).div_const (z - (r0:ℂ)))
      rw [div_self (sub_ne_zero.mpr hzc)] at hw
      set w : ℕ → ℂ := fun n => (serviceProb A mu n : ℂ) *
        ∑ k ∈ Finset.range n, z ^ k * (r0:ℂ) ^ (n - 1 - k) with hw_def
      have hw' : HasSum w 1 := by
        have e : w = fun i => (↑(serviceProb A mu i) * z ^ i - ↑(serviceProb A mu i) * ↑r0 ^ i) / (z - ↑r0) := by
          funext n
          rw [hw_def]; dsimp only
          rw [eq_div_iff (sub_ne_zero.mpr hzc), mul_assoc, geom_sum₂_mul]; ring
        rw [e]; exact hw
      have hbr0 : HasSum (fun n : ℕ => serviceProb A mu n * r0 ^ n) r0 := by
        have := (br_summable A lam mu hlam hmu hA (x := r0) (by rw [abs_of_pos hr0.1]; exact hr0.2.le)).hasSum
        unfold br at hroot; rwa [hroot] at this
      have hv := (hbr0.sub hbr_a).div_const (r0 - a)
      set v : ℕ → ℝ := fun n => serviceProb A mu n *
        ∑ k ∈ Finset.range n, a ^ k * r0 ^ (n - 1 - k) with hv_def
      have hra : r0 - a ≠ 0 := by linarith
      have hv' : HasSum v ((r0 - br A mu a) / (r0 - a)) := by
        have e : v = fun i => (serviceProb A mu i * r0 ^ i - serviceProb A mu i * a ^ i) / (r0 - a) := by
          funext n
          rw [hv_def]; dsimp only
          rw [eq_div_iff hra, mul_assoc, show r0 - a = -(a - r0) by ring, mul_neg, geom_sum₂_mul]; ring
        rw [e]; exact hv
      have hD : (r0 - br A mu a) / (r0 - a) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      have hu := hv'.sub (Complex.hasSum_re hw')
      have hun : ∀ n, 0 ≤ v n - (w n).re := by
        intro n
        rw [sub_nonneg]
        refine (Complex.re_le_norm _).trans ?_
        rw [hw_def, hv_def]; dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (b_nonneg A lam mu hmu hA n)]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) (b_nonneg A lam mu hmu hA n)
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.1.le]
      have h2 := le_hasSum hu 2 (fun m _ => hun m)
      have h2' : v 2 - (w 2).re = 0 := by
        have := hun 2; simp only [Complex.one_re] at h2; linarith
      rw [hw_def, hv_def] at h2'
      simp [Finset.sum_range_succ] at h2'
      have hb2 := b_pos A lam mu hlam hmu hA 2
      have : serviceProb A mu 2 * (r0 + a - (r0 + z.re)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    · -- a = r0
      have hbra : br A mu a = a := by rw [heq]; exact hroot
      set t : ℕ → ℝ := fun n => a * (serviceProb A mu n * a ^ n) -
        ((starRingEnd ℂ) z * ((serviceProb A mu n : ℂ) * z ^ n)).re with ht_def
      have hs := (hbr_a.mul_left a).sub (Complex.hasSum_re (hbeta.mul_left ((starRingEnd ℂ) z)))
      rw [Complex.conj_mul', hbra] at hs
      have hs' : HasSum t 0 := by
        have e : a * a - ((‖z‖ : ℂ) ^ 2).re = 0 := by
          rw [← ha_def, ← Complex.ofReal_pow, Complex.ofReal_re]; ring
        rw [e] at hs; exact hs
      have htn : ∀ n, 0 ≤ t n := by
        intro n; rw [ht_def]; dsimp only; rw [sub_nonneg]
        refine (Complex.re_le_norm _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (b_nonneg A lam mu hmu hA n), norm_pow]
      have h0 := le_hasSum hs' 0 (fun m _ => htn m)
      have h0' : t 0 = 0 := le_antisymm h0 (htn 0)
      rw [ht_def] at h0'; simp at h0'
      have hb0 := b_pos A lam mu hlam hmu hA 0
      have : serviceProb A mu 0 * (a - z.re) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
  have hz_eq := re_eq_norm_imp A lam mu hlam hmu hA (z := z) hre
  rw [← ha_def] at hz_eq
  have hbra : br A mu a = a := by
    have e := beta_ofReal A mu a
    rw [← hz_eq, hzr] at e
    nth_rewrite 1 [hz_eq] at e
    exact_mod_cast e.symm
  have := root_unique A lam mu hlam hmu hA haI ⟨hr0.1.le, hr0.2⟩ hbra hroot
  rw [hz_eq, this]

theorem unique_root_unit_disk_core (hrho : lam / mu < 1) :
    ∃! z : ℂ, ‖z‖ < 1 ∧ beta A mu z = z := by
  obtain ⟨r0, hr0, hroot⟩ := (root_exists_iff A lam mu hlam hmu hA).mpr hrho
  refine ⟨(r0 : ℂ), ⟨?_, ?_⟩, ?_⟩
  · simp [abs_of_pos hr0.1]; exact hr0.2
  · rw [beta_ofReal, hroot]
  · rintro z ⟨hz, hzr⟩
    exact disk_root_eq A lam mu hlam hmu hA r0 hr0 hroot z hz hzr

lemma p_nonneg (i j : ℕ) : 0 ≤ transitionProb A mu i j := by
  unfold transitionProb
  split_ifs
  · have := sum_le_hasSum (Finset.range (i + 1)) (fun k _ => b_nonneg A lam mu hmu hA k)
      (b_hasSum A lam mu hmu hA)
    linarith
  · exact b_nonneg A lam mu hmu hA _
  · exact le_rfl

lemma p_row (i : ℕ) : HasSum (fun j => transitionProb A mu i j) 1 := by
  have h : HasSum (fun j => transitionProb A mu i j)
      (∑ j ∈ Finset.range (i + 2), transitionProb A mu i j) :=
    hasSum_sum_of_ne_finset_zero (by
      intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      unfold transitionProb
      rw [if_neg (by omega), if_neg (by omega)])
  have hs : ∑ j ∈ Finset.range (i + 2), transitionProb A mu i j = 1 := by
    rw [Finset.sum_range_succ']
    have e : ∑ k ∈ Finset.range (i + 1), transitionProb A mu i (k + 1) =
        ∑ k ∈ Finset.range (i + 1), serviceProb A mu k := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      unfold transitionProb
      rw [if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    rw [e]; unfold transitionProb; simp
  rw [hs] at h; exact h

lemma p_col (i k : ℕ) : transitionProb A mu (i + k) (k + 1) = serviceProb A mu i := by
  unfold transitionProb; rw [if_neg (by omega), if_pos (by omega)]; congr 1; omega

lemma p_col_zero (i k : ℕ) (h : i < k) : transitionProb A mu i (k + 1) = 0 := by
  unfold transitionProb; rw [if_neg (by omega), if_neg (by omega)]

lemma interchange (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) {s : ℝ} (hqs : HasSum q s) :
    (∀ j, Summable fun i => q i * transitionProb A mu i j) ∧
      HasSum (fun j => ∑' i, q i * transitionProb A mu i j) s := by
  set f : ℕ × ℕ → ℝ := fun x => q x.1 * transitionProb A mu x.1 x.2 with hf_def
  have hf0 : 0 ≤ f := fun x => mul_nonneg (hq0 _) (p_nonneg A lam mu hlam hmu hA _ _)
  have hrow : ∀ i, HasSum (fun j => f (i, j)) (q i) := fun i => by
    have := (p_row A lam mu hlam hmu hA i).mul_left (q i); rw [mul_one] at this; exact this
  have hf : Summable f := by
    refine (summable_prod_of_nonneg hf0).mpr ⟨fun i => (hrow i).summable, ?_⟩
    simp_rw [(hrow _).tsum_eq]; exact hqs.summable
  have hfs : HasSum f s := by
    have := hf.hasSum
    rwa [hf.tsum_prod' (fun i => (hrow i).summable), tsum_congr (fun i => (hrow i).tsum_eq),
      hqs.tsum_eq] at this
  have hg : HasSum (f ∘ Prod.swap) s := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hfs
  have hcol : ∀ j, Summable fun i => (f ∘ Prod.swap) (j, i) := fun j => hg.summable.prod_factor j
  exact ⟨hcol, hg.prod_fiberwise fun j => (hcol j).hasSum⟩

lemma terms_zero {f : ℕ → ℝ} (h0 : ∀ n, 0 ≤ f n) (hs : HasSum f 0) (n : ℕ) : f n = 0 :=
  le_antisymm (le_hasSum hs n fun m _ => h0 m) (h0 n)

lemma geom_stationary (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0:ℝ) 1) (hroot : br A mu r0 = r0) :
    IsArrivalPointStationary A mu (fun n => (1 - r0) * r0 ^ n) := by
  set q : ℕ → ℝ := fun n => (1 - r0) * r0 ^ n with hq_def
  have hq0 : ∀ n, 0 ≤ q n := fun n => mul_nonneg (by linarith [hr0.2]) (pow_nonneg hr0.1.le n)
  have hqs : HasSum q 1 := by
    have := (hasSum_geometric_of_lt_one hr0.1.le hr0.2).mul_left (1 - r0)
    rwa [mul_inv_cancel₀ (by linarith [hr0.2])] at this
  have hbr0 : HasSum (fun n : ℕ => serviceProb A mu n * r0 ^ n) r0 := by
    have := (br_summable A lam mu hlam hmu hA (x := r0) (by rw [abs_of_pos hr0.1]; exact hr0.2.le)).hasSum
    unfold br at hroot; rwa [hroot] at this
  have hsucc : ∀ k, HasSum (fun i => q i * transitionProb A mu i (k + 1)) (q (k + 1)) := by
    intro k
    rw [← hasSum_nat_add_iff' k]
    have e0 : ∑ i ∈ Finset.range k, q i * transitionProb A mu i (k + 1) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [p_col_zero A lam mu hlam hmu hA i k (Finset.mem_range.mp hi), mul_zero]
    rw [e0, sub_zero]
    have := hbr0.mul_left ((1 - r0) * r0 ^ k)
    have e : (fun i => q (i + k) * transitionProb A mu (i + k) (k + 1)) =
        fun i => (1 - r0) * r0 ^ k * (serviceProb A mu i * r0 ^ i) := by
      funext i; rw [p_col A lam mu hlam hmu hA, hq_def]; dsimp only; ring
    have e2 : q (k + 1) = (1 - r0) * r0 ^ k * r0 := by rw [hq_def]; dsimp only; ring
    rw [e, e2]; exact this
  refine ⟨hq0, hqs, ?_⟩
  intro j
  rcases j with _ | k
  · obtain ⟨hcol, hT⟩ := interchange A lam mu hlam hmu hA q hq0 hqs
    have h1 := (hasSum_nat_add_iff' 1).mpr hT
    have h2 := (hasSum_nat_add_iff' 1).mpr hqs
    simp only [Finset.range_one, Finset.sum_singleton] at h1 h2
    have e : (fun k => ∑' i, q i * transitionProb A mu i (k + 1)) = fun k => q (k + 1) := by
      funext k; exact (hsucc k).tsum_eq
    rw [e] at h1
    have := h1.unique h2
    have hT0 : ∑' i, q i * transitionProb A mu i 0 = q 0 := by linarith
    rw [← hT0]; exact (hcol 0).hasSum
  · exact hsucc k

lemma stationary_unique (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0:ℝ) 1) (hroot : br A mu r0 = r0)
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) : q = fun n => (1 - r0) * r0 ^ n := by
  obtain ⟨hq0, hqs, hqj⟩ := hq
  obtain ⟨hg0, hgs, hgj⟩ := geom_stationary A lam mu hlam hmu hA r0 hr0 hroot
  set g : ℕ → ℝ := fun n => (1 - r0) * r0 ^ n with hg_def
  set d : ℕ → ℝ := fun n => q n - g n with hd_def
  have hd : ∀ j, HasSum (fun i => d i * transitionProb A mu i j) (d j) := by
    intro j
    have h := (hqj j).sub (hgj j)
    have e : (fun i => q i * transitionProb A mu i j - g i * transitionProb A mu i j) =
        fun i => d i * transitionProb A mu i j := by funext i; rw [hd_def]; ring
    rw [e] at h; exact h
  have hds : HasSum d 0 := by have h := hqs.sub hgs; rw [sub_self] at h; exact h
  set u : ℕ → ℝ := fun n => |d n| with hu_def
  have hu0 : ∀ n, 0 ≤ u n := fun n => abs_nonneg _
  have hus : Summable u := hds.summable.abs
  obtain ⟨hucol, huT⟩ := interchange A lam mu hlam hmu hA u hu0 hus.hasSum
  have hle : ∀ j, u j ≤ ∑' i, u i * transitionProb A mu i j := by
    intro j
    have hn : Summable fun i => ‖d i * transitionProb A mu i j‖ :=
      (hucol j).congr fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p_nonneg A lam mu hlam hmu hA i j)]
    calc u j = ‖∑' i, d i * transitionProb A mu i j‖ := by
            rw [(hd j).tsum_eq, Real.norm_eq_abs]
      _ ≤ ∑' i, ‖d i * transitionProb A mu i j‖ := norm_tsum_le_tsum_norm hn
      _ = ∑' i, u i * transitionProb A mu i j := by
            congr 1; funext i
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p_nonneg A lam mu hlam hmu hA i j)]
  have hdiff := huT.sub hus.hasSum
  rw [sub_self] at hdiff
  have h1 : ∑' i, u i * transitionProb A mu i 1 = u 1 := by
    have := terms_zero A lam mu hlam hmu hA (f := fun j => ∑' i, u i * transitionProb A mu i j - u j)
      (fun j => sub_nonneg.mpr (hle j)) hdiff 1
    linarith
  have p1 : ∀ i, transitionProb A mu i 1 = serviceProb A mu i := fun i => by
    have := p_col A lam mu hlam hmu hA i 0; simpa using this
  simp_rw [p1] at h1
  have hd1 : HasSum (fun i => d i * serviceProb A mu i) (d 1) := by
    have := hd 1; simp_rw [p1] at this; exact this
  have hu1 : HasSum (fun i => u i * serviceProb A mu i) (u 1) := by
    rw [← h1]; have := hucol 1; simp_rw [p1] at this; exact this.hasSum
  set σ : ℝ := if 0 ≤ d 1 then 1 else -1 with hσ
  have hσd : σ * d 1 = |d 1| := by
    rw [hσ]; split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · push_neg at h; rw [abs_of_neg h]; ring
  have hσabs : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have hw := hu1.sub (hd1.mul_left σ)
  rw [hσd] at hw
  have hw0 : HasSum (fun i => u i * serviceProb A mu i - σ * (d i * serviceProb A mu i)) 0 := by
    have : u 1 - |d 1| = 0 := by rw [hu_def]; ring
    rw [this] at hw; exact hw
  have hwn : ∀ i, 0 ≤ u i * serviceProb A mu i - σ * (d i * serviceProb A mu i) := by
    intro i
    rw [sub_nonneg, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (b_nonneg A lam mu hmu hA i)
    refine (le_abs_self _).trans (le_of_eq ?_)
    rw [abs_mul, hσabs, one_mul]
  have hσd_nonneg : ∀ i, 0 ≤ σ * d i := by
    intro i
    have h := terms_zero A lam mu hlam hmu hA hwn hw0 i
    have hb := b_pos A lam mu hlam hmu hA i
    have : (u i - σ * d i) * serviceProb A mu i = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · have : σ * d i = u i := by linarith
      rw [this]; exact hu0 i
    · linarith
  have hsd : HasSum (fun i => σ * d i) 0 := by have := hds.mul_left σ; rwa [mul_zero] at this
  funext n
  have h0 := terms_zero A lam mu hlam hmu hA hσd_nonneg hsd n
  have hσ0 : σ ≠ 0 := by intro h; rw [h] at hσabs; simp at hσabs
  have : d n = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hσ0
    · exact h
  rw [hd_def] at this; dsimp only at this; rw [hg_def] at this; linarith

theorem arrival_point_geometric_core (hrho : lam / mu < 1) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r0 : ℂ) = (r0 : ℂ) ∧
      (∀ z : ℂ, ‖z‖ < 1 → beta A mu z = z → z = (r0 : ℂ)) ∧
      IsArrivalPointStationary A mu (fun n => (1 - r0) * r0 ^ n) ∧
      ∀ q : ℕ → ℝ, IsArrivalPointStationary A mu q → q = fun n => (1 - r0) * r0 ^ n := by
  obtain ⟨r0, hr0, hroot⟩ := (root_exists_iff A lam mu hlam hmu hA).mpr hrho
  refine ⟨r0, hr0, by rw [beta_ofReal, hroot], fun z hz hzr =>
    disk_root_eq A lam mu hlam hmu hA r0 hr0 hroot z hz hzr,
    geom_stationary A lam mu hlam hmu hA r0 hr0 hroot,
    fun q hq => stationary_unique A lam mu hlam hmu hA r0 hr0 hroot q hq⟩

lemma br_of_root (r0 : ℝ) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ)) : br A mu r0 = r0 := by
  rw [beta_ofReal] at hroot; exact_mod_cast hroot

theorem arrival_point_means_core
    (r0 : ℝ) (hr0 : r0 ∈ Set.Ioo (0 : ℝ) 1) (hroot : beta A mu (r0 : ℂ) = (r0 : ℂ))
    (q : ℕ → ℝ) (hq : IsArrivalPointStationary A mu q) :
    HasSum (fun n : ℕ => (n : ℝ) * q n) (r0 / (1 - r0)) ∧
      HasSum (fun n : ℕ => (n : ℝ) * q (n + 1)) (r0 ^ 2 / (1 - r0)) := by
  have hq' := stationary_unique A lam mu hlam hmu hA r0 hr0 (br_of_root A lam mu hlam hmu hA r0 hroot) q hq
  subst hq'
  have hnorm : ‖r0‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hr0.1]; exact hr0.2
  have h := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have h1r : (1 - r0) ≠ 0 := by linarith [hr0.2]
  constructor
  · have := h.mul_left (1 - r0)
    have e : (1 - r0) * (r0 / (1 - r0) ^ 2) = r0 / (1 - r0) := by field_simp
    rw [e] at this
    refine this.congr_fun ?_
    intro n; ring
  · have := h.mul_left ((1 - r0) * r0)
    have e : (1 - r0) * r0 * (r0 / (1 - r0) ^ 2) = r0 ^ 2 / (1 - r0) := by field_simp
    rw [e] at this
    refine this.congr_fun ?_
    intro n; ring

end PartB

end QueueingFundamentals.GM1

open QueueingFundamentals.GM1
open QueueingFundamentals.GM1 MeasureTheory

theorem solution (A : Measure ℝ) (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hA : IsInterarrivalLaw A lam) (hrho : lam / mu < 1) :
    ∃ r0 : ℝ, r0 ∈ Set.Ioo (0 : ℝ) 1 ∧ beta A mu (r0 : ℂ) = (r0 : ℂ) ∧
      (∀ z : ℂ, ‖z‖ < 1 → beta A mu z = z → z = (r0 : ℂ)) ∧
      IsArrivalPointStationary A mu (fun n => (1 - r0) * r0 ^ n) ∧
      ∀ q : ℕ → ℝ, IsArrivalPointStationary A mu q → q = fun n => (1 - r0) * r0 ^ n := by
  exact arrival_point_geometric_core A lam mu hlam hmu hA hrho
