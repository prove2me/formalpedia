-- Prove2me | solution 1 for SkipFreeFluct.MBI.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:35:01.316564+00:00
-- url     : https://prove2.me/submissions/c3612f21-ec83-4337-a3a4-e81398b75b81

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
open scoped ENNReal Topology
open Filter MeasureTheory

namespace L51
open SkipFreeFluct.MBI PowerSeries Finset

noncomputable def ev (f : PowerSeries ℝ) (s : ℝ) : ℝ := ∑' n, coeff n f * s ^ n
def AS (f : PowerSeries ℝ) (s : ℝ) : Prop := Summable (fun n => ‖coeff n f * s ^ n‖)

lemma coeff_mul_pow (f g : PowerSeries ℝ) (s : ℝ) (n : ℕ) :
    coeff n (f * g) * s ^ n =
      ∑ k ∈ range (n + 1), (coeff k f * s ^ k) * (coeff (n - k) g * s ^ (n - k)) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f * coeff j g),
    Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have : s ^ n = s ^ k * s ^ (n - k) := by
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hk; omega
  rw [this]; ring

lemma ev_mul {f g : PowerSeries ℝ} {s : ℝ} (hf : AS f s) (hg : AS g s) :
    AS (f * g) s ∧ HasSum (fun n => coeff n (f * g) * s ^ n) (ev f s * ev g s) := by
  have h1 := summable_norm_sum_mul_range_of_summable_norm hf hg
  have h2 := hasSum_sum_range_mul_of_summable_norm hf hg
  simp_rw [← coeff_mul_pow] at h1 h2
  exact ⟨h1, h2⟩

lemma AS.hasSum {f : PowerSeries ℝ} {s : ℝ} (hf : AS f s) :
    HasSum (fun n => coeff n f * s ^ n) (ev f s) := hf.of_norm.hasSum

lemma AS_one (s : ℝ) : AS 1 s := by
  unfold AS
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn; simp at hn; simp [coeff_one, hn]

lemma ev_one (s : ℝ) : ev 1 s = 1 := by
  unfold ev
  rw [tsum_eq_single 0 (fun n hn => by simp [coeff_one, hn])]; simp

lemma AS_X (s : ℝ) : AS X s := by
  unfold AS
  apply summable_of_ne_finset_zero (s := {1})
  intro n hn; simp at hn; simp [coeff_X, hn]

lemma ev_X (s : ℝ) : ev X s = s := by
  unfold ev
  rw [tsum_eq_single 1 (fun n hn => by simp [coeff_X, hn])]; simp

lemma AS_add {f g : PowerSeries ℝ} {s : ℝ} (hf : AS f s) (hg : AS g s) : AS (f + g) s := by
  unfold AS at *
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hf.add hg)
  simp only [map_add, add_mul]; exact norm_add_le _ _

lemma ev_add {f g : PowerSeries ℝ} {s : ℝ} (hf : AS f s) (hg : AS g s) :
    ev (f + g) s = ev f s + ev g s := by
  have := (hf.hasSum).add (hg.hasSum)
  simp only [← add_mul, ← map_add] at this
  exact this.tsum_eq

lemma AS_C_mul {f : PowerSeries ℝ} {s : ℝ} (c : ℝ) (hf : AS f s) : AS (C c * f) s := by
  unfold AS at *
  refine (hf.mul_left ‖c‖).congr (fun n => ?_)
  simp [coeff_C_mul, mul_assoc, norm_mul]

lemma ev_C_mul {f : PowerSeries ℝ} {s : ℝ} (c : ℝ) (hf : AS f s) :
    ev (C c * f) s = c * ev f s := by
  have := (hf.hasSum).mul_left c
  simp only [← mul_assoc, ← coeff_C_mul] at this
  exact this.tsum_eq

lemma AS_neg {f : PowerSeries ℝ} {s : ℝ} (hf : AS f s) : AS (-f) s := by
  unfold AS at *; simpa using hf

lemma ev_neg {f : PowerSeries ℝ} {s : ℝ} (hf : AS f s) : ev (-f) s = - ev f s := by
  have := (hf.hasSum).neg
  simp only [← neg_mul, ← map_neg] at this
  exact this.tsum_eq

lemma AS_sub {f g : PowerSeries ℝ} {s : ℝ} (hf : AS f s) (hg : AS g s) : AS (f - g) s := by
  rw [sub_eq_add_neg]; exact AS_add hf (AS_neg hg)

lemma ev_sub {f g : PowerSeries ℝ} {s : ℝ} (hf : AS f s) (hg : AS g s) :
    ev (f - g) s = ev f s - ev g s := by
  rw [sub_eq_add_neg, ev_add hf (AS_neg hg), ev_neg hg, sub_eq_add_neg]

/-- bounded coefficients, `0 ≤ s < 1`. -/
lemma AS_of_bdd {f : PowerSeries ℝ} {s : ℝ} (B : ℝ) (hB : ∀ n, |coeff n f| ≤ B)
    (hs0 : 0 ≤ s) (hs1 : s < 1) : AS f s := by
  unfold AS
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one hs0 hs1).mul_left B)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs0]
  exact mul_le_mul_of_nonneg_right (hB n) (pow_nonneg hs0 _)

/-- partial sums of a convolution of nonneg sequences. -/
lemma conv_partial_le (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hbs : Summable b) (N : ℕ) :
    ∑ n ∈ range N, ∑ k ∈ range (n + 1), a k * b (n - k) ≤
      (∑ k ∈ range N, a k) * ∑' n, b n := by
  rw [Finset.sum_mul]
  have e : ∑ n ∈ range N, ∑ k ∈ range (n + 1), a k * b (n - k) =
      ∑ k ∈ range N, ∑ n ∈ Ico k N, a k * b (n - k) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    apply Finset.sum_bij' (fun x _ => ⟨x.2, x.1⟩) (fun x _ => ⟨x.2, x.1⟩) <;>
      simp (config := { contextual := true }) [Finset.mem_sigma] <;> omega
  rw [e]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (ha k)
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact hbs.sum_le_tsum _ (fun i _ => hb i)


section P
variable (P : MBIParams)

lemma mu_partial (hP : P.Valid) (n : ℕ) : 0 ≤ ∑ j ∈ range n, P.mu j ∧ ∑ j ∈ range n, P.mu j ≤ 1 :=
  ⟨Finset.sum_nonneg (fun j _ => hP.2.1 j), sum_le_hasSum _ (fun j _ => hP.2.1 j) hP.2.2.1⟩

lemma nu_partial (hP : P.Valid) (n : ℕ) : 0 ≤ ∑ j ∈ range n, P.nu j ∧ ∑ j ∈ range n, P.nu j ≤ 1 :=
  ⟨Finset.sum_nonneg (fun j _ => hP.2.2.2.2.2.2.2.1 j),
    sum_le_hasSum _ (fun j _ => hP.2.2.2.2.2.2.2.1 j) hP.2.2.2.2.2.2.2.2.2.1⟩

lemma muBar_bd (hP : P.Valid) (k : ℕ) : 0 ≤ muBar P k ∧ muBar P k ≤ 1 := by
  have := mu_partial P hP (k + 1); unfold muBar; constructor <;> linarith [this.1, this.2]

lemma nuBar_bd (hP : P.Valid) (k : ℕ) : 0 ≤ nuBar P k ∧ nuBar P k ≤ 1 := by
  have := nu_partial P hP (k + 1); unfold nuBar; constructor <;> linarith [this.1, this.2]

lemma dW_zero : dW P 0 = 1 / (P.alpha * P.mu 0) := by rw [dW]
lemma dW_succ (k : ℕ) : dW P (k + 1) = 1 / P.mu 0 *
      ∑ j ∈ range (k + 1), dW P j * (muBar P (k - j + 1) + P.p / P.alpha) := by
  rw [dW, Fin.sum_univ_eq_sum_range (fun j => dW P j * (muBar P (k - j + 1) + P.p / P.alpha))]

lemma piSeq_succ (k : ℕ) : piSeq P (k + 1) = 1 / ((k : ℝ) + 1) *
    ∑ j ∈ range (k + 1), piSeq P (k - j) * kappa P j := by
  rw [piSeq, Fin.sum_univ_eq_sum_range (fun j => piSeq P (k - j) * kappa P j)]

lemma varpi_succ (k : ℕ) : varpi P (k + 1) = -(1 / ((k : ℝ) + 1)) *
    ∑ j ∈ range (k + 1), varpi P (k - j) * kappa P j := by
  rw [varpi, Fin.sum_univ_eq_sum_range (fun j => varpi P (k - j) * kappa P j)]

lemma piSeq_zero : piSeq P 0 = 1 := by rw [piSeq]
lemma varpi_zero : varpi P 0 = 1 := by rw [varpi]

lemma dW_nonneg (hP : P.Valid) (k : ℕ) : 0 ≤ dW P k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [dW_zero]; have := hP.1; have := hP.2.2.2.1; positivity
    · rw [dW_succ]
      have h0 := hP.2.2.2.1
      refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun j hj => mul_nonneg
        (ih j (by simp at hj; omega)) ?_))
      have := (muBar_bd P hP (k - j + 1)).1
      have : 0 ≤ P.p / P.alpha := div_nonneg hP.2.2.2.2.2.1 hP.1.le
      linarith

lemma W_nonneg (hP : P.Valid) (k : ℕ) : 0 ≤ W P k :=
  Finset.sum_nonneg (fun j _ => dW_nonneg P hP j)

lemma kappa_nonneg (hP : P.Valid) (k : ℕ) : 0 ≤ kappa P k := by
  unfold kappa
  have hb := hP.2.2.2.2.2.2.1
  have hq := hP.2.2.2.2.2.2.2.2.2.2
  refine add_nonneg (mul_nonneg hb (Finset.sum_nonneg (fun j _ => mul_nonneg (dW_nonneg P hP _)
    (nuBar_bd P hP j).1))) (mul_nonneg hq (W_nonneg P hP k))

lemma piSeq_nonneg (hP : P.Valid) (k : ℕ) : 0 ≤ piSeq P k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [piSeq_zero]; norm_num
    · rw [piSeq_succ]
      refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun j hj => mul_nonneg
        (ih _ (by omega)) (kappa_nonneg P hP j)))

lemma varpi_abs_le (hP : P.Valid) (k : ℕ) : |varpi P k| ≤ piSeq P k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [piSeq_zero, varpi_zero]; norm_num
    · rw [piSeq_succ, varpi_succ, abs_mul, abs_neg, abs_of_pos (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
      rw [abs_mul, abs_of_nonneg (kappa_nonneg P hP j)]
      exact mul_le_mul_of_nonneg_right (ih _ (by omega)) (kappa_nonneg P hP j)

lemma muStar_cont (hP : P.Valid) :
    ContinuousOn (fun s : ℝ => ∑' j : ℕ, P.mu j * s ^ j) (Set.Icc (-1) 1) := by
  refine continuousOn_tsum (u := P.mu) (fun j => by fun_prop) hP.2.2.1.summable ?_
  intro n x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hP.2.1 n), abs_pow]
  have : |x| ≤ 1 := abs_le.2 ⟨hx.1, hx.2⟩
  calc P.mu n * |x| ^ n ≤ P.mu n * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (abs_nonneg _) this) (hP.2.1 n)
    _ = P.mu n := mul_one _

lemma nuStar_cont (hP : P.Valid) :
    ContinuousOn (fun s : ℝ => ∑' j : ℕ, P.nu j * s ^ j) (Set.Icc (-1) 1) := by
  have hn := hP.2.2.2.2.2.2.2.1
  refine continuousOn_tsum (u := P.nu) (fun j => by fun_prop) hP.2.2.2.2.2.2.2.2.2.1.summable ?_
  intro n x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn n), abs_pow]
  have : |x| ≤ 1 := abs_le.2 ⟨hx.1, hx.2⟩
  calc P.nu n * |x| ^ n ≤ P.nu n * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (abs_nonneg _) this) (hn n)
    _ = P.nu n := mul_one _

lemma psi_cont (hP : P.Valid) : ContinuousOn (psi P) (Set.Icc (-1) 1) := by
  unfold psi
  exact ((continuousOn_const.mul ((muStar_cont P hP).sub continuousOn_id)).sub
    (continuousOn_const.mul continuousOn_id))

lemma phi_cont (hP : P.Valid) : ContinuousOn (phiImm P) (Set.Icc (-1) 1) := by
  unfold phiImm
  exact (continuousOn_const.mul (continuousOn_const.sub (nuStar_cont P hP))).add continuousOn_const

lemma psi_zero (hP : P.Valid) : psi P 0 = P.alpha * P.mu 0 := by
  unfold psi
  rw [tsum_eq_single 0 (fun n hn => by simp [hn])]; simp

lemma s_props (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) : s < 1 ∧ 0 < psi P s := by
  set S := {s : ℝ | s ∈ Set.Ioc (0 : ℝ) 1 ∧ psi P s = 0}
  have hS : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : s0 P = 0 := by unfold s0; rw [show {s : ℝ | s ∈ Set.Ioc (0 : ℝ) 1 ∧ psi P s = 0} = S
      from rfl, h, Real.sInf_empty]
    linarith [hs.1, hs.2]
  have hbdd : BddBelow S := ⟨0, fun t ht => ht.1.1.le⟩
  obtain ⟨t0, ht0⟩ := hS
  have hs1 : s < 1 := lt_of_lt_of_le hs.2 ((csInf_le hbdd ht0).trans ht0.1.2)
  refine ⟨hs1, ?_⟩
  by_contra hneg
  push_neg at hneg
  have hpos0 : 0 < psi P 0 := by rw [psi_zero P hP]; exact mul_pos hP.1 hP.2.2.2.1
  have hcont : ContinuousOn (psi P) (Set.Icc 0 s) :=
    (psi_cont P hP).mono (Set.Icc_subset_Icc (by norm_num) hs1.le)
  obtain ⟨t, ht, hpt⟩ := intermediate_value_Icc' hs.1 hcont ⟨hneg, hpos0.le⟩
  have ht0' : t ≠ 0 := by rintro rfl; linarith
  have htS : t ∈ S := ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm ht0'), ht.2.trans hs1.le⟩, hpt⟩
  have := csInf_le hbdd htS
  have : s0 P ≤ t := this
  linarith [ht.2, hs.2]


noncomputable def gco (k : ℕ) : ℝ := if k = 0 then 0 else P.alpha * muBar P k + P.p

lemma I1 (hP : P.Valid) :
    PowerSeries.mk (dW P) * (C (P.alpha * P.mu 0) - PowerSeries.mk (gco P)) = 1 := by
  have ha := hP.1.ne'
  have hm := hP.2.2.2.1.ne'
  ext n
  rw [mul_sub, map_sub, coeff_mul_C, coeff_mul, coeff_one,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (PowerSeries.mk (dW P)) * coeff j (PowerSeries.mk (gco P)))]
  simp only [coeff_mk]
  rcases n with _ | k
  · simp [gco, dW_zero]; field_simp
  · rw [Finset.sum_range_succ, dW_succ]
    simp only [Nat.sub_self, gco, if_true, mul_zero, add_zero, Nat.add_one_ne_zero, if_false]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have e : k + 1 - j = k - j + 1 := by omega
    rw [if_neg (by omega), e]
    field_simp
    ring

lemma muBar_succ (k : ℕ) : muBar P (k + 1) = muBar P k - P.mu (k + 1) := by
  unfold muBar; rw [Finset.sum_range_succ _ (k + 1)]; ring

lemma nuBar_succ (k : ℕ) : nuBar P (k + 1) = nuBar P k - P.nu (k + 1) := by
  unfold nuBar; rw [Finset.sum_range_succ _ (k + 1)]; ring

lemma I2 (hP : P.Valid) :
    (1 - X : PowerSeries ℝ) * (C (P.alpha * P.mu 0) - PowerSeries.mk (gco P)) =
      C P.alpha * PowerSeries.mk P.mu - C (P.alpha + P.p) * X := by
  have hm1 := hP.2.2.2.2.1
  ext n
  simp only [sub_mul, one_mul, map_sub, coeff_C_mul, coeff_X, coeff_mk]
  rcases n with _ | n
  · simp [gco]
  rcases n with _ | n
  · rw [coeff_succ_X_mul]
    simp [gco, muBar, Finset.sum_range_succ, hm1]; ring
  · rw [coeff_succ_X_mul]
    simp only [map_sub, coeff_C, coeff_mk, gco]
    simp only [show ∀ x : ℕ, x + 1 ≠ 0 from fun x => Nat.add_one_ne_zero x, if_false,
      show n + 1 + 1 ≠ 1 by omega]
    rw [muBar_succ P (n + 1)]; ring

lemma I3 : PowerSeries.mk (W P) = PowerSeries.mk (dW P) * PowerSeries.mk (fun _ => (1 : ℝ)) := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk (dW P)) * coeff j (PowerSeries.mk (fun _ => (1 : ℝ))))]
  simp [W]

lemma I4 : (1 - X : PowerSeries ℝ) * PowerSeries.mk (fun _ => (1 : ℝ)) = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_mk, coeff_one]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul]; simp

lemma I5 (hP : P.Valid) : (1 - X : PowerSeries ℝ) * PowerSeries.mk (nuBar P) = 1 - PowerSeries.mk P.nu := by
  ext n
  rw [sub_mul, one_mul, map_sub, map_sub, coeff_mk, coeff_one, coeff_mk]
  rcases n with _ | n
  · simp [nuBar]
  · rw [coeff_succ_X_mul, coeff_mk, nuBar_succ]; simp

lemma I6 : PowerSeries.mk (kappa P) = C P.beta * (PowerSeries.mk (nuBar P) * PowerSeries.mk (dW P)) + C P.q * PowerSeries.mk (W P) := by
  ext n
  rw [map_add, coeff_C_mul, coeff_C_mul, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk (nuBar P)) * coeff j (PowerSeries.mk (dW P)))]
  simp only [coeff_mk, kappa]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma I7 : d⁄dX ℝ (PowerSeries.mk (piSeq P)) = PowerSeries.mk (kappa P) * PowerSeries.mk (piSeq P) := by
  ext n
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk (kappa P)) * coeff j (PowerSeries.mk (piSeq P)))]
  simp only [coeff_mk]
  rw [piSeq_succ]
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  refine Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma I8 : d⁄dX ℝ (PowerSeries.mk (varpi P)) = -(PowerSeries.mk (kappa P) * PowerSeries.mk (varpi P)) := by
  ext n
  rw [coeff_derivative, map_neg, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (PowerSeries.mk (kappa P)) * coeff j (PowerSeries.mk (varpi P)))]
  simp only [coeff_mk]
  rw [varpi_succ]
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  simp only [Nat.succ_eq_add_one, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma I9 : PowerSeries.mk (varpi P) * PowerSeries.mk (piSeq P) = 1 := by
  apply derivative.ext
  · rw [Derivation.leibniz, I7, I8, derivative_one]
    simp only [smul_eq_mul]; ring
  · simp [varpi_zero, piSeq_zero]


lemma ev_mk (f : ℕ → ℝ) (s : ℝ) : ev (PowerSeries.mk f) s = ∑' n, f n * s ^ n := by
  simp [ev, coeff_mk]

lemma AS_mk_bdd (f : ℕ → ℝ) (B : ℝ) (hB : ∀ n, |f n| ≤ B) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    AS (PowerSeries.mk f) s := AS_of_bdd B (fun n => by rw [coeff_mk]; exact hB n) hs0 hs1

lemma eval_core (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    AS (PowerSeries.mk (dW P)) s ∧ ev (PowerSeries.mk (dW P)) s = (1 - s) / psi P s ∧
    AS (PowerSeries.mk (W P)) s ∧ ev (PowerSeries.mk (W P)) s = 1 / psi P s ∧
    AS (PowerSeries.mk (kappa P)) s ∧ ev (PowerSeries.mk (kappa P)) s = phiImm P s / psi P s := by
  obtain ⟨hs1, hpsi⟩ := s_props P hP s hs
  have hs0 : 0 ≤ s := hs.1
  have h1s : 0 < 1 - s := by linarith
  have ha := hP.1
  have hp := hP.2.2.2.2.2.1
  -- auxiliary summabilities
  have AS1X : AS (1 - X : PowerSeries ℝ) s := AS_sub (AS_one s) (AS_X s)
  have ev1X : ev (1 - X : PowerSeries ℝ) s = 1 - s := by rw [ev_sub (AS_one s) (AS_X s), ev_one, ev_X]
  have ASmu : AS (PowerSeries.mk P.mu) s := AS_mk_bdd _ 1 (fun n => by
    rw [abs_of_nonneg (hP.2.1 n)]
    have := mu_partial P hP (n + 1)
    rw [Finset.sum_range_succ] at this; linarith [this.1, (mu_partial P hP n).1]) hs0 hs1
  have ASnu : AS (PowerSeries.mk P.nu) s := AS_mk_bdd _ 1 (fun n => by
    rw [abs_of_nonneg (hP.2.2.2.2.2.2.2.1 n)]
    have := nu_partial P hP (n + 1)
    rw [Finset.sum_range_succ] at this; linarith [this.1, (nu_partial P hP n).1]) hs0 hs1
  have ASg : AS (PowerSeries.mk (gco P)) s := AS_mk_bdd _ (P.alpha + P.p) (fun n => by
    unfold gco; split_ifs
    · simp; linarith
    · have := muBar_bd P hP n
      rw [abs_of_nonneg (by nlinarith)]; nlinarith) hs0 hs1
  have ASgeo : AS (PowerSeries.mk (fun _ => (1 : ℝ))) s := AS_mk_bdd _ 1 (fun n => by simp) hs0 hs1
  have ASnb : AS (PowerSeries.mk (nuBar P)) s := AS_mk_bdd _ 1 (fun n => by
    have := nuBar_bd P hP n; rw [abs_of_nonneg this.1]; exact this.2) hs0 hs1
  set c := P.alpha * P.mu 0
  have ASC : AS (C c) s := by
    have := AS_C_mul c (AS_one s); simpa using this
  have evC : ev (C c) s = c := by
    have := ev_C_mul c (AS_one s); simpa [ev_one] using this
  have ASh : AS (C c - PowerSeries.mk (gco P)) s := AS_sub ASC ASg
  -- value of h
  have evh : ev (C c - PowerSeries.mk (gco P)) s * (1 - s) = psi P s := by
    have := (ev_mul AS1X ASh).2
    rw [I2 P hP] at this
    have e2 := this.tsum_eq
    have eR : ev (C P.alpha * PowerSeries.mk P.mu - C (P.alpha + P.p) * X) s
        = P.alpha * (∑' j, P.mu j * s ^ j) - (P.alpha + P.p) * s := by
      rw [ev_sub (AS_C_mul _ ASmu) (AS_C_mul _ (AS_X s)), ev_C_mul _ ASmu, ev_C_mul _ (AS_X s),
        ev_X, ev_mk]
    have : ev (C P.alpha * PowerSeries.mk P.mu - C (P.alpha + P.p) * X) s =
      ev (1 - X : PowerSeries ℝ) s * ev (C c - PowerSeries.mk (gco P)) s := e2
    rw [this, ev1X] at eR
    unfold psi; linarith
  have hhpos : 0 < ev (C c - PowerSeries.mk (gco P)) s := by
    by_contra hh; push_neg at hh; nlinarith
  have evh' : ev (C c - PowerSeries.mk (gco P)) s = c - ev (PowerSeries.mk (gco P)) s := by
    rw [ev_sub ASC ASg, evC]
  -- summability of dW
  have ASD : AS (PowerSeries.mk (dW P)) s := by
    have hnn : ∀ n, 0 ≤ dW P n * s ^ n := fun n => mul_nonneg (dW_nonneg P hP n) (pow_nonneg hs0 n)
    have hcoef : ∀ n, c * (dW P n * s ^ n) = (if n = 0 then 1 else 0) +
        ∑ k ∈ range (n + 1), (dW P k * s ^ k) * (gco P (n - k) * s ^ (n - k)) := by
      intro n
      have := congrArg (coeff n) (I1 P hP)
      rw [mul_sub, map_sub, coeff_mul_C, coeff_one, coeff_mk] at this
      have e := coeff_mul_pow (PowerSeries.mk (dW P)) (PowerSeries.mk (gco P)) s n
      simp only [coeff_mk] at e
      rw [← e]
      have h2 : coeff n (PowerSeries.mk (dW P) * PowerSeries.mk (gco P)) =
          dW P n * c - (if n = 0 then 1 else 0) := by linarith
      rw [h2]
      split_ifs with hn
      · subst hn; simp only [pow_zero, mul_one, if_true]; ring
      · ring
    have hgs : Summable (fun n => gco P n * s ^ n) := ASg.of_norm.congr (fun n => by simp [coeff_mk])
    have hgnn : ∀ n, 0 ≤ gco P n * s ^ n := fun n => mul_nonneg (by
      unfold gco; split_ifs
      · rfl
      · have := (muBar_bd P hP n).1; positivity) (pow_nonneg hs0 n)
    have Gs : ∑' n, gco P n * s ^ n = ev (PowerSeries.mk (gco P)) s := (ev_mk _ _).symm
    have bound : ∀ N, ∑ n ∈ range N, dW P n * s ^ n ≤ 1 / ev (C c - PowerSeries.mk (gco P)) s := by
      intro N
      have hc := conv_partial_le (fun k => dW P k * s ^ k) (fun k => gco P k * s ^ k) hnn hgnn hgs N
      have hsum : c * ∑ n ∈ range N, dW P n * s ^ n ≤ 1 + (∑ n ∈ range N, dW P n * s ^ n) *
          ev (PowerSeries.mk (gco P)) s := by
        rw [Finset.mul_sum, ← Gs]
        simp_rw [hcoef]
        rw [Finset.sum_add_distrib]
        have : ∑ n ∈ range N, (if n = 0 then (1 : ℝ) else 0) ≤ 1 := by
          rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
        linarith
      rw [le_div_iff₀ hhpos, evh']
      linarith
    unfold AS
    refine (summable_of_sum_range_le hnn bound).congr (fun n => ?_)
    rw [coeff_mk, Real.norm_of_nonneg (hnn n)]
  have evD : ev (PowerSeries.mk (dW P)) s = (1 - s) / psi P s := by
    have := (ev_mul ASD ASh).2
    rw [I1 P hP] at this
    have e := this.tsum_eq
    have e1 : ev 1 s = ev (PowerSeries.mk (dW P)) s * ev (C c - PowerSeries.mk (gco P)) s := e
    rw [ev_one] at e1
    rw [eq_div_iff hpsi.ne', ← evh]
    nlinarith
  have evgeo : ev (PowerSeries.mk (fun _ => (1 : ℝ))) s = 1 / (1 - s) := by
    have := (ev_mul AS1X ASgeo).2
    rw [I4] at this
    have e1 : ev 1 s = ev (1 - X : PowerSeries ℝ) s * ev (PowerSeries.mk (fun _ => (1 : ℝ))) s :=
      this.tsum_eq
    rw [ev_one, ev1X] at e1
    field_simp; linarith
  have ASW : AS (PowerSeries.mk (W P)) s := by rw [I3]; exact (ev_mul ASD ASgeo).1
  have evW : ev (PowerSeries.mk (W P)) s = 1 / psi P s := by
    have : ev (PowerSeries.mk (W P)) s = ev (PowerSeries.mk (dW P)) s *
        ev (PowerSeries.mk (fun _ => (1 : ℝ))) s := by
      rw [I3]; exact (ev_mul ASD ASgeo).2.tsum_eq
    rw [this, evD, evgeo]; field_simp
  have evnb : ev (PowerSeries.mk (nuBar P)) s = (1 - ∑' j, P.nu j * s ^ j) / (1 - s) := by
    have := (ev_mul AS1X ASnb).2
    rw [I5 P hP] at this
    have e1 : ev (1 - PowerSeries.mk P.nu) s = ev (1 - X : PowerSeries ℝ) s *
        ev (PowerSeries.mk (nuBar P)) s := this.tsum_eq
    rw [ev_sub (AS_one s) ASnu, ev_one, ev_mk, ev1X] at e1
    rw [e1]; field_simp
  have ASnbD := ev_mul ASnb ASD
  have ASK : AS (PowerSeries.mk (kappa P)) s := by
    rw [I6]; exact AS_add (AS_C_mul _ ASnbD.1) (AS_C_mul _ ASW)
  refine ⟨ASD, evD, ASW, evW, ASK, ?_⟩
  have eprod : ev (PowerSeries.mk (nuBar P) * PowerSeries.mk (dW P)) s =
      ev (PowerSeries.mk (nuBar P)) s * ev (PowerSeries.mk (dW P)) s := ASnbD.2.tsum_eq
  rw [I6, ev_add (AS_C_mul _ ASnbD.1) (AS_C_mul _ ASW), ev_C_mul _ ASnbD.1, ev_C_mul _ ASW,
    eprod, evnb, evD, evW]
  unfold phiImm
  field_simp


noncomputable def kf (u : ℝ) : ℝ := phiImm P u / psi P u
noncomputable def KK (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, kf P t
noncomputable def QN (N : ℕ) (u : ℝ) : ℝ := ∑ k ∈ range (N + 1), piSeq P k * u ^ k
noncomputable def DN (N : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ range N, coeff m (PowerSeries.mk (piSeq P) * PowerSeries.mk (kappa P)) * u ^ m

lemma kf_props (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    ContinuousOn (kf P) (Set.Icc 0 s) ∧ (∀ u ∈ Set.Icc 0 s, 0 ≤ kf P u) ∧
    ContinuousOn (KK P) (Set.Icc 0 s) ∧ (∀ u ∈ Set.Ioo 0 s, HasDerivAt (KK P) (kf P u) u) ∧
    (∀ u ∈ Set.Icc 0 s, 0 ≤ KK P u) ∧ KK P 0 = 0 := by
  have hs1 := (s_props P hP s hs).1
  have hu : ∀ u ∈ Set.Icc 0 s, u ∈ Set.Ico 0 (s0 P) := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hs.2⟩
  have hsub : Set.Icc 0 s ⊆ Set.Icc (-1) 1 := Set.Icc_subset_Icc (by norm_num) hs1.le
  have hc : ContinuousOn (kf P) (Set.Icc 0 s) := by
    unfold kf
    exact ((phi_cont P hP).mono hsub).div ((psi_cont P hP).mono hsub)
      (fun u hu' => (s_props P hP u (hu u hu')).2.ne')
  have hnn : ∀ u ∈ Set.Icc 0 s, 0 ≤ kf P u := by
    intro u hu'
    have := eval_core P hP u (hu u hu')
    unfold kf; rw [← this.2.2.2.2.2, ev_mk]
    exact tsum_nonneg (fun n => mul_nonneg (kappa_nonneg P hP n) (pow_nonneg hu'.1 n))
  refine ⟨hc, hnn, ?_, ?_, ?_, ?_⟩
  · have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := s)
      (f := kf P) (by rw [Set.uIcc_of_le hs.1]; exact hc.integrableOn_Icc)
    rw [Set.uIcc_of_le hs.1] at this
    exact this
  · intro u hu'
    have hc' : ContinuousOn (kf P) (Set.Icc 0 u) := hc.mono (Set.Icc_subset_Icc le_rfl hu'.2.le)
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hc'.intervalIntegrable_of_Icc hu'.1.le
    · exact (hc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu'
    · exact hc.continuousAt (Icc_mem_nhds hu'.1 hu'.2)
  · intro u hu'
    exact intervalIntegral.integral_nonneg hu'.1 (fun t ht => hnn t ⟨ht.1, ht.2.trans hu'.2⟩)
  · simp [KK]

lemma QN_zero (N : ℕ) : QN P N 0 = 1 := by
  unfold QN; rw [Finset.sum_range_succ']; simp [piSeq_zero]

lemma QN_deriv (N : ℕ) (u : ℝ) : HasDerivAt (QN P N) (DN P N u) u := by
  have e : QN P N = fun u => ∑ m ∈ range N, piSeq P (m + 1) * u ^ (m + 1) + piSeq P 0 := by
    funext u; unfold QN; rw [Finset.sum_range_succ']; simp
  rw [e]
  have hd : ∀ m ∈ range N, HasDerivAt (fun u => piSeq P (m + 1) * u ^ (m + 1))
      (coeff m (PowerSeries.mk (piSeq P) * PowerSeries.mk (kappa P)) * u ^ m) u := by
    intro m _
    have h1 := ((hasDerivAt_pow (m + 1) u).const_mul (piSeq P (m + 1)))
    refine h1.congr_deriv ?_
    have := congrArg (coeff m) (I7 P)
    rw [coeff_derivative, coeff_mk, mul_comm (PowerSeries.mk (kappa P))] at this
    rw [← this, Nat.add_sub_cancel]; push_cast; ring
  have h2 := (HasDerivAt.sum hd).add_const (piSeq P 0)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall (fun x => ?_))
  simp [Finset.sum_apply]

lemma coeffPK_nonneg (hP : P.Valid) (m : ℕ) :
    0 ≤ coeff m (PowerSeries.mk (piSeq P) * PowerSeries.mk (kappa P)) := by
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun x _ => by
    simp only [coeff_mk]; exact mul_nonneg (piSeq_nonneg P hP _) (kappa_nonneg P hP _))

lemma DN_le (hP : P.Valid) (N : ℕ) (u : ℝ) (hu : u ∈ Set.Ico 0 (s0 P)) :
    DN P N u ≤ QN P N u * kf P u := by
  have ev := eval_core P hP u hu
  have hk : ∑' n, kappa P n * u ^ n = kf P u := by rw [← ev_mk, ev.2.2.2.2.2]; rfl
  have hks : Summable (fun n => kappa P n * u ^ n) :=
    ev.2.2.2.2.1.of_norm.congr (fun n => by simp [coeff_mk])
  have hc := conv_partial_le (fun k => piSeq P k * u ^ k) (fun k => kappa P k * u ^ k)
    (fun n => mul_nonneg (piSeq_nonneg P hP n) (pow_nonneg hu.1 n))
    (fun n => mul_nonneg (kappa_nonneg P hP n) (pow_nonneg hu.1 n)) hks N
  have e : DN P N u = ∑ n ∈ range N, ∑ k ∈ range (n + 1),
      (piSeq P k * u ^ k) * (kappa P (n - k) * u ^ (n - k)) := by
    unfold DN
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [coeff_mul_pow]; simp [coeff_mk]
  rw [e, ← hk]
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (hk ▸ tsum_nonneg (fun n =>
    mul_nonneg (kappa_nonneg P hP n) (pow_nonneg hu.1 n))))
  unfold QN
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ N))
    (fun i _ _ => mul_nonneg (piSeq_nonneg P hP i) (pow_nonneg hu.1 i))

lemma QN_deriv_cont (N : ℕ) : Continuous (QN P N) := by
  unfold QN; fun_prop

lemma QN_le (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) (N : ℕ) :
    QN P N s ≤ Real.exp (KK P s) := by
  obtain ⟨hc, hnn, hKc, hKd, hK0, hK00⟩ := kf_props P hP s hs
  have hu : ∀ u ∈ Set.Icc 0 s, u ∈ Set.Ico 0 (s0 P) := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hs.2⟩
  let f := fun u => QN P N u * Real.exp (-KK P u)
  have hder : ∀ u ∈ Set.Ioo 0 s, HasDerivAt f
      (DN P N u * Real.exp (-KK P u) + QN P N u * (Real.exp (-KK P u) * -kf P u)) u := by
    intro u hu'
    exact (QN_deriv P N u).mul ((hKd u hu').neg.exp)
  have hanti : AntitoneOn f (Set.Icc 0 s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 s)
    · exact (QN_deriv_cont P N).continuousOn.mul (hKc.neg.rexp)
    · rw [interior_Icc]; exact fun u hu' => (hder u hu').differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro u hu'
      rw [(hder u hu').deriv]
      have := DN_le P hP N u (hu u (Set.Ioo_subset_Icc_self hu'))
      have he := Real.exp_pos (-KK P u)
      nlinarith
  have h := hanti ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
  simp only [f, hK00, neg_zero, Real.exp_zero, mul_one, QN_zero] at h
  have : QN P N s = QN P N s * Real.exp (-KK P s) * Real.exp (KK P s) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [this]
  calc QN P N s * Real.exp (-KK P s) * Real.exp (KK P s) ≤ 1 * Real.exp (KK P s) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := one_mul _


lemma AS_pi (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    AS (PowerSeries.mk (piSeq P)) s ∧ ev (PowerSeries.mk (piSeq P)) s ≤ Real.exp (KK P s) := by
  have hnn : ∀ n, 0 ≤ piSeq P n * s ^ n := fun n => mul_nonneg (piSeq_nonneg P hP n) (pow_nonneg hs.1 n)
  have bound : ∀ M, ∑ n ∈ range M, piSeq P n * s ^ n ≤ Real.exp (KK P s) := by
    intro M
    refine le_trans ?_ (QN_le P hP s hs M)
    unfold QN
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ M))
      (fun i _ _ => hnn i)
  constructor
  · unfold AS
    refine (summable_of_sum_range_le hnn bound).congr (fun n => ?_)
    rw [coeff_mk, Real.norm_of_nonneg (hnn n)]
  · rw [ev_mk]; exact Real.tsum_le_of_sum_range_le hnn bound

lemma pi_eq (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    ev (PowerSeries.mk (piSeq P)) s = Real.exp (KK P s) := by
  obtain ⟨hc, hnn, hKc, hKd, hK0, hK00⟩ := kf_props P hP s hs
  have hu : ∀ u ∈ Set.Icc 0 s, u ∈ Set.Ico 0 (s0 P) := fun u hu => ⟨hu.1, lt_of_le_of_lt hu.2 hs.2⟩
  set PK := PowerSeries.mk (piSeq P) * PowerSeries.mk (kappa P)
  -- products
  have hprod : ∀ u ∈ Set.Icc 0 s, AS PK u ∧ ev PK u = ev (PowerSeries.mk (piSeq P)) u * kf P u := by
    intro u hu'
    have e1 := AS_pi P hP u (hu u hu')
    have e2 := eval_core P hP u (hu u hu')
    have := ev_mul e1.1 e2.2.2.2.2.1
    refine ⟨this.1, ?_⟩
    have h3 : ev PK u = ev (PowerSeries.mk (piSeq P)) u * ev (PowerSeries.mk (kappa P)) u :=
      this.2.tsum_eq
    rw [h3, e2.2.2.2.2.2]; rfl
  have hPKs : Summable (fun m => coeff m PK * s ^ m) := (hprod s ⟨hs.1, le_rfl⟩).1.of_norm
  set cN := fun N : ℕ => ev PK s - DN P N s
  have tail : ∀ N, ∀ u ∈ Set.Icc 0 s, QN P N u * kf P u - DN P N u ≤ cN N := by
    intro N u hu'
    have hPKu : Summable (fun m => coeff m PK * u ^ m) := (hprod u hu').1.of_norm
    have h1 : QN P N u ≤ ev (PowerSeries.mk (piSeq P)) u := by
      unfold QN; rw [ev_mk]
      exact ((AS_pi P hP u (hu u hu')).1.of_norm.congr (fun n => by simp [coeff_mk])).sum_le_tsum _
        (fun i _ => mul_nonneg (piSeq_nonneg P hP i) (pow_nonneg hu'.1 i))
    have h2 : QN P N u * kf P u ≤ ev PK u := by
      rw [(hprod u hu').2]; exact mul_le_mul_of_nonneg_right h1 (hnn u hu')
    have eu := hPKu.sum_add_tsum_nat_add N
    have es := hPKs.sum_add_tsum_nat_add N
    have hle : ∑' i, coeff (i + N) PK * u ^ (i + N) ≤ ∑' i, coeff (i + N) PK * s ^ (i + N) :=
      Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu'.1 hu'.2 _)
        (coeffPK_nonneg P hP _)) ((summable_nat_add_iff N).2 hPKu) ((summable_nat_add_iff N).2 hPKs)
    have : ev PK u = DN P N u + ∑' i, coeff (i + N) PK * u ^ (i + N) := eu.symm
    have : ev PK s = DN P N s + ∑' i, coeff (i + N) PK * s ^ (i + N) := es.symm
    simp only [cN]
    linarith
  have lower : ∀ N, 1 - cN N * s ≤ ev (PowerSeries.mk (piSeq P)) s * Real.exp (-KK P s) := by
    intro N
    let g := fun u => QN P N u * Real.exp (-KK P u) + cN N * u
    have hder : ∀ u ∈ Set.Ioo 0 s, HasDerivAt g
        (DN P N u * Real.exp (-KK P u) + QN P N u * (Real.exp (-KK P u) * -kf P u) + cN N * 1) u := by
      intro u hu'
      exact ((QN_deriv P N u).mul ((hKd u hu').neg.exp)).add ((hasDerivAt_id u).const_mul _)
    have hmono : MonotoneOn g (Set.Icc 0 s) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 s)
      · exact ((QN_deriv_cont P N).continuousOn.mul (hKc.neg.rexp)).add
          (continuousOn_const.mul continuousOn_id)
      · rw [interior_Icc]; exact fun u hu' => (hder u hu').differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro u hu'
        rw [(hder u hu').deriv]
        have hu2 : u ∈ Set.Icc 0 s := Set.Ioo_subset_Icc_self hu'
        have d1 := DN_le P hP N u (hu u hu2)
        have d2 := tail N u hu2
        have he := Real.exp_pos (-KK P u)
        have he1 : Real.exp (-KK P u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hK0 u hu2])
        nlinarith
    have h := hmono ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
    simp only [g, hK00, neg_zero, Real.exp_zero, mul_one, QN_zero, mul_zero, add_zero] at h
    have h1 : QN P N s ≤ ev (PowerSeries.mk (piSeq P)) s := by
      unfold QN; rw [ev_mk]
      exact ((AS_pi P hP s hs).1.of_norm.congr (fun n => by simp [coeff_mk])).sum_le_tsum _
        (fun i _ => mul_nonneg (piSeq_nonneg P hP i) (pow_nonneg hs.1 i))
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-KK P s)).le
    linarith
  have hlim : Tendsto (fun N => 1 - cN N * s) atTop (𝓝 1) := by
    have : Tendsto (fun N => DN P N s) atTop (𝓝 (ev PK s)) := hPKs.hasSum.tendsto_sum_nat
    have h2 : Tendsto cN atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ev PK s)).sub this
      simpa [cN] using this
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub (h2.mul_const s)
    simpa using this
  have hge : 1 ≤ ev (PowerSeries.mk (piSeq P)) s * Real.exp (-KK P s) :=
    le_of_tendsto' hlim lower
  have hup := (AS_pi P hP s hs).2
  have : Real.exp (KK P s) ≤ ev (PowerSeries.mk (piSeq P)) s := by
    have e : ev (PowerSeries.mk (piSeq P)) s =
        ev (PowerSeries.mk (piSeq P)) s * Real.exp (-KK P s) * Real.exp (KK P s) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    rw [e]
    calc Real.exp (KK P s) = 1 * Real.exp (KK P s) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hge (Real.exp_pos _).le
  linarith

lemma varpi_eq (hP : P.Valid) (s : ℝ) (hs : s ∈ Set.Ico 0 (s0 P)) :
    AS (PowerSeries.mk (varpi P)) s ∧ ev (PowerSeries.mk (varpi P)) s = Real.exp (-KK P s) := by
  have hpi := AS_pi P hP s hs
  have AV : AS (PowerSeries.mk (varpi P)) s := by
    unfold AS
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hpi.1
    simp only [coeff_mk, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hs.1,
      abs_of_nonneg (piSeq_nonneg P hP n)]
    exact mul_le_mul_of_nonneg_right (varpi_abs_le P hP n) (pow_nonneg hs.1 n)
  refine ⟨AV, ?_⟩
  have := (ev_mul AV hpi.1).2
  rw [I9 P] at this
  have e : ev 1 s = ev (PowerSeries.mk (varpi P)) s * ev (PowerSeries.mk (piSeq P)) s :=
    this.tsum_eq
  rw [ev_one, pi_eq P hP s hs] at e
  rw [Real.exp_neg]
  exact eq_inv_of_mul_eq_one_left e.symm

end P
end L51

open L51 in
theorem solution (P : SkipFreeFluct.MBI.MBIParams) (hP : P.Valid) :
    (∀ k : ℕ, 0 ≤ SkipFreeFluct.MBI.dW P k ∧ 0 ≤ SkipFreeFluct.MBI.W P k ∧
      0 ≤ SkipFreeFluct.MBI.kappa P k ∧ 0 ≤ SkipFreeFluct.MBI.piSeq P k) ∧
    ∀ s ∈ Set.Ico 0 (SkipFreeFluct.MBI.s0 P),
      HasSum (fun k : ℕ => SkipFreeFluct.MBI.dW P k * s ^ k) ((1 - s) / SkipFreeFluct.MBI.psi P s) ∧
      HasSum (fun k : ℕ => SkipFreeFluct.MBI.W P k * s ^ k) (1 / SkipFreeFluct.MBI.psi P s) ∧
      HasSum (fun k : ℕ => SkipFreeFluct.MBI.kappa P k * s ^ k)
        (SkipFreeFluct.MBI.phiImm P s / SkipFreeFluct.MBI.psi P s) ∧
      HasSum (fun k : ℕ => SkipFreeFluct.MBI.piSeq P k * s ^ k)
        (Real.exp (∫ u in (0 : ℝ)..s, SkipFreeFluct.MBI.phiImm P u / SkipFreeFluct.MBI.psi P u)) ∧
      HasSum (fun k : ℕ => SkipFreeFluct.MBI.varpi P k * s ^ k)
        (Real.exp (-∫ u in (0 : ℝ)..s,
          SkipFreeFluct.MBI.phiImm P u / SkipFreeFluct.MBI.psi P u)) := by
  refine ⟨fun k => ⟨dW_nonneg P hP k, W_nonneg P hP k, kappa_nonneg P hP k, piSeq_nonneg P hP k⟩,
    fun s hs => ?_⟩
  have ec := eval_core P hP s hs
  have hsum : ∀ (f : ℕ → ℝ), AS (PowerSeries.mk f) s →
      HasSum (fun k => f k * s ^ k) (ev (PowerSeries.mk f) s) := by
    intro f hf
    have := hf.hasSum
    simpa [PowerSeries.coeff_mk] using this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← ec.2.1]; exact hsum _ ec.1
  · rw [← ec.2.2.2.1]; exact hsum _ ec.2.2.1
  · rw [← ec.2.2.2.2.2]; exact hsum _ ec.2.2.2.2.1
  · have := pi_eq P hP s hs
    unfold KK kf at this
    rw [← this]; exact hsum _ (AS_pi P hP s hs).1
  · have := varpi_eq P hP s hs
    unfold KK kf at this
    rw [← this.2]; exact hsum _ this.1
