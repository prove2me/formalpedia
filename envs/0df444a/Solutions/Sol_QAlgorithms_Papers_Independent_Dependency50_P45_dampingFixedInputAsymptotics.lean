-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P45.dampingFixedInputAsymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:04:31.742984+00:00
-- url     : https://prove2.me/submissions/52854bfa-18f6-4e6f-a9e0-75ef5479b3f1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

-- ===== P45A =====


open scoped ComplexConjugate Matrix
open Filter


namespace X6P45

open QAlgorithms.Papers.Independent.Dependency50.P45
open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel generalizedDampingKraus)

lemma out_input (p x : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1) :
    dampingChannel p 1 (dampingInput x) =
      !![((1 - (1 - p) * x : ℝ) : ℂ), ((0 : ℝ) : ℂ); ((0 : ℝ) : ℂ), (((1 - p) * x : ℝ) : ℂ)] := by
  have hs : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsp : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  push_cast at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dampingChannel, QAlgorithms.krausApply, generalizedDampingKraus,
      QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, Fin.sum_univ_four,
      Matrix.mul_apply, Fin.sum_univ_two, dampingInput, Matrix.diagonal] <;>
    first
    | linear_combination (x : ℂ) * hsp
    | linear_combination (x : ℂ) * hs

lemma out_signal (p x : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1) (b : Bool) :
    dampingChannel p 1 (dampingSignal x b) =
      !![((1 - (1 - p) * x : ℝ) : ℂ),
          (((if b then Real.sqrt (x * (1 - x)) else -Real.sqrt (x * (1 - x))) *
            Real.sqrt (1 - p) : ℝ) : ℂ);
        (((if b then Real.sqrt (x * (1 - x)) else -Real.sqrt (x * (1 - x))) *
            Real.sqrt (1 - p) : ℝ) : ℂ),
        (((1 - p) * x : ℝ) : ℂ)] := by
  have hs : (Real.sqrt (1 - p) : ℂ) * (Real.sqrt (1 - p) : ℂ) = ((1 - p : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsp : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  push_cast at hs
  ext i j
  cases b <;>
  fin_cases i <;> fin_cases j <;>
    simp [dampingChannel, QAlgorithms.krausApply, generalizedDampingKraus,
      QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, Fin.sum_univ_four,
      Matrix.mul_apply, Fin.sum_univ_two, dampingSignal, Matrix.diagonal] <;>
    first
    | linear_combination (x : ℂ) * hsp
    | linear_combination (x : ℂ) * hs
    | ring

lemma trace_cfc_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2, one_mul,
    Matrix.trace_diagonal]
  rfl

lemma ent_one_sub (e : ℝ) :
    -(e * Real.logb 2 e + (1 - e) * Real.logb 2 (1 - e)) = QAlgorithms.binEntropy2 e := by
  unfold QAlgorithms.binEntropy2 Real.logb
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog]
  ring

/-- von Neumann entropy of a real symmetric 2×2 density matrix -/
lemma ent2 [DecidableEq (Fin 2)] (a c d t : ℝ) (had : a + d = 1) (ht : t * (1 - t) = a * d - c * c) :
    QAlgorithms.vnEntropy (!![(a : ℂ), (c : ℂ); (c : ℂ), (d : ℂ)]) =
      QAlgorithms.binEntropy2 t := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![(a : ℂ), (c : ℂ); (c : ℂ), (d : ℂ)]
  have hH : M.IsHermitian := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M]
  have hsum : hH.eigenvalues 0 + hH.eigenvalues 1 = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [Fin.sum_univ_two] at this
    have h2 : M.trace = ((a + d : ℝ) : ℂ) := by
      simp [M, Matrix.trace, Fin.sum_univ_two]
    rw [h2, had] at this
    have h3 := congrArg Complex.re this
    simp at h3
    linarith
  have hprod : hH.eigenvalues 0 * hH.eigenvalues 1 = a * d - c * c := by
    have := hH.det_eq_prod_eigenvalues
    rw [Fin.prod_univ_two] at this
    have hdet : M.det = (a : ℂ) * d - c * c := by
      convert Matrix.det_fin_two_of (a : ℂ) c c d using 2
    rw [hdet] at this
    have h3 := congrArg Complex.re this
    simp at h3
    linarith
  unfold QAlgorithms.vnEntropy
  rw [trace_cfc_herm hH, Fin.sum_univ_two]
  simp only [Complex.add_re, Complex.ofReal_re]
  generalize hH.eigenvalues 0 = e0 at hsum hprod ⊢
  generalize hH.eigenvalues 1 = e1 at hsum hprod ⊢
  have h1 : e1 = 1 - e0 := by linarith
  subst h1
  rw [ent_one_sub]
  have : (e0 - t) * (e0 - (1 - t)) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · rw [show e0 = t by linarith]
  · rw [show e0 = 1 - t by linarith]
    unfold QAlgorithms.binEntropy2
    rw [Real.binEntropy_one_sub]

end X6P45

-- ===== P45B =====


open Filter Topology Real

namespace X6P45

lemma inv_log_tendsto : Tendsto (fun q : ℝ => (Real.log q)⁻¹) (𝓝[>] 0) (𝓝 0) :=
  Real.tendsto_log_nhdsGT_zero.inv_tendsto_atBot

lemma negMulLog_one_sub_le {l : ℝ} (h0 : 0 < l) (h1 : l < 1) :
    0 ≤ negMulLog (1 - l) ∧ negMulLog (1 - l) ≤ l := by
  have hpos : 0 < 1 - l := by linarith
  have hlog : Real.log (1 - l) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  have hge := Real.one_sub_inv_le_log_of_pos hpos
  refine ⟨?_, ?_⟩
  · unfold negMulLog; nlinarith
  · unfold negMulLog
    have : (1 - l) * (1 - (1 - l)⁻¹) = -l := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hge hpos.le]

/-- `h(l(q)) / (-q log q) → c` whenever `l(q)/q → c > 0`. -/
lemma key_limit (l : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hl : Tendsto (fun q => l q / q) (𝓝[>] 0) (𝓝 c))
    (hpos : ∀ᶠ q in 𝓝[>] 0, 0 < l q ∧ l q < 1) :
    Tendsto (fun q => binEntropy (l q) / (-q * Real.log q)) (𝓝[>] 0) (𝓝 c) := by
  have hq : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q ∧ q < 1 := by
    have h1 : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q := self_mem_nhdsWithin
    have h2 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
    exact h1.and h2
  set T1 := fun q => (l q / q) * (1 + Real.log (l q / q) * (Real.log q)⁻¹)
  set T2 := fun q => negMulLog (1 - l q) / (-q * Real.log q)
  have hT1 : Tendsto T1 (𝓝[>] 0) (𝓝 c) := by
    have hlog : Tendsto (fun q => Real.log (l q / q)) (𝓝[>] 0) (𝓝 (Real.log c)) :=
      (Real.continuousAt_log hc.ne').tendsto.comp hl
    have := hl.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hlog.mul inv_log_tendsto))
    simpa using this
  have hT2 : Tendsto T2 (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun q => (l q / q) * |(Real.log q)⁻¹|) (𝓝[>] 0) (𝓝 0) := by
      have := hl.mul inv_log_tendsto.abs
      simpa using this
    apply squeeze_zero_norm' _ hb
    filter_upwards [hq, hpos] with q hq hp
    obtain ⟨n0, n1⟩ := negMulLog_one_sub_le hp.1 hp.2
    have hlq : Real.log q < 0 := Real.log_neg hq.1 hq.2
    simp only [T2, Real.norm_eq_abs]
    rw [abs_div, abs_of_nonneg n0, abs_inv,
      show |-q * Real.log q| = q * |Real.log q| by
        rw [abs_mul, abs_neg, abs_of_pos hq.1]]
    have hab : 0 < |Real.log q| := abs_pos.2 hlq.ne
    rw [div_le_iff₀ (mul_pos hq.1 hab)]
    have : l q / q * |Real.log q|⁻¹ * (q * |Real.log q|) = l q := by
      field_simp
      exact mul_div_cancel_right₀ _ hq.1.ne'
    rw [this]; exact n1
  have := hT1.add hT2
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [hq, hpos] with q hq hp
  have hlq : Real.log q ≠ 0 := (Real.log_neg hq.1 hq.2).ne
  simp only [T1, T2]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.log_div hp.1.ne' hq.1.ne']
  unfold negMulLog
  field_simp
  ring

end X6P45

-- ===== P45C =====


open Filter Topology Real

namespace X6P45

open QAlgorithms.Papers.Independent.Dependency50.P45

/-- small eigenvalue of the damped signal state -/
def lam (q x : ℝ) : ℝ :=
  2 * (q * (1 - q) * x ^ 2) / (1 + Real.sqrt (1 - 4 * (q * (1 - q) * x ^ 2)))

lemma D_le (q x : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ q * (1 - q) * x ^ 2 ∧ 4 * (q * (1 - q) * x ^ 2) ≤ 1 := by
  have h1 : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have h2 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have h3 : x ^ 2 ≤ 1 := by nlinarith
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_le_mul h2 h3 (by positivity) (by norm_num)]

lemma lam_prop (q x : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    lam q x * (1 - lam q x) = q * (1 - q) * x ^ 2 := by
  obtain ⟨hD0, hD1⟩ := D_le q x hq0 hq1 hx0 hx1
  set D := q * (1 - q) * x ^ 2
  set s := Real.sqrt (1 - 4 * D)
  have hs : s ^ 2 = 1 - 4 * D := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  unfold lam
  rw [show Real.sqrt (1 - 4 * (q * (1 - q) * x ^ 2)) = s from rfl]
  have : 0 < 1 + s := by linarith
  field_simp
  nlinarith [hs]

lemma holevo_eq (p x : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    dampingHolevoObjective p x =
      QAlgorithms.binEntropy2 ((1 - p) * x) - QAlgorithms.binEntropy2 (lam (1 - p) x) := by
  unfold dampingHolevoObjective
  rw [out_input p x hp0 hp1, out_signal p x hp0 hp1, out_signal p x hp0 hp1]
  have hsq : Real.sqrt (x * (1 - x)) * Real.sqrt (x * (1 - x)) = x * (1 - x) :=
    Real.mul_self_sqrt (mul_nonneg hx0 (by linarith))
  have hsq' : Real.sqrt (1 - p) * Real.sqrt (1 - p) = 1 - p :=
    Real.mul_self_sqrt (by linarith)
  have hl := lam_prop (1 - p) x (by linarith) (by linarith) hx0 hx1
  rw [ent2 _ _ _ ((1 - p) * x) (by ring) (by ring)]
  rw [ent2 _ _ _ (lam (1 - p) x) (by ring) (by simp only [if_true]; rw [hl]; nlinarith [hsq, hsq'])]
  rw [ent2 _ _ _ (lam (1 - p) x) (by ring)
    (by simp only [Bool.false_eq_true, if_false]; rw [hl]; nlinarith [hsq, hsq'])]
  ring

lemma hq_ev : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q ∧ q < 1 := by
  have h1 : ∀ᶠ q in 𝓝[>] (0 : ℝ), 0 < q := self_mem_nhdsWithin
  have h2 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num))
  exact h1.and h2

lemma K1_lim (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun q => binEntropy (q * x) / (-q * Real.log q)) (𝓝[>] 0) (𝓝 x) := by
  apply key_limit (fun q => q * x) x hx0
  · apply tendsto_const_nhds.congr'
    filter_upwards [hq_ev] with q hq
    have := hq.1.ne'
    field_simp
  · filter_upwards [hq_ev] with q hq
    exact ⟨mul_pos hq.1 hx0, by nlinarith⟩

lemma K2_lim (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun q => binEntropy (lam q x) / (-q * Real.log q)) (𝓝[>] 0) (𝓝 (x ^ 2)) := by
  apply key_limit (fun q => lam q x) (x ^ 2) (by positivity)
  · set k := fun q : ℝ => 2 * ((1 - q) * x ^ 2) / (1 + Real.sqrt (1 - 4 * (q * (1 - q) * x ^ 2)))
    have hk : Tendsto k (𝓝[>] 0) (𝓝 (x ^ 2)) := by
      have hc : ContinuousAt k 0 := by
        apply ContinuousAt.div (by fun_prop) (by fun_prop)
        positivity
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      convert this using 2
      simp [k]; ring
    apply hk.congr'
    filter_upwards [hq_ev] with q hq
    simp only [k, lam]
    have := hq.1.ne'
    field_simp
  · filter_upwards [hq_ev] with q hq
    obtain ⟨hD0, hD1⟩ := D_le q x hq.1.le hq.2.le hx0.le hx1.le
    have hDp : 0 < q * (1 - q) * x ^ 2 :=
      mul_pos (mul_pos hq.1 (by linarith)) (by positivity)
    have hs0 : 0 ≤ Real.sqrt (1 - 4 * (q * (1 - q) * x ^ 2)) := Real.sqrt_nonneg _
    unfold lam
    constructor
    · positivity
    · rw [div_lt_one (by positivity)]
      nlinarith

lemma EA_q_lim (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun q => (binEntropy x + binEntropy (q * x) - binEntropy ((1 - q) * x)) /
      (-x * q * Real.log q)) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun q : ℝ => (1 - q) * x) (-x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub 1).mul_const x
  have hb : HasDerivAt binEntropy (deriv binEntropy x) ((1 - 0) * x) := by
    simpa using (Real.differentiableAt_binEntropy hx0.ne' (by linarith : x ≠ 1)).hasDerivAt
  have hg := hb.comp (0 : ℝ) hd
  have hS := hg.tendsto_slope_zero_right
  have hK := K1_lim x hx0 hx1
  have := (hK.const_mul (1 / x)).add ((hS.mul_const (1 / x)).mul inv_log_tendsto)
  rw [show 1 / x * x + deriv binEntropy x * -x * (1 / x) * 0 = 1 by field_simp; ring] at this
  apply this.congr'
  filter_upwards [hq_ev] with q hq
  have hlq : Real.log q ≠ 0 := (Real.log_neg hq.1 hq.2).ne
  simp only [Function.comp_def, zero_add, sub_zero, one_mul, smul_eq_mul]
  field_simp
  ring

lemma H_q_lim (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun q => (binEntropy (q * x) - binEntropy (lam q x)) /
      (-x * (1 - x) * q * Real.log q)) (𝓝[>] 0) (𝓝 1) := by
  have := ((K1_lim x hx0 hx1).sub (K2_lim x hx0 hx1)).const_mul (1 / (x * (1 - x)))
  have hx1' : 1 - x ≠ 0 := by linarith
  rw [show 1 / (x * (1 - x)) * (x - x ^ 2) = 1 by field_simp] at this
  apply this.congr'
  filter_upwards [hq_ev] with q hq
  have hlq : Real.log q ≠ 0 := (Real.log_neg hq.1 hq.2).ne
  field_simp
  ring

end X6P45

open QAlgorithms.Papers.Independent.Dependency50.P45 X6P45 in
theorem solution (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun p => dampingEAObjective p x / (-x * (1 - p) * Real.logb 2 (1 - p)))
      (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 1) ∧
    Tendsto (fun p => dampingHolevoObjective p x /
      (-x * (1 - x) * (1 - p) * Real.logb 2 (1 - p)))
      (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 1) := by
  have hmap : Tendsto (fun p : ℝ => 1 - p) (𝓝[Set.Ico (0 : ℝ) 1] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun p : ℝ => 1 - p) (𝓝 1) (𝓝 (1 - 1)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact sub_pos.2 hp.2
  have hev : ∀ᶠ p in 𝓝[Set.Ico (0 : ℝ) 1] 1, 0 < p ∧ p < 1 := by
    have h1 : ∀ᶠ p in 𝓝[Set.Ico (0 : ℝ) 1] 1, 0 < p :=
      nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num))
    filter_upwards [h1, self_mem_nhdsWithin] with p h1 h2
    exact ⟨h1, h2.2⟩
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  constructor
  · apply ((EA_q_lim x hx0 hx1).comp hmap).congr'
    filter_upwards [hev] with p hp
    have hlq : Real.log (1 - p) ≠ 0 := (Real.log_neg (by linarith) (by linarith)).ne
    simp only [Function.comp_def, dampingEAObjective, QAlgorithms.binEntropy2, Real.logb]
    rw [show p * x = (1 - (1 - p)) * x by ring]
    have : 1 - p ≠ 0 := by linarith
    field_simp
  · apply ((H_q_lim x hx0 hx1).comp hmap).congr'
    filter_upwards [hev] with p hp
    have hlq : Real.log (1 - p) ≠ 0 := (Real.log_neg (by linarith) (by linarith)).ne
    simp only [Function.comp_def]
    rw [holevo_eq p x hp.1.le hp.2.le hx0.le hx1.le]
    simp only [QAlgorithms.binEntropy2, Real.logb]
    have : 1 - p ≠ 0 := by linarith
    field_simp


