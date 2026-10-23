-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P21.finiteCodewordDistinguishability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:20:57.915995+00:00
-- url     : https://prove2.me/submissions/c40e2139-8201-4cc0-b12f-d057c00b1d44

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P21
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open scoped Nat ComplexConjugate
open InnerProductSpace

theorem X7H_hasSum_pi : ∀ (n : ℕ) (f : Fin n → ℕ → ℂ), (∀ i, Summable (fun k => ‖f i k‖)) →
    Summable (fun occ : Fin n → ℕ => ‖∏ i, f i (occ i)‖) ∧
      HasSum (fun occ : Fin n → ℕ => ∏ i, f i (occ i)) (∏ i, ∑' k, f i k) := by
  intro n
  induction n with
  | zero =>
    intro f _
    refine ⟨Summable.of_finite, ?_⟩
    simpa using (hasSum_fintype (fun occ : Fin 0 → ℕ => ∏ i, f i (occ i)))
  | succ n ih =>
    intro f hf
    obtain ⟨ih1, ih2⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1) => ℕ)
    have hcomp : ∀ x : ℕ × (Fin n → ℕ), (∏ i, f i ((e x) i)) =
        f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i) := by
      intro x
      rw [Fin.prod_univ_succ]
      simp [e, Fin.consEquiv]
    constructor
    · rw [← e.summable_iff]
      have := Summable.mul_of_nonneg (hf 0) ih1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      refine this.congr (fun x => ?_)
      simp only [Function.comp, hcomp, norm_mul]
    · rw [← e.hasSum_iff]
      have hs := summable_mul_of_summable_norm (hf 0) ih1
      have := hs.hasSum
      rw [← tsum_mul_tsum_of_summable_norm (hf 0) ih1, ih2.tsum_eq, ← Fin.prod_univ_succ (f := fun i => ∑' k, f i k)] at this
      refine this.congr_fun (fun x => ?_)
      simp only [Function.comp, hcomp]

/-- coherent overlap kernel -/
def X7H_K (a b : ℂ) : ℂ :=
  (Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ) *
    Complex.exp (conj a * b)

theorem X7H_term (a b : ℂ) : (fun n => conj (coherentCoefficient a n) * coherentCoefficient b n) =
    fun n => ((Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ)) *
      ((conj a * b) ^ n / (n ! : ℂ)) := by
  funext n
  have hs : ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) = (n ! : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]; simp
  have hne : ((Real.sqrt (n ! : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']; positivity
  simp only [coherentCoefficient, map_div₀, map_mul, map_pow, Complex.conj_ofReal]
  rw [← hs, mul_pow]
  field_simp

theorem X7H_term_summable (a b : ℂ) :
    Summable (fun n => ‖conj (coherentCoefficient a n) * coherentCoefficient b n‖) := by
  refine ((NormedSpace.norm_expSeries_div_summable (conj a * b)).mul_left
    ‖((Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ))‖).congr
    (fun n => ?_)
  rw [congrFun (X7H_term a b) n]; simp only [norm_mul]

theorem X7H_term_hasSum (a b : ℂ) :
    HasSum (fun n => conj (coherentCoefficient a n) * coherentCoefficient b n) (X7H_K a b) := by
  rw [X7H_term, X7H_K]
  have := (NormedSpace.expSeries_div_hasSum_exp (conj a * b)).mul_left
    ((Real.exp (-Complex.normSq a / 2) : ℂ) * (Real.exp (-Complex.normSq b / 2) : ℂ))
  rwa [← Complex.exp_eq_exp_ℂ] at this

theorem X7H_K_self (a : ℂ) : X7H_K a a = 1 := by
  rw [X7H_K, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  rw [← Complex.exp_zero]
  congr 1
  push_cast; ring

theorem X7H_K_ne (a b : ℂ) : X7H_K a b ≠ 0 := by
  simp only [X7H_K]
  have h1 := Real.exp_pos (-Complex.normSq a / 2)
  have h2 := Real.exp_pos (-Complex.normSq b / 2)
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
  · exact_mod_cast h1.ne'
  · exact_mod_cast h2.ne'

theorem X7H_word_prod {L : ℕ} (alpha beta : Fin L → ℂ) (occ : Fin L → ℕ) :
    conj (coherentWordCoefficient alpha occ) * coherentWordCoefficient beta occ =
      ∏ i, (conj (coherentCoefficient (alpha i) (occ i)) * coherentCoefficient (beta i) (occ i)) := by
  simp [coherentWordCoefficient, map_prod, Finset.prod_mul_distrib]

theorem X7H_word_summable {L : ℕ} (alpha beta : Fin L → ℂ) :
    Summable (fun occ => ‖conj (coherentWordCoefficient alpha occ) * coherentWordCoefficient beta occ‖) ∧
    HasSum (fun occ => conj (coherentWordCoefficient alpha occ) * coherentWordCoefficient beta occ)
      (∏ i, X7H_K (alpha i) (beta i)) := by
  have := X7H_hasSum_pi L (fun i n => conj (coherentCoefficient (alpha i) n) * coherentCoefficient (beta i) n)
    (fun i => X7H_term_summable _ _)
  simp_rw [X7H_word_prod]
  refine ⟨this.1, ?_⟩
  convert this.2 using 2 with i
  exact (X7H_term_hasSum _ _).tsum_eq.symm

theorem X7H_exists {L : ℕ} (alpha : Fin L → ℂ) : ∃ u : WordFock L, ∀ occupation,
      u occupation = coherentWordCoefficient alpha occupation := by
  have hmem : Memℓp (fun occ : Fin L → ℕ => coherentWordCoefficient alpha occ) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    refine (X7H_word_summable alpha alpha).1.congr (fun occ => ?_)
    simp only [norm_mul, Complex.norm_conj, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, sq]
  exact ⟨⟨_, hmem⟩, fun _ => rfl⟩

theorem X7H_coeff {L : ℕ} (alpha : Fin L → ℂ) (occ : Fin L → ℕ) :
    coherentWord alpha occ = coherentWordCoefficient alpha occ := by
  rw [coherentWord, dif_pos (X7H_exists alpha)]
  exact Classical.choose_spec (X7H_exists alpha) occ

theorem X7H_inner {L : ℕ} (alpha beta : Fin L → ℂ) :
    inner ℂ (coherentWord alpha) (coherentWord beta) = ∏ i, X7H_K (alpha i) (beta i) := by
  refine (lp.hasSum_inner (coherentWord alpha) (coherentWord beta)).unique ?_
  have := (X7H_word_summable alpha beta).2
  refine this.congr_fun (fun occ => ?_)
  simp only [X7H_coeff, RCLike.inner_apply']

theorem X7H_realized {L : ℕ} (alpha : Fin L → ℂ) : CoherentWordRealized alpha := by
  refine ⟨X7H_coeff alpha, ?_⟩
  have h := X7H_inner alpha alpha
  simp only [X7H_K_self, Finset.prod_const_one] at h
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (coherentWord alpha)
  rw [h] at h2
  simp at h2
  nlinarith [norm_nonneg (coherentWord alpha), sq_nonneg (‖coherentWord alpha‖ - 1)]


theorem X7H_core (α β γ l m A B C : ℝ) (hsum : l + m = α + γ) (hprod : l * m = α * γ - β ^ 2)
    (hβ : β ≠ 0) (hl : 0 ≤ l) (hm : m ≤ 0)
    (h1 : β ^ 2 * A + 2 * β * (l - α) * C + (l - α) ^ 2 * B ≤ β ^ 2 + (l - α) ^ 2)
    (h0 : 0 ≤ β ^ 2 * A + 2 * β * (m - α) * C + (m - α) ^ 2 * B) :
    α * A + 2 * β * C + γ * B ≤ l := by
  obtain ⟨d, rfl⟩ : ∃ d, l = α + d := ⟨l - α, by ring⟩
  obtain ⟨d', rfl⟩ : ∃ d', m = α + d' := ⟨m - α, by ring⟩
  obtain rfl : γ = d + d' + α := by linarith
  have hdd : β ^ 2 = -(d * d') := by linear_combination hprod
  have hb2 : 0 < β ^ 2 := by positivity
  have hd : 0 < d := by nlinarith
  have hd' : d' < 0 := by nlinarith
  simp only [add_sub_cancel_left] at h1 h0
  rw [hdd] at h1 h0
  have hN : 0 < d * (d - d') := by nlinarith
  have hN' : 0 < d' * (d' - d) := by nlinarith
  have key : (α + d - (α * A + 2 * β * C + (d + d' + α) * B)) * (d * (d - d') * (d' * (d' - d))) =
      (α + d) * (d' * (d' - d)) * (-(d * d') + d ^ 2 - (-(d * d') * A + 2 * β * d * C + d ^ 2 * B))
      - (α + d') * (d * (d - d')) * (-(d * d') * A + 2 * β * d' * C + d' ^ 2 * B) := by ring
  have hr : 0 ≤ (α + d - (α * A + 2 * β * C + (d + d' + α) * B)) * (d * (d - d') * (d' * (d' - d))) := by
    rw [key]
    have e1 : 0 ≤ (α + d) * (d' * (d' - d)) * (-(d * d') + d ^ 2 - (-(d * d') * A + 2 * β * d * C + d ^ 2 * B)) :=
      mul_nonneg (mul_nonneg hl hN'.le) (by linarith)
    have e2 : 0 ≤ -(α + d') * (d * (d - d')) * (-(d * d') * A + 2 * β * d' * C + d' ^ 2 * B) :=
      mul_nonneg (mul_nonneg (by linarith) hN.le) h0
    linarith
  have := nonneg_of_mul_nonneg_left hr (mul_pos hN hN')
  linarith

theorem X7H_core_eq (α β γ l m : ℝ) (hsum : l + m = α + γ) (hprod : l * m = α * γ - β ^ 2) :
    α * β ^ 2 + 2 * β * β * (l - α) + γ * (l - α) ^ 2 = l * (β ^ 2 + (l - α) ^ 2) := by
  obtain ⟨d, rfl⟩ : ∃ d, l = α + d := ⟨l - α, by ring⟩
  obtain ⟨d', rfl⟩ : ∃ d', m = α + d' := ⟨m - α, by ring⟩
  obtain rfl : γ = d + d' + α := by linarith
  have hdd : β ^ 2 = -(d * d') := by linear_combination hprod
  linear_combination d * hdd

/-- quadratic form expansion -/
theorem X7H_quad {L : ℕ} (T : WordFock L →L[ℂ] WordFock L) (hT : ContinuousLinearMap.adjoint T = T)
    (e1 e2 : WordFock L) (x y : ℝ) :
    (inner ℂ ((x : ℂ) • e1 + (y : ℂ) • e2) (T ((x : ℂ) • e1 + (y : ℂ) • e2))).re =
      x ^ 2 * (inner ℂ e1 (T e1)).re + 2 * x * y * (inner ℂ e1 (T e2)).re +
        y ^ 2 * (inner ℂ e2 (T e2)).re := by
  have h21 : (inner ℂ e2 (T e1)).re = (inner ℂ e1 (T e2)).re := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hT, ← inner_conj_symm (T e2) e1]
    exact Complex.conj_re _
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul, h21]
  ring

theorem X7H_inner_comb {L : ℕ} (e1 e2 : WordFock L) (h11 : inner ℂ e1 e1 = 1) (h12 : inner ℂ e1 e2 = 0)
    (h22 : inner ℂ e2 e2 = 1) (x y x' y' : ℝ) :
    inner ℂ ((x : ℂ) • e1 + (y : ℂ) • e2) ((x' : ℂ) • e1 + (y' : ℂ) • e2) = ((x * x' + y * y' : ℝ) : ℂ) := by
  have h21 : inner ℂ e2 e1 = 0 := by rw [← inner_conj_symm, h12]; simp
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, h11, h12, h21, h22]
  push_cast; ring

theorem X7H_rank_val {L : ℕ} (w x : WordFock L) :
    (inner ℂ x (rankOne ℂ w w x)).re = ‖inner ℂ w x‖ ^ 2 := by
  rw [inner_right_rankOne_apply, ← inner_conj_symm x w, RCLike.conj_mul]
  norm_cast

def X7H_rankEff {L : ℕ} (w : WordFock L) (hw : ‖w‖ = 1) : BinaryEffect L where
  operator := rankOne ℂ w w
  selfAdjoint := by simp
  nonnegative := fun x => by rw [X7H_rank_val]; positivity
  atMostIdentity := fun x => by
    rw [X7H_rank_val]
    have := norm_inner_le_norm (𝕜 := ℂ) w x
    rw [hw, one_mul] at this
    gcongr

def X7H_zeroEff (L : ℕ) : BinaryEffect L where
  operator := 0
  selfAdjoint := by simp
  nonnegative := fun x => by simp
  atMostIdentity := fun x => by simp

def X7H_idEff (L : ℕ) : BinaryEffect L where
  operator := ContinuousLinearMap.id ℂ _
  selfAdjoint := ContinuousLinearMap.adjoint_id
  nonnegative := fun x => by
    rw [ContinuousLinearMap.id_apply]; exact inner_self_nonneg (𝕜 := ℂ)
  atMostIdentity := fun x => by
    rw [ContinuousLinearMap.id_apply]; exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).le

theorem X7H_err_nonneg {L : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u v : WordFock L)
    (hu : ‖u‖ = 1) (T : BinaryEffect L) : 0 ≤ binaryAverageError p u v T.operator := by
  have h1 := T.atMostIdentity u
  have h2 := T.nonnegative v
  rw [hu] at h1
  unfold binaryAverageError
  have : 0 ≤ 1 - p := by linarith
  have : 0 ≤ 1 - (inner ℂ u (T.operator u)).re := by linarith
  positivity


set_option maxHeartbeats 1000000 in
theorem X7H_helstrom_real {L : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (u v : WordFock L)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (s : ℝ) (hs : inner ℂ u v = (s : ℂ)) (hs0 : 0 < s) (hs1 : s < 1) :
    IsLeast (binaryErrorValues p u v) ((1 - Real.sqrt (1 - 4 * p * (1 - p) * s ^ 2)) / 2) := by
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (1 - s ^ 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr (by nlinarith)
  have hr2 : r ^ 2 = 1 - s ^ 2 := by rw [hr]; exact Real.sq_sqrt (by nlinarith)
  obtain ⟨e2, he2⟩ : ∃ e2 : WordFock L, e2 = ((r⁻¹ : ℝ) : ℂ) • (v - (s : ℂ) • u) := ⟨_, rfl⟩
  have huu : inner ℂ u u = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; simp
  have hvv : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
  have hvu : inner ℂ v u = (s : ℂ) := by rw [← inner_conj_symm, hs, Complex.conj_ofReal]
  have h12 : inner ℂ u e2 = 0 := by
    rw [he2, inner_smul_right, inner_sub_right, inner_smul_right, hs, huu]; simp
  have hrC : ((r : ℂ)) ^ 2 = 1 - (s : ℂ) ^ 2 := by exact_mod_cast hr2
  have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have h22 : inner ℂ e2 e2 = 1 := by
    rw [he2, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, huu, hvv, hs, hvu]
    simp only [Complex.conj_ofReal]
    push_cast
    field_simp
    linear_combination -hrC
  have hv_dec : v = (s : ℂ) • u + (r : ℂ) • e2 := by
    rw [he2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr0.ne', Complex.ofReal_one, one_smul]
    abel
  have hu_dec : u = ((1 : ℝ) : ℂ) • u + ((0 : ℝ) : ℂ) • e2 := by simp
  have hnorm : ∀ x y : ℝ, ‖(x : ℂ) • u + (y : ℂ) • e2‖ ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), X7H_inner_comb u e2 huu h12 h22]
    simp; ring
  obtain ⟨D, hD⟩ : ∃ D, D = Real.sqrt (1 - 4 * p * (1 - p) * s ^ 2) := ⟨_, rfl⟩
  rw [← hD]
  have hrad : 0 ≤ 1 - 4 * p * (1 - p) * s ^ 2 := by
    have : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (2 * p - 1)]
    have : 0 ≤ p * (1 - p) := by nlinarith
    nlinarith
  have hD2 : D ^ 2 = 1 - 4 * p * (1 - p) * s ^ 2 := by rw [hD]; exact Real.sq_sqrt hrad
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.sqrt_nonneg _
  have hpq : 0 < p * (1 - p) := by nlinarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = p - (1 - p) * s ^ 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -((1 - p) * s * r) := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = -((1 - p) * r ^ 2) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (p - (1 - p) + D) / 2 := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (p - (1 - p) - D) / 2 := ⟨_, rfl⟩
  have hsum : l + m = α + γ := by rw [hl, hm, hα, hγ]; linear_combination (1 - p) * hr2
  have hprod : l * m = α * γ - β ^ 2 := by
    rw [hl, hm, hα, hβ, hγ]; linear_combination (-1/4) * hD2 + (p * (1 - p)) * hr2
  have hβ0 : β ≠ 0 := by
    rw [hβ]; have : 0 < (1 - p) * s * r := by
      have : 0 < 1 - p := by linarith
      positivity
    linarith
  have hsq : (2 * p - 1) ^ 2 ≤ D ^ 2 := by
    rw [hD2]; nlinarith [mul_pos hpq (mul_pos hr0 hr0)]
  have habs := abs_le_of_sq_le_sq' hsq hD0
  have hl0 : 0 ≤ l := by rw [hl]; linarith [habs.1, habs.2]
  have hm0 : m ≤ 0 := by rw [hm]; linarith [habs.1, habs.2]
  have hval : (1 - D) / 2 = p - l := by rw [hl]; ring
  rw [hval]
  constructor
  · -- attainment
    have hN : 0 < β ^ 2 + (l - α) ^ 2 := by positivity
    obtain ⟨sN, hsN⟩ : ∃ sN, sN = Real.sqrt (β ^ 2 + (l - α) ^ 2) := ⟨_, rfl⟩
    have hsN0 : 0 < sN := by rw [hsN]; exact Real.sqrt_pos.mpr hN
    have hsN2 : sN ^ 2 = β ^ 2 + (l - α) ^ 2 := by rw [hsN]; exact Real.sq_sqrt hN.le
    obtain ⟨w1, hw1⟩ : ∃ w1 : ℝ, w1 = β / sN := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w2 : ℝ, w2 = (l - α) / sN := ⟨_, rfl⟩
    have hww : w1 ^ 2 + w2 ^ 2 = 1 := by
      rw [hw1, hw2]; field_simp; linarith
    have hw : ‖(w1 : ℂ) • u + (w2 : ℂ) • e2‖ = 1 := by
      have h := hnorm w1 w2
      rw [hww] at h
      rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]
    refine ⟨X7H_rankEff _ hw, ?_⟩
    change p - l = binaryAverageError p u v
      (rankOne ℂ ((w1 : ℂ) • u + (w2 : ℂ) • e2) ((w1 : ℂ) • u + (w2 : ℂ) • e2))
    unfold binaryAverageError
    rw [X7H_rank_val, X7H_rank_val]
    have hi1 : inner ℂ ((w1 : ℂ) • u + (w2 : ℂ) • e2) u = ((w1 : ℝ) : ℂ) := by
      have e := X7H_inner_comb u e2 huu h12 h22 w1 w2 1 0
      rw [← hu_dec] at e
      rw [e]; simp
    have hi2 : inner ℂ ((w1 : ℂ) • u + (w2 : ℂ) • e2) v = ((w1 * s + w2 * r : ℝ) : ℂ) := by
      conv_lhs => rw [hv_dec]
      rw [X7H_inner_comb u e2 huu h12 h22]
    rw [hi1, hi2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs]
    have hkey : α * w1 ^ 2 + 2 * β * w1 * w2 + γ * w2 ^ 2 = l := by
      have : α * w1 ^ 2 + 2 * β * w1 * w2 + γ * w2 ^ 2 =
          (α * β ^ 2 + 2 * β * β * (l - α) + γ * (l - α) ^ 2) / sN ^ 2 := by
        rw [hw1, hw2]; field_simp
      rw [this, X7H_core_eq α β γ l m hsum hprod, hsN2]
      field_simp
    rw [← hkey, hα, hβ, hγ]
    ring
  · rintro e ⟨T, rfl⟩
    have hQ : ∀ x y : ℝ, (inner ℂ ((x : ℂ) • u + (y : ℂ) • e2)
        (T.operator ((x : ℂ) • u + (y : ℂ) • e2))).re =
        x ^ 2 * (inner ℂ u (T.operator u)).re + 2 * x * y * (inner ℂ u (T.operator e2)).re +
        y ^ 2 * (inner ℂ e2 (T.operator e2)).re :=
      fun x y => X7H_quad T.operator T.selfAdjoint u e2 x y
    have h1 := T.atMostIdentity ((β : ℂ) • u + ((l - α : ℝ) : ℂ) • e2)
    rw [hQ, hnorm] at h1
    have h0 := T.nonnegative ((β : ℂ) • u + ((m - α : ℝ) : ℂ) • e2)
    rw [hQ] at h0
    have hc := X7H_core α β γ l m _ _ _ hsum hprod hβ0 hl0 hm0 h1 h0
    have hb := hQ s r
    rw [← hv_dec] at hb
    unfold binaryAverageError
    rw [hb]
    rw [hα, hβ, hγ] at hc
    linarith [hc]


theorem X7H_phase {L : ℕ} (p : ℝ) (u v : WordFock L) (ω : ℂ) (hω : ‖ω‖ = 1) :
    binaryErrorValues p u (ω • v) = binaryErrorValues p u v := by
  have key : ∀ T : WordFock L →L[ℂ] WordFock L,
      binaryAverageError p u (ω • v) T = binaryAverageError p u v T := by
    intro T
    unfold binaryAverageError
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, RCLike.conj_mul, hω]
    simp
  ext e
  simp only [binaryErrorValues, key]

theorem X7H_equal_case {L : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (u : WordFock L)
    (hu : ‖u‖ = 1) : IsLeast (binaryErrorValues p u u) (min p (1 - p)) := by
  have huu : (inner ℂ u u).re = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) u
    rw [hu] at this
    simpa using this
  constructor
  · rcases le_total p (1 - p) with h | h
    · rw [min_eq_left h]
      exact ⟨X7H_zeroEff L, by simp [binaryAverageError, X7H_zeroEff]⟩
    · rw [min_eq_right h]
      refine ⟨X7H_idEff L, ?_⟩
      show 1 - p = binaryAverageError p u u (ContinuousLinearMap.id ℂ _)
      unfold binaryAverageError
      rw [ContinuousLinearMap.id_apply, huu]; ring
  · rintro e ⟨T, rfl⟩
    unfold binaryAverageError
    have h1 := T.atMostIdentity u
    have h0 := T.nonnegative u
    rw [hu] at h1
    rcases le_total p (1 - p) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith

theorem X7H_helstrom_pos {L : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (u v : WordFock L)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hz : inner ℂ u v ≠ 0) :
    ∃ e : ℝ, 0 < e ∧ IsLeast (binaryErrorValues p u v) e := by
  obtain ⟨z, hzdef⟩ : ∃ z, z = inner ℂ u v := ⟨_, rfl⟩
  rw [← hzdef] at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzC : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℂ, ω = conj z / ((‖z‖ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hω : ‖ω‖ = 1 := by
    rw [hωdef, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hzn, div_self hzn.ne']
  have hv' : ‖ω • v‖ = 1 := by rw [norm_smul, hω, hv, one_mul]
  have hs : inner ℂ u (ω • v) = ((‖z‖ : ℝ) : ℂ) := by
    rw [inner_smul_right, ← hzdef, hωdef, div_mul_eq_mul_div, RCLike.conj_mul]
    field_simp
    rfl
  rw [← X7H_phase p u v ω hω]
  have hs1 : ‖z‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) u v
    rw [hu, hv, ← hzdef] at this; linarith
  rcases hs1.lt_or_eq with hlt | heq
  · refine ⟨_, ?_, X7H_helstrom_real p hp0 hp1 u (ω • v) hu hv' ‖z‖ hs hzn hlt⟩
    have hpq : 0 < p * (1 - p) := by nlinarith
    have : Real.sqrt (1 - 4 * p * (1 - p) * ‖z‖ ^ 2) < 1 := by
      rw [Real.sqrt_lt' one_pos]
      have := mul_pos hpq (pow_pos hzn 2)
      nlinarith
    linarith
  · have hsq := norm_sub_sq (𝕜 := ℂ) u (ω • v)
    rw [hs, heq, hu, hv'] at hsq
    have h0 : ‖u - ω • v‖ = 0 := by
      have : ‖u - ω • v‖ ^ 2 = 0 := by rw [hsq]; simp; norm_num
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have huv : ω • v = u := (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
    rw [huv]
    exact ⟨_, lt_min hp0 (by linarith), X7H_equal_case p hp0 hp1 u hu⟩

theorem X7H_numberWord_norm {L : ℕ} (a : Fin L → ℕ) : ‖numberWord a‖ = 1 := by
  unfold numberWord
  rw [lp.norm_single (by norm_num)]; simp

theorem X7H_numberWord_inner {L : ℕ} (a b : Fin L → ℕ) (hab : a ≠ b) :
    inner ℂ (numberWord a) (numberWord b) = 0 := by
  unfold numberWord
  rw [lp.inner_single_left, lp.single_apply_ne _ _ _ hab]
  simp

theorem X7H_number_least {L : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (a b : Fin L → ℕ)
    (hab : a ≠ b) : IsLeast (binaryErrorValues p (numberWord a) (numberWord b)) 0 := by
  constructor
  · refine ⟨X7H_rankEff (numberWord a) (X7H_numberWord_norm a), ?_⟩
    show 0 = binaryAverageError p _ _ (rankOne ℂ _ _)
    unfold binaryAverageError
    rw [X7H_rank_val, X7H_rank_val, X7H_numberWord_inner a b hab, inner_self_eq_norm_sq_to_K,
      X7H_numberWord_norm]
    simp
  · rintro e ⟨T, rfl⟩
    exact X7H_err_nonneg p hp0.le hp1.le _ _ (X7H_numberWord_norm a) T

end QAlgorithms.Papers.Independent.Frontier30.P21

end

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open scoped Topology

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Frontier30.P21 in
theorem solution (L : ℕ) (hL : 0 < L)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (a b : Fin L → ℕ) (hab : a ≠ b) (alpha beta : Fin L → ℂ) :
    ‖numberWord a‖ = 1 ∧ ‖numberWord b‖ = 1 ∧
    CoherentWordRealized alpha ∧ CoherentWordRealized beta ∧
    IsLeast (binaryErrorValues p (numberWord a) (numberWord b)) 0 ∧
    ∃ e : ℝ, 0 < e ∧
      IsLeast (binaryErrorValues p (coherentWord alpha) (coherentWord beta)) e := by
  refine ⟨X7H_numberWord_norm a, X7H_numberWord_norm b, X7H_realized alpha, X7H_realized beta,
    X7H_number_least p hp0 hp1 a b hab, ?_⟩
  refine X7H_helstrom_pos p hp0 hp1 _ _ (X7H_realized alpha).2 (X7H_realized beta).2 ?_
  rw [X7H_inner]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => X7H_K_ne _ _)

end
