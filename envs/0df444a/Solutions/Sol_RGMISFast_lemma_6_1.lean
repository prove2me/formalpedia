-- Prove2me | solution 1 for RGMISFast.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T23:39:55.119191+00:00
-- url     : https://prove2.me/submissions/65a79982-feb2-4772-a6bc-b935f1a0a2e6

import Theorems.Thm_RGMISFast_conditional_extension_bounds
import Theorems.Thm_RGMISFast_binomial_moment_exponential_tail

open RGMISFast
set_option autoImplicit false

lemma ct_c_gt : 1 < c := by
  unfold c
  have : 0 < 1 / (2 * Real.exp 2) := by positivity
  linarith
lemma ct_am_pos (m : ℕ) : 0 < am m := by
  unfold am a0 c
  positivity
lemma ct_oneMinus_coe (a b : ℝ) : oneMinusExp a (b : WithTop ℝ) = 1-Real.exp (-(b-a)) := by
  simp [oneMinusExp]
lemma ct_oneMinus_le (a b : ℝ) : oneMinusExp a (b : WithTop ℝ) ≤ b-a := by
  rw [ct_oneMinus_coe]
  have := Real.add_one_le_exp (-(b-a))
  linarith
lemma ct_q_growth (a : ℝ) (ha : 0 < a) :
    Real.exp 1 * oneMinusExp a ((c*a:ℝ):WithTop ℝ) / (a-a/2) ≤ Real.exp (-1) := by
  have h := ct_oneMinus_le a (c*a)
  have hle := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (Real.exp_pos 1).le) (show 0 ≤ a-a/2 by linarith)
  have he : Real.exp 1 * (c*a-a) / (a-a/2) = Real.exp (-1) := by
    unfold c
    have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [←Real.exp_add]; norm_num
    rw [he2,Real.exp_neg]
    field_simp
    <;> ring
  exact he ▸ hle
lemma ct_band_ratio (m i : ℕ) (hi : 1 ≤ i) (him : i < m) :
    am (i-1) / am m = c^(1+m-i) := by
  have hc : c ≠ 0 := (lt_trans (by norm_num) ct_c_gt).ne'
  have he : c^m = c^(1+m-i)*c^(i-1) := by
    rw [←pow_add]
    congr 1
    omega
  unfold am
  have ha : a0 ≠ 0 := (Real.exp_pos 2).ne'
  field_simp
  rw [he]
  <;> ring
lemma ct_band_lt (m i : ℕ) (him : i < m) : (am m : WithTop ℝ) < b i := by
  by_cases hi : i = 0
  · simp [b,hi]
  · simp only [b,if_neg hi,WithTop.coe_lt_coe]
    have hc : 0 < c := lt_trans (by norm_num) ct_c_gt
    have hp : c^(i-1) < c^m := pow_lt_pow_right₀ ct_c_gt (by omega)
    unfold am
    exact mul_lt_mul_of_pos_left (inv_strictAnti₀ (by positivity) hp) (Real.exp_pos 2)
lemma ct_q_boundary (m i : ℕ) (him : i < m) :
    Real.exp 1 * oneMinusExp (am m) (b i) / (am m-am m/2) ≤
      2*Real.exp 1*c^(1+m-i) := by
  have ha := ct_am_pos m
  have hc : 0 < c := lt_trans (by norm_num) ct_c_gt
  by_cases hi : i = 0
  · subst i
    rw [show b 0 = ⊤ by simp [b], show oneMinusExp (am m) ⊤ = 1 by simp [oneMinusExp]]
    simp only [Nat.sub_zero,mul_one]
    have hbig : 1 ≤ a0*c := le_trans (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 2))
      (le_mul_of_one_le_right (Real.exp_pos 2).le ct_c_gt.le)
    have hid : am m*c^(1+m) = a0*c := by
      unfold am
      rw [pow_add]
      simp only [pow_one]
      field_simp
    apply (div_le_iff₀ (show 0 < am m-am m/2 by linarith)).mpr
    have hh := mul_le_mul_of_nonneg_left hbig (Real.exp_pos 1).le
    rw [←hid] at hh
    nlinarith [hh]
  · have hib : 1 ≤ i := by omega
    simp only [b,if_neg hi]
    have h := ct_oneMinus_le (am m) (am (i-1))
    have hle : oneMinusExp (am m) ((am (i-1):ℝ):WithTop ℝ) ≤ am (i-1) := by linarith
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hle (Real.exp_pos 1).le) (show 0 ≤ am m-am m/2 by linarith)
    calc
      _ ≤ _ := hm
      _ = 2*Real.exp 1*(am (i-1)/am m) := by field_simp; ring
      _ = _ := by rw [ct_band_ratio m i hib him]

lemma ct_q_nonneg (a θ : ℝ) (hθa : θ < a) (bb : WithTop ℝ) (hab : (a:WithTop ℝ) < bb) :
    0 ≤ Real.exp 1 * oneMinusExp a bb / (a-θ) := by
  have hnon : 0 ≤ oneMinusExp a bb := by
    induction bb using WithTop.recTopCoe with
    | top => simp [oneMinusExp]
    | coe b =>
      rw [ct_oneMinus_coe]
      have hh : a < b := by exact_mod_cast hab
      have := Real.exp_le_one_iff.mpr (show -(b-a) ≤ 0 by linarith)
      linarith
  exact div_nonneg (mul_nonneg (Real.exp_pos _).le hnon) (by linarith)
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma ct_discrete_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (N : Ω → ℕ) (q : ℝ) (hq : 0 ≤ q) (hqexp : q ≤ Real.exp (-1))
    (htail : ∀ k : ℕ, 1 ≤ k → μ {ω | k ≤ N ω} ≤ ENNReal.ofReal (q^k))
    (x : ℝ) (hx : 0 ≤ x) : μ {ω | x < (N ω:ℝ)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  let k := ⌊x⌋₊+1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hxk : x < (k:ℝ) := by simpa [k] using Nat.lt_floor_add_one x
  have hsub : {ω | x < (N ω:ℝ)} ⊆ {ω | k ≤ N ω} := by
    intro ω hω
    have hh : (⌊x⌋₊:ℝ) < (N ω:ℝ) := lt_of_le_of_lt (Nat.floor_le hx) hω
    have hn : ⌊x⌋₊ < N ω := by exact_mod_cast hh
    dsimp [k]
    omega
  calc
    _ ≤ μ {ω | k ≤ N ω} := measure_mono hsub
    _ ≤ _ := htail k hk
    _ ≤ ENNReal.ofReal ((Real.exp (-1))^k) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hq hqexp _)
    _ = ENNReal.ofReal (Real.exp (-(k:ℝ))) := by
      rw [←Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (bb : WithTop ℝ)
    (hab : ((a : ℝ) : WithTop ℝ) < bb) :
    (∀ k : ℕ, 1 ≤ k →
      condLaw r₀ θ A rA {r | k ≤ (GammaAB G r a bb A).card} ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      Measurable (fun r : V → ℝ => (KAB G r a bb A).choose k) ∧
      ∫⁻ r, ((KAB G r a bb A).choose k : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (θ = a / 2 → ∀ x : ℝ, 0 ≤ x →
      condLaw r₀ θ A rA {r | x < ((GammaAB G r a ((c * a : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-x))) ∧
    (∀ m i : ℕ, i < m → θ = a / 2 → a = am m → ∀ x : ℝ, 1 ≤ x →
      condLaw r₀ θ A rA {r | 32 * c ^ (1 + m - i) * x < (Kmi G r m i A : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-x))) := by
  have hbase := conditional_extension_bounds G θ a hθ hθa r₀ hr₀ A hA hAθ rA hrA bb hab
  refine ⟨hbase.1,hbase.2,?_,?_⟩
  · intro he x hx
    subst θ
    have ha : 0 < a := by linarith
    have hab' : (a:WithTop ℝ) < ((c*a:ℝ):WithTop ℝ) := by
      apply WithTop.coe_lt_coe.mpr
      nlinarith [ct_c_gt]
    exact ct_discrete_tail (condLaw r₀ (a/2) A rA)
      (fun r => (GammaAB G r a ((c*a:ℝ):WithTop ℝ) A).card)
      _ (ct_q_nonneg a (a/2) hθa _ hab') (ct_q_growth a ha)
      (conditional_extension_bounds G (a/2) a hθ hθa r₀ hr₀ A hA hAθ rA hrA _ hab').1 x hx
  · intro m i hi he hea x hx
    subst θ
    subst a
    have hc : 1 ≤ c^(1+m-i) := one_le_pow₀ ct_c_gt.le
    have hmom := (conditional_extension_bounds G (am m/2) (am m) hθ hθa
      r₀ hr₀ A hA hAθ rA hrA (b i) (ct_band_lt m i hi)).2
    apply binomial_moment_exponential_tail (condLaw r₀ (am m/2) A rA)
      (fun r => Kmi G r m i A) (c^(1+m-i)) hc ?_ x hx
    intro k hk
    refine ⟨(hmom k hk).1, (hmom k hk).2.trans ?_⟩
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (ct_q_nonneg (am m) (am m/2) hθa (b i) (ct_band_lt m i hi))
      (ct_q_boundary m i hi) k)


