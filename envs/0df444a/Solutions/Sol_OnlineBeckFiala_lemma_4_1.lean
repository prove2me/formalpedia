-- Prove2me | solution 1 for OnlineBeckFiala.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:24:32.621181+00:00
-- url     : https://prove2.me/submissions/6aa06838-8060-4d86-8de8-8dc2ca7bae93

import Mathlib
import Definitions.Def_OnlineBeckFiala_W
import Theorems.Thm_OnlineBeckFiala_eq_10

section
open MeasureTheory

/-
PLAN. c0 = 1/M, C0 = 2/Z. (1) eq_10 + W <= x when u <= x/(M log^p(ex)) gives P{W>x} <= C0 exp(-c0 x/log^p(ex)).
(2) f = min(max 0 W, d); layer cake: E exp(lam f) = 1 + int_0^inf P{f>t} lam e^{lam t} dt <= 1 + lam D I, with
lam = c0/(2 log^p(ed)), envelope D exp(-b sqrt t) using (1+log t)^p <= K sqrt t. (3) Chernoff with K' = B+1, r <= d:
P{sum f > K' d} <= exp(-lam d). (4) union bound: P{some W_i > d or y_i outside (-1,1)} <= r C0 exp(-c0 d/log^p(ed))
<= C0 C1 exp(-(c0/2) d/log^p(ed)), via d <= C1 exp(b sqrt d). Result: C = C0 C1 + 1, c = c0/2, K = B + 1.
-/
namespace OnlineBeckFiala

namespace Dev.L41

lemma A_ge_one (η : ℝ) (hη : 0 < η) {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : 1 ≤ A η y := by
  unfold A
  have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have h2 : 1 - y ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h1 h2 (by
    have : 0 < 2 / η := by positivity
    rw [neg_div]; linarith)

lemma meas_A (η : ℝ) : Measurable (A η) := by
  unfold A; fun_prop

lemma meas_u (η : ℝ) : Measurable (u η) := by
  unfold u; have := meas_A η; fun_prop

lemma meas_W (η M : ℝ) : Measurable (W η M) := by
  unfold W; have := meas_A η; have := meas_u η; fun_prop

lemma integrable_exp_neg_u (η : ℝ) (hη : 0 < η) :
    IntegrableOn (fun y => Real.exp (-u η y)) (Set.Ioo (-1) 1) := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) ?_ ?_ ?_
  · simp
  · exact (Real.measurable_exp.comp (meas_u η).neg).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have : 0 ≤ u η y := (Real.exp_pos _).le
    calc Real.exp (-u η y) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero

lemma Z_pos (η : ℝ) (hη : 0 < η) : 0 < Z η := by
  unfold Z Zu
  rw [integral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun y => Real.exp (-u η y)) = Set.univ := by
      ext y; simp [Real.exp_ne_zero]
    rw [this, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    simp
  · exact Filter.Eventually.of_forall fun y => (Real.exp_pos _).le
  · exact integrable_exp_neg_u η hη

lemma prob_rho (η : ℝ) (hη : 0 < η) : IsProbabilityMeasure (rho1 η) := by
  constructor
  have h := (eq_10 (u η) (integrable_exp_neg_u η hη) 0).1
  have hs : {y | (0:ℝ) < u η y} = Set.univ := by
    ext y; simp [u, Real.exp_pos]
  have hs2 : {y | y ∈ Set.Ioo (-1 : ℝ) 1 ∧ (0:ℝ) < u η y} = Set.Ioo (-1) 1 := by
    ext y; simp [u, Real.exp_pos]
  rw [hs, hs2] at h
  have hZ := Z_pos η hη
  show potLaw (u η) Set.univ = 1
  rw [h]
  have : (Zu (u η))⁻¹ * ∫ y in Set.Ioo (-1 : ℝ) 1, Real.exp (-u η y) = 1 := by
    have e : Zu (u η) = Z η := rfl
    rw [e]; unfold Z Zu at *
    exact inv_mul_cancel₀ hZ.ne'
  rw [this]; simp

lemma null_compl (η : ℝ) : rho1 η (Set.Ioo (-1 : ℝ) 1)ᶜ = 0 := by
  unfold rho1 potLaw
  rw [withDensity_apply _ measurableSet_Ioo.compl]
  rw [setLIntegral_congr_fun measurableSet_Ioo.compl (g := fun _ => 0)]
  · simp
  · intro y hy
    have : y ∉ Set.Ioo (-1 : ℝ) 1 := hy
    simp [uRho, Set.indicator_of_notMem this]

lemma W_le (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) {y x : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : 1 ≤ x)
    (h : u η y ≤ x / (M * (Real.log (Real.exp 1 * x)) ^ (2 + η))) : W η M y ≤ x := by
  have hA := A_ge_one η hη hy
  have hℓ : Real.log (Real.exp 1 * x) = 1 + Real.log x := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  set ℓ := Real.log (Real.exp 1 * x) with hℓdef
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith
  have hp : (0 : ℝ) < 2 + η := by linarith
  have hℓp : 1 ≤ ℓ ^ (2 + η) := Real.one_le_rpow hℓ1 hp.le
  have hMℓ : 1 ≤ M * ℓ ^ (2 + η) := by nlinarith
  have hupos : 0 < u η y := Real.exp_pos _
  set r := x / (M * ℓ ^ (2 + η)) with hr
  have hrx : r ≤ x := by
    rw [hr, div_le_iff₀ (by linarith)]; nlinarith
  have hAeq : A η y = Real.log (u η y) := by unfold u; rw [Real.log_exp]
  have hAx : A η y ≤ Real.log x := by
    rw [hAeq]; exact Real.log_le_log hupos (h.trans hrx)
  have hAl : A η y ≤ ℓ := by rw [hℓ]; linarith
  have hApow : A η y ^ (2 + η) ≤ ℓ ^ (2 + η) :=
    Real.rpow_le_rpow (by linarith) hAl hp.le
  unfold W
  calc M * u η y * A η y ^ (2 + η) ≤ M * r * ℓ ^ (2 + η) := by
        have h0 : 0 ≤ A η y ^ (2 + η) := Real.rpow_nonneg (by linarith) _
        have hM0 : 0 ≤ M := by linarith
        calc M * u η y * A η y ^ (2 + η) ≤ M * r * A η y ^ (2 + η) := by gcongr
          _ ≤ M * r * ℓ ^ (2 + η) := by
            have : 0 ≤ M * r := by
              rw [hr]; positivity
            exact mul_le_mul_of_nonneg_left hApow this
    _ = x := by rw [hr]; field_simp

lemma tail (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) :
    ∀ x : ℝ, 1 ≤ x →
      rho1 η {y | x < W η M y} ≤
        ENNReal.ofReal (2 / Z η * Real.exp (-(1 / M * x) / (Real.log (Real.exp 1 * x)) ^ (2 + η))) := by
  have hZ := Z_pos η hη
  intro x hx
  set r := x / (M * (Real.log (Real.exp 1 * x)) ^ (2 + η)) with hr
  have hsub : {y | x < W η M y} ⊆ {y | r < u η y} ∪ (Set.Ioo (-1 : ℝ) 1)ᶜ := by
    intro y hy
    by_cases hmem : y ∈ Set.Ioo (-1 : ℝ) 1
    · left
      by_contra hc
      exact absurd (W_le η hη M hM hmem hx (not_lt.mp hc)) (not_le.mpr hy)
    · right; exact hmem
  calc rho1 η {y | x < W η M y}
      ≤ rho1 η ({y | r < u η y} ∪ (Set.Ioo (-1 : ℝ) 1)ᶜ) := measure_mono hsub
    _ ≤ rho1 η {y | r < u η y} + rho1 η (Set.Ioo (-1 : ℝ) 1)ᶜ := measure_union_le _ _
    _ = rho1 η {y | r < u η y} := by rw [null_compl, add_zero]
    _ ≤ ENNReal.ofReal (2 / Zu (u η) * Real.exp (-r)) := (eq_10 (u η) (integrable_exp_neg_u η hη) r).2
    _ = _ := by
      have e : -r = -(1 / M * x) / (Real.log (Real.exp 1 * x)) ^ (2 + η) := by
        rw [hr]; ring
      rw [e]; rfl

lemma log_pow_le (p : ℝ) (hp : 0 < p) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → (1 + Real.log t) ^ p ≤ K * t ^ (1 / 2 : ℝ) := by
  set n := ⌈p⌉₊ with hn
  refine ⟨2 ^ n * (n.factorial : ℝ) * Real.exp (1 / 2), by positivity, fun t ht => ?_⟩
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hs : 1 ≤ 1 + Real.log t := by linarith
  have h1 : (1 + Real.log t) ^ p ≤ (1 + Real.log t) ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs (Nat.le_ceil p)
  rw [Real.rpow_natCast] at h1
  have h2 := Real.pow_div_factorial_le_exp ((1 + Real.log t) / 2) (by linarith) n
  have h3 : Real.exp ((1 + Real.log t) / 2) = Real.exp (1 / 2) * t ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]; congr 1; ring
  rw [h3, div_pow, div_le_iff₀ (by positivity)] at h2
  calc (1 + Real.log t) ^ p ≤ (1 + Real.log t) ^ n := h1
    _ ≤ _ := by
      have : (0:ℝ) < 2 ^ n := by positivity
      rw [div_le_iff₀ this] at h2
      nlinarith [h2]

noncomputable def fd (η M d y : ℝ) : ℝ := min (max 0 (W η M y)) d

lemma fd_nonneg (η M d : ℝ) (hd : 0 ≤ d) (y : ℝ) : 0 ≤ fd η M d y :=
  le_min (le_max_left _ _) hd

lemma fd_le (η M d y : ℝ) : fd η M d y ≤ d := min_le_right _ _

lemma meas_fd (η M d : ℝ) : Measurable (fd η M d) := by
  unfold fd; have := meas_W η M; fun_prop

lemma lt_of_lt_fd {η M d t y : ℝ} (ht : 0 < t) (h : t < fd η M d y) : t < W η M y := by
  unfold fd at h
  have := lt_of_lt_of_le h (min_le_left _ _)
  rcases lt_max_iff.mp this with h1 | h1
  · linarith
  · exact h1

lemma pointwise (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) (K : ℝ) (hK : 0 < K)
    (hQ : ∀ t : ℝ, 1 ≤ t → (1 + Real.log t) ^ (2 + η) ≤ K * t ^ (1 / 2 : ℝ))
    (d : ℝ) (hd : 2 ≤ d) (lam : ℝ) (hlam : 0 < lam)
    (hle : lam ≤ (1 / M) / (2 * (Real.log (Real.exp 1 * d)) ^ (2 + η))) (t : ℝ) (ht : 0 < t) :
    rho1 η {a | t < fd η M d a} * ENNReal.ofReal (lam * Real.exp (lam * t)) ≤
      ENNReal.ofReal (lam * (Real.exp (1 / M / 2 + 1 / M / (2 * K)) + 2 / Z η) *
        Real.exp (-(1 / M / (2 * K)) * t ^ (1 / 2 : ℝ))) := by
  haveI := prob_rho η hη
  have hM0 : 0 < M := by linarith
  have hp : (0 : ℝ) < 2 + η := by linarith
  have hZ := Z_pos η hη
  set c0 : ℝ := 1 / M with hc0
  have hc0pos : 0 < c0 := by positivity
  set b : ℝ := c0 / (2 * K) with hb
  have hbpos : 0 < b := by positivity
  have hℓd : 1 ≤ Real.log (Real.exp 1 * d) := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
    have : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
    linarith
  have hℓdp : 1 ≤ (Real.log (Real.exp 1 * d)) ^ (2 + η) := Real.one_le_rpow hℓd hp.le
  have hlam2 : lam ≤ c0 / 2 := by
    refine hle.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  by_cases htd : d ≤ t
  · have : {a | t < fd η M d a} = ∅ := by
      ext a; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (fd_le η M d a).trans htd
    rw [this]; simp
  push_neg at htd
  by_cases ht1 : t ≤ 1
  · have h1 : rho1 η {a | t < fd η M d a} ≤ 1 := prob_le_one
    calc rho1 η {a | t < fd η M d a} * ENNReal.ofReal (lam * Real.exp (lam * t))
        ≤ 1 * ENNReal.ofReal (lam * Real.exp (lam * t)) := by gcongr
      _ ≤ _ := by
        rw [one_mul]
        apply ENNReal.ofReal_le_ofReal
        have e1 : Real.exp (lam * t) ≤ Real.exp (c0 / 2) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hsq : t ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
        have e2 : Real.exp (-b) ≤ Real.exp (-b * t ^ (1 / 2 : ℝ)) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have e3 : Real.exp (c0 / 2) ≤ Real.exp (c0 / 2 + b) * Real.exp (-b) := by
          rw [← Real.exp_add]; apply le_of_eq; congr 1; ring
        have e4 : Real.exp (c0 / 2 + b) ≤ Real.exp (c0 / 2 + b) + 2 / Z η := by
          have : 0 ≤ 2 / Z η := by positivity
          linarith
        have e5 : 0 < Real.exp (c0 / 2 + b) := Real.exp_pos _
        calc lam * Real.exp (lam * t) ≤ lam * Real.exp (c0 / 2) := by gcongr
          _ ≤ lam * (Real.exp (c0 / 2 + b) * Real.exp (-b)) := by gcongr
          _ ≤ lam * ((Real.exp (c0 / 2 + b) + 2 / Z η) * Real.exp (-b * t ^ (1 / 2 : ℝ))) := by
            gcongr
          _ = _ := by ring
  · push_neg at ht1
    have hsub : {a | t < fd η M d a} ⊆ {a | t < W η M a} := fun a ha => lt_of_lt_fd ht ha
    have h1 := (tail η hη M hM t ht1.le)
    calc rho1 η {a | t < fd η M d a} * ENNReal.ofReal (lam * Real.exp (lam * t))
        ≤ ENNReal.ofReal (2 / Z η * Real.exp (-(c0 * t) / (Real.log (Real.exp 1 * t)) ^ (2 + η))) *
            ENNReal.ofReal (lam * Real.exp (lam * t)) := by
          gcongr
          exact (measure_mono hsub).trans h1
      _ = ENNReal.ofReal ((2 / Z η * Real.exp (-(c0 * t) / (Real.log (Real.exp 1 * t)) ^ (2 + η))) *
            (lam * Real.exp (lam * t))) := by
          exact (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hlt : Real.log (Real.exp 1 * t) = 1 + Real.log t := by
          rw [Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
        have hlogt : 0 < Real.log t := Real.log_pos ht1
        have hlogtd : Real.log t ≤ Real.log d := Real.log_le_log ht htd.le
        have hℓt : 0 < (Real.log (Real.exp 1 * t)) ^ (2 + η) := by
          rw [hlt]; exact Real.rpow_pos_of_pos (by linarith) _
        have hℓtd : (Real.log (Real.exp 1 * t)) ^ (2 + η) ≤ (Real.log (Real.exp 1 * d)) ^ (2 + η) := by
          apply Real.rpow_le_rpow (by rw [hlt]; linarith) _ hp.le
          rw [hlt, Real.log_mul (Real.exp_pos _).ne' (by linarith), Real.log_exp]
          linarith
        set P := (Real.log (Real.exp 1 * t)) ^ (2 + η) with hP
        have hlamP : lam ≤ c0 / (2 * P) := by
          refine hle.trans ?_
          apply div_le_div_of_nonneg_left hc0pos.le (by positivity)
          linarith
        have hlamt : lam * t ≤ c0 * t / (2 * P) := by
          calc lam * t ≤ c0 / (2 * P) * t := by gcongr
            _ = _ := by ring
        have hQt : P ≤ K * t ^ (1 / 2 : ℝ) := by rw [hP, hlt]; exact hQ t ht1.le
        have hsq : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht _
        have hsq2 : t = t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add ht]; norm_num
        have hlow : b * t ^ (1 / 2 : ℝ) ≤ c0 * t / (2 * P) := by
          rw [hb, le_div_iff₀ (by positivity)]
          have : t ^ (1 / 2 : ℝ) * (2 * P) ≤ t ^ (1 / 2 : ℝ) * (2 * (K * t ^ (1 / 2 : ℝ))) := by
            gcongr
          calc c0 / (2 * K) * t ^ (1 / 2 : ℝ) * (2 * P)
              ≤ c0 / (2 * K) * (t ^ (1 / 2 : ℝ) * (2 * (K * t ^ (1 / 2 : ℝ)))) := by
                rw [mul_assoc]; gcongr
            _ = c0 * t := by
                field_simp
                nth_rewrite 2 [hsq2]; ring
        have hexp : Real.exp (lam * t) * Real.exp (-(c0 * t) / P) ≤
            Real.exp (-b * t ^ (1 / 2 : ℝ)) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
          have : -(c0 * t) / P = -(c0 * t / (2 * P)) * 2 := by field_simp
          rw [this]; nlinarith
        have hCpos : 0 ≤ 2 / Z η := by positivity
        calc 2 / Z η * Real.exp (-(c0 * t) / P) * (lam * Real.exp (lam * t))
            = lam * (2 / Z η) * (Real.exp (lam * t) * Real.exp (-(c0 * t) / P)) := by ring
          _ ≤ lam * (2 / Z η) * Real.exp (-b * t ^ (1 / 2 : ℝ)) := by gcongr
          _ ≤ lam * (Real.exp (c0 / 2 + b) + 2 / Z η) * Real.exp (-b * t ^ (1 / 2 : ℝ)) := by
            have : 0 < Real.exp (c0 / 2 + b) := Real.exp_pos _
            gcongr; linarith

lemma mgf_bound (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d : ℝ, 2 ≤ d → ∀ lam : ℝ, 0 < lam →
      lam ≤ (1 / M) / (2 * (Real.log (Real.exp 1 * d)) ^ (2 + η)) →
      ∫ y, Real.exp (lam * fd η M d y) ∂(rho1 η) ≤ 1 + lam * B := by
  haveI := prob_rho η hη
  have hM0 : 0 < M := by linarith
  have hZ := Z_pos η hη
  obtain ⟨K, hK, hQ⟩ := log_pow_le (2 + η) (by linarith)
  set b : ℝ := 1 / M / (2 * K) with hb
  have hbpos : 0 < b := by positivity
  set D : ℝ := Real.exp (1 / M / 2 + 1 / M / (2 * K)) + 2 / Z η with hD
  have hDpos : 0 < D := by positivity
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-b * t ^ (1 / 2 : ℝ))) (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1 / 2) (s := 0) (b := b)
      (by norm_num) (by norm_num) hbpos
    simpa using this
  set I : ℝ := ∫ t in Set.Ioi 0, Real.exp (-b * t ^ (1 / 2 : ℝ)) with hIdef
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t _ => (Real.exp_pos _).le
  refine ⟨D * I, by positivity, fun d hd lam hlam hle => ?_⟩
  have hd0 : (0 : ℝ) ≤ d := by linarith
  have hmeas := meas_fd η M d
  have hg : ∀ t : ℝ, HasDerivAt (fun t => Real.exp (lam * t)) (lam * Real.exp (lam * t)) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul lam).exp
    simpa [mul_comm] using this
  have hint : ∀ a : ℝ, ∫ t in (0 : ℝ)..a, lam * Real.exp (lam * t) = Real.exp (lam * a) - 1 := by
    intro a
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)]
    · simp
    · exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hpt : ∀ y, ENNReal.ofReal (Real.exp (lam * fd η M d y)) =
      1 + ENNReal.ofReal (∫ t in (0 : ℝ)..fd η M d y, lam * Real.exp (lam * t)) := by
    intro y
    rw [hint]
    have : Real.exp (lam * fd η M d y) = 1 + (Real.exp (lam * fd η M d y) - 1) := by ring
    have h1 : 0 ≤ Real.exp (lam * fd η M d y) - 1 := by
      have := fd_nonneg η M d hd0 y
      have : 1 ≤ Real.exp (lam * fd η M d y) := Real.one_le_exp (by positivity)
      linarith
    conv_lhs => rw [this]
    rw [ENNReal.ofReal_add zero_le_one h1]; simp
  have hlc : ∫⁻ y, ENNReal.ofReal (Real.exp (lam * fd η M d y)) ∂(rho1 η) =
      1 + ∫⁻ t in Set.Ioi 0, rho1 η {a | t < fd η M d a} * ENNReal.ofReal (lam * Real.exp (lam * t)) := by
    simp_rw [hpt]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    congr 1
    exact lintegral_comp_eq_lintegral_meas_lt_mul (rho1 η)
      (Filter.Eventually.of_forall fun y => fd_nonneg η M d hd0 y) hmeas.aemeasurable
      (fun t _ => (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _)
      (Filter.Eventually.of_forall fun t => by positivity)
  have hle2 : ∫⁻ t in Set.Ioi 0, rho1 η {a | t < fd η M d a} * ENNReal.ofReal (lam * Real.exp (lam * t))
      ≤ ENNReal.ofReal (lam * (D * I)) := by
    calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (lam * D * Real.exp (-b * t ^ (1 / 2 : ℝ))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          exact pointwise η hη M hM K hK hQ d hd lam hlam hle t ht
      _ = ENNReal.ofReal (∫ t in Set.Ioi (0 : ℝ), lam * D * Real.exp (-b * t ^ (1 / 2 : ℝ))) := by
          symm
          apply ofReal_integral_eq_lintegral_ofReal (hI.const_mul _)
          exact Filter.Eventually.of_forall fun t => by positivity
      _ = _ := by rw [integral_const_mul]; congr 1; ring
  have hE : ∫⁻ y, ENNReal.ofReal (Real.exp (lam * fd η M d y)) ∂(rho1 η) ≤
      ENNReal.ofReal (1 + lam * (D * I)) := by
    rw [hlc, ENNReal.ofReal_add zero_le_one (by positivity)]
    simp only [ENNReal.ofReal_one]
    gcongr
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)
    (by have := meas_fd η M d; fun_prop : Measurable fun y => Real.exp (lam * fd η M d y)).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hE

lemma W_nonneg (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : 0 ≤ W η M y := by
  have := A_ge_one η hη hy
  unfold W
  have : 0 ≤ A η y ^ (2 + η) := Real.rpow_nonneg (by linarith) _
  have : 0 ≤ u η y := (Real.exp_pos _).le
  positivity

lemma bad_union (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ) (S : Set ℝ)
    (hS : MeasurableSet S) :
    (Measure.pi (fun _ : Fin r => ν)) {y | ∃ i, y i ∈ S} ≤ r * ν S := by
  have : {y : Fin r → ℝ | ∃ i, y i ∈ S} = ⋃ i : Fin r, (fun y : Fin r → ℝ => y i) ⁻¹' S := by
    ext y; simp
  rw [this]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have h : ∀ i : Fin r, (Measure.pi (fun _ : Fin r => ν)) ((fun y : Fin r → ℝ => y i) ⁻¹' S) = ν S :=
    fun i => (measurePreserving_eval (fun _ : Fin r => ν) i).measure_preimage hS.nullMeasurableSet
  simp [h]

lemma chernoff (η : ℝ) (hη : 0 < η) (M d lam T : ℝ) (hd : 0 ≤ d) (hlam : 0 < lam) (r : ℕ) :
    (Measure.pi (fun _ : Fin r => rho1 η)) {y | T < ∑ i, fd η M d (y i)} ≤
      ENNReal.ofReal (Real.exp (-(lam * T)) *
        (∫ y, Real.exp (lam * fd η M d y) ∂(rho1 η)) ^ r) := by
  haveI := prob_rho η hη
  set μ := Measure.pi (fun _ : Fin r => rho1 η) with hμ
  set E := ∫ y, Real.exp (lam * fd η M d y) ∂(rho1 η) with hE
  have hmf := meas_fd η M d
  have hFm : Measurable (fun y : Fin r → ℝ => Real.exp (lam * ∑ i, fd η M d (y i))) := by
    have : ∀ i : Fin r, Measurable (fun y : Fin r → ℝ => fd η M d (y i)) :=
      fun i => hmf.comp (measurable_pi_apply i)
    fun_prop
  have hFint : Integrable (fun y : Fin r → ℝ => Real.exp (lam * ∑ i, fd η M d (y i))) μ := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (Real.exp (lam * (r * d)))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam.le
    calc ∑ i, fd η M d (y i) ≤ ∑ _i : Fin r, d := Finset.sum_le_sum fun i _ => fd_le η M d _
      _ = r * d := by simp
  have hFval : ∫ y, Real.exp (lam * ∑ i, fd η M d (y i)) ∂μ = E ^ r := by
    have : ∀ y : Fin r → ℝ, Real.exp (lam * ∑ i, fd η M d (y i)) =
        ∏ i, Real.exp (lam * fd η M d (y i)) := by
      intro y; rw [Finset.mul_sum, Real.exp_sum]
    simp_rw [this]
    rw [integral_fintype_prod_eq_prod (fun _ : Fin r => fun x : ℝ => Real.exp (lam * fd η M d x))]
    simp
    rfl
  have hsub : {y : Fin r → ℝ | T < ∑ i, fd η M d (y i)} ⊆
      {y | Real.exp (lam * T) ≤ Real.exp (lam * ∑ i, fd η M d (y i))} := by
    intro y hy
    exact Real.exp_le_exp.mpr (by simp only [Set.mem_setOf_eq] at hy; nlinarith)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le) hFint (Real.exp (lam * T))
  rw [hFval] at hmk
  have hpos : 0 < Real.exp (lam * T) := Real.exp_pos _
  have hreal : μ.real {y | Real.exp (lam * T) ≤ Real.exp (lam * ∑ i, fd η M d (y i))} ≤
      Real.exp (-(lam * T)) * E ^ r := by
    rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ hpos]; linarith
  calc μ {y | T < ∑ i, fd η M d (y i)}
      ≤ μ {y | Real.exp (lam * T) ≤ Real.exp (lam * ∑ i, fd η M d (y i))} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {y | Real.exp (lam * T) ≤ Real.exp (lam * ∑ i, fd η M d (y i))}) := by
        rw [ofReal_measureReal]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

lemma first_term (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ d : ℝ, 2 ≤ d →
      d * Real.exp (-(1 / M * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η)) ≤
        C1 * Real.exp (-(1 / M / 2 * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η)) := by
  have hM0 : 0 < M := by linarith
  obtain ⟨K, hK, hQ⟩ := log_pow_le (2 + η) (by linarith)
  set c0 : ℝ := 1 / M with hc0
  have hc0pos : 0 < c0 := by positivity
  set b : ℝ := c0 / 2 / K with hb
  have hbpos : 0 < b := by positivity
  refine ⟨2 / b ^ 2, by positivity, fun d hd => ?_⟩
  have hd0 : 0 < d := by linarith
  have hlt : Real.log (Real.exp 1 * d) = 1 + Real.log d := by
    rw [Real.log_mul (Real.exp_pos _).ne' hd0.ne', Real.log_exp]
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  rw [hlt]
  set P := (1 + Real.log d) ^ (2 + η) with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos (by linarith) _
  have hPK : P ≤ K * d ^ (1 / 2 : ℝ) := hQ d (by linarith)
  have hsq : 0 < d ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hd0 _
  have hsq2 : d = d ^ (1 / 2 : ℝ) * d ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hd0]; norm_num
  have h1 : b * d ^ (1 / 2 : ℝ) ≤ c0 / 2 * d / P := by
    rw [le_div_iff₀ hPpos]
    calc b * d ^ (1 / 2 : ℝ) * P ≤ b * d ^ (1 / 2 : ℝ) * (K * d ^ (1 / 2 : ℝ)) := by gcongr
      _ = c0 / 2 * d := by
        rw [hb]; field_simp; nth_rewrite 2 [hsq2]; ring
  have h2 : (b * d ^ (1 / 2 : ℝ)) ^ 2 / 2 ≤ Real.exp (b * d ^ (1 / 2 : ℝ)) := by
    have := Real.quadratic_le_exp_of_nonneg (x := b * d ^ (1 / 2 : ℝ)) (by positivity)
    nlinarith [sq_nonneg (b * d ^ (1 / 2 : ℝ))]
  have h3 : (b * d ^ (1 / 2 : ℝ)) ^ 2 = b ^ 2 * d := by
    rw [mul_pow, sq (d ^ (1 / 2 : ℝ))]; rw [← hsq2]
  have h4 : d ≤ 2 / b ^ 2 * Real.exp (c0 / 2 * d / P) := by
    have : d ≤ 2 / b ^ 2 * Real.exp (b * d ^ (1 / 2 : ℝ)) := by
      rw [h3] at h2
      have hb2 : 0 < b ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hb2]; nlinarith
    exact this.trans (by gcongr)
  have e : -(c0 * d) / P = -(c0 / 2 * d) / P + -(c0 / 2 * d) / P := by ring
  rw [e, Real.exp_add]
  have hX : 0 < Real.exp (-(c0 / 2 * d) / P) := Real.exp_pos _
  have hY : Real.exp (c0 / 2 * d / P) * Real.exp (-(c0 / 2 * d) / P) = 1 := by
    rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  calc d * (Real.exp (-(c0 / 2 * d) / P) * Real.exp (-(c0 / 2 * d) / P))
      = (d * Real.exp (-(c0 / 2 * d) / P)) * Real.exp (-(c0 / 2 * d) / P) := by ring
    _ ≤ (2 / b ^ 2 * Real.exp (c0 / 2 * d / P) * Real.exp (-(c0 / 2 * d) / P)) *
          Real.exp (-(c0 / 2 * d) / P) := by gcongr
    _ = 2 / b ^ 2 * Real.exp (-(c0 / 2 * d) / P) := by
        calc _ = 2 / b ^ 2 * (Real.exp (c0 / 2 * d / P) * Real.exp (-(c0 / 2 * d) / P)) *
              Real.exp (-(c0 / 2 * d) / P) := by ring
          _ = _ := by rw [hY]; ring

end Dev.L41

theorem chk_lemma_4_1 (η : ℝ) (hη : 0 < η) (M : ℝ) (hM : 1 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ d : ℝ, 2 ≤ d → ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ d →
        (Measure.pi (fun _ : Fin r => rho1 η)) {y | K * d < ∑ i, W η M (y i)} ≤
          ENNReal.ofReal (C * Real.exp (-(c * d) / (Real.log (Real.exp 1 * d)) ^ (2 + η))) := by
  have hM0 : 0 < M := by linarith
  have hZ := Dev.L41.Z_pos η hη
  obtain ⟨B, hB0, hmgf⟩ := Dev.L41.mgf_bound η hη M hM
  obtain ⟨C1, hC1, hft⟩ := Dev.L41.first_term η hη M hM
  refine ⟨B + 1, by linarith, 2 / Z η * C1 + 1, 1 / M / 2, by positivity, by positivity, ?_⟩
  intro d hd r hr1 hrd
  haveI := Dev.L41.prob_rho η hη
  have hd0 : 0 < d := by linarith
  have hℓd : 1 ≤ Real.log (Real.exp 1 * d) := by
    rw [Real.log_mul (Real.exp_pos _).ne' hd0.ne', Real.log_exp]
    have : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
    linarith
  have hp : (0 : ℝ) < 2 + η := by linarith
  have hPpos : 0 < (Real.log (Real.exp 1 * d)) ^ (2 + η) := Real.rpow_pos_of_pos (by linarith) _
  set P := (Real.log (Real.exp 1 * d)) ^ (2 + η) with hP
  set lam : ℝ := (1 / M) / (2 * P) with hlam
  have hlampos : 0 < lam := by positivity
  set μ := Measure.pi (fun _ : Fin r => rho1 η) with hμ
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hsub : {y : Fin r → ℝ | (B + 1) * d < ∑ i, W η M (y i)} ⊆
      ({y | ∃ i, y i ∈ (Set.Ioo (-1 : ℝ) 1)ᶜ} ∪ {y | ∃ i, y i ∈ {x | d < W η M x}}) ∪
        {y | (B + 1) * d < ∑ i, Dev.L41.fd η M d (y i)} := by
    intro y hy
    by_cases h1 : ∃ i, y i ∈ (Set.Ioo (-1 : ℝ) 1)ᶜ
    · exact Or.inl (Or.inl h1)
    by_cases h2 : ∃ i, y i ∈ {x | d < W η M x}
    · exact Or.inl (Or.inr h2)
    right
    have heq : ∀ i, Dev.L41.fd η M d (y i) = W η M (y i) := by
      intro i
      have hi : y i ∈ Set.Ioo (-1 : ℝ) 1 := by
        by_contra hc; exact h1 ⟨i, hc⟩
      have hi2 : W η M (y i) ≤ d := by
        by_contra hc; exact h2 ⟨i, not_le.mp hc⟩
      have := Dev.L41.W_nonneg η hη M hM hi
      unfold Dev.L41.fd
      rw [max_eq_right this, min_eq_left hi2]
    simp only [Set.mem_ofPred_eq] at hy ⊢
    simpa [heq] using hy
  have b1 : μ {y | ∃ i, y i ∈ (Set.Ioo (-1 : ℝ) 1)ᶜ} = 0 := by
    refine le_antisymm ?_ zero_le
    refine (Dev.L41.bad_union (rho1 η) r _ measurableSet_Ioo.compl).trans ?_
    rw [Dev.L41.null_compl]; simp
  have b2 : μ {y | ∃ i, y i ∈ {x | d < W η M x}} ≤
      ENNReal.ofReal (2 / Z η * C1 * Real.exp (-(1 / M / 2 * d) / P)) := by
    have hmW : MeasurableSet {x : ℝ | d < W η M x} := measurableSet_lt measurable_const (Dev.L41.meas_W η M)
    refine (Dev.L41.bad_union (rho1 η) r _ hmW).trans ?_
    have ht := Dev.L41.tail η hη M hM d (by linarith)
    calc (r : ENNReal) * rho1 η {x | d < W η M x}
        ≤ (r : ENNReal) * ENNReal.ofReal (2 / Z η * Real.exp (-(1 / M * d) / P)) := by gcongr
      _ = ENNReal.ofReal (r * (2 / Z η * Real.exp (-(1 / M * d) / P))) := by
          rw [ENNReal.ofReal_mul hr0, ENNReal.ofReal_natCast]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have := hft d hd
          have h2Z : 0 ≤ 2 / Z η := by positivity
          calc (r : ℝ) * (2 / Z η * Real.exp (-(1 / M * d) / P))
              ≤ d * (2 / Z η * Real.exp (-(1 / M * d) / P)) := by gcongr
            _ = 2 / Z η * (d * Real.exp (-(1 / M * d) / P)) := by ring
            _ ≤ 2 / Z η * (C1 * Real.exp (-(1 / M / 2 * d) / P)) := by gcongr
            _ = _ := by ring
  have b3 : μ {y | (B + 1) * d < ∑ i, Dev.L41.fd η M d (y i)} ≤
      ENNReal.ofReal (Real.exp (-(1 / M / 2 * d) / P)) := by
    refine (Dev.L41.chernoff η hη M d lam _ hd0.le hlampos r).trans ?_
    apply ENNReal.ofReal_le_ofReal
    set E := ∫ y, Real.exp (lam * Dev.L41.fd η M d y) ∂(rho1 η) with hE
    have hE0 : 0 ≤ E := integral_nonneg fun y => (Real.exp_pos _).le
    have hE1 : E ≤ 1 + lam * B := hmgf d hd lam hlampos le_rfl
    have hE2 : E ≤ Real.exp (lam * B) := hE1.trans (by linarith [Real.add_one_le_exp (lam * B)])
    have hE3 : E ^ r ≤ Real.exp (d * (lam * B)) := by
      calc E ^ r ≤ (Real.exp (lam * B)) ^ r := by gcongr
        _ = Real.exp (r * (lam * B)) := by rw [← Real.exp_nat_mul]
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have : 0 ≤ lam * B := by positivity
          nlinarith
    calc Real.exp (-(lam * ((B + 1) * d))) * E ^ r
        ≤ Real.exp (-(lam * ((B + 1) * d))) * Real.exp (d * (lam * B)) := by gcongr
      _ = Real.exp (-(1 / M / 2 * d) / P) := by
          rw [← Real.exp_add]; congr 1; rw [hlam]; field_simp; ring
  calc μ {y | (B + 1) * d < ∑ i, W η M (y i)}
      ≤ μ (({y | ∃ i, y i ∈ (Set.Ioo (-1 : ℝ) 1)ᶜ} ∪ {y | ∃ i, y i ∈ {x | d < W η M x}}) ∪
        {y | (B + 1) * d < ∑ i, Dev.L41.fd η M d (y i)}) := measure_mono hsub
    _ ≤ μ ({y | ∃ i, y i ∈ (Set.Ioo (-1 : ℝ) 1)ᶜ} ∪ {y | ∃ i, y i ∈ {x | d < W η M x}}) +
        μ {y | (B + 1) * d < ∑ i, Dev.L41.fd η M d (y i)} := measure_union_le _ _
    _ ≤ (μ {y | ∃ i, y i ∈ (Set.Ioo (-1 : ℝ) 1)ᶜ} + μ {y | ∃ i, y i ∈ {x | d < W η M x}}) +
        μ {y | (B + 1) * d < ∑ i, Dev.L41.fd η M d (y i)} := by
        gcongr; exact measure_union_le _ _
    _ ≤ (0 + ENNReal.ofReal (2 / Z η * C1 * Real.exp (-(1 / M / 2 * d) / P))) +
        ENNReal.ofReal (Real.exp (-(1 / M / 2 * d) / P)) := by rw [b1]; gcongr
    _ = ENNReal.ofReal (2 / Z η * C1 * Real.exp (-(1 / M / 2 * d) / P) +
        Real.exp (-(1 / M / 2 * d) / P)) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by congr 1; ring

end OnlineBeckFiala

end

theorem solution : type_of% @OnlineBeckFiala.chk_lemma_4_1 := @OnlineBeckFiala.chk_lemma_4_1
