-- Prove2me | solution 1 for StochApproxDyn.MartingaleNoise.burkholder_eq13
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:37:09.6437+00:00
-- url     : https://prove2.me/submissions/462dfe2e-6c3b-4339-901a-86786a4b4ca7

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


universe u

namespace StochApproxDyn.MartingaleNoise



/-- tangent inequality: `|x|^p ≥ |y|^p + p |y|^(p-2) y (x - y)` for `p ≥ 1`. -/
lemma d42_tangent (p : ℝ) (hp : 1 ≤ p) (x y : ℝ) :
    |y| ^ p + p * (|y| ^ (p - 2) * y) * (x - y) ≤ |x| ^ p := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
    exact Real.rpow_nonneg (abs_nonneg _) _
  have hb : 0 < |y| := abs_pos.2 hy
  set t := x / y with ht
  have hxt : x = t * y := by rw [ht]; field_simp
  have hbern : 1 + p * (|t| - 1) ≤ |t| ^ p := by
    have := one_add_mul_self_le_rpow_one_add (s := |t| - 1) (by linarith [abs_nonneg t]) hp
    simpa using this
  have hsplit : |y| ^ p = |y| ^ (p - 2) * y ^ 2 := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_add hb]; norm_num
  have hx : |x| ^ p = |y| ^ p * |t| ^ p := by
    rw [hxt, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]; ring
  rw [hx]
  have hpos : 0 ≤ |y| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  have hc : 0 ≤ |y| ^ (p - 2) := Real.rpow_nonneg (abs_nonneg _) _
  have key : |y| ^ p + p * (|y| ^ (p - 2) * y) * (x - y) = |y| ^ p * (1 + p * (t - 1)) := by
    rw [hsplit, hxt]; ring
  rw [key]
  apply mul_le_mul_of_nonneg_left _ hpos
  have : t ≤ |t| := le_abs_self t
  nlinarith

/-- monotonicity estimate for `ψ(u) = |u|^(p-2) u`, nonnegative case. -/
lemma d42_psi_nonneg (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    (|y| ^ (p - 2) * y - |x| ^ (p - 2) * x) * (y - x) ≤ (p - 1) * y ^ (p - 2) * (y - x) ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [abs_of_nonneg hx, abs_of_nonneg hy]
  -- tangent inequality for exponent r = p - 1 at y
  have ht := d42_tangent (p - 1) (by linarith) x y
  rw [abs_of_nonneg hx, abs_of_nonneg hy] at ht
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · have : x = 0 := le_antisymm (hy0 ▸ hxy) hx
    subst this; rw [← hy0]; simp
  have e1 : y ^ (p - 2) * y = y ^ (p - 1) := by
    rw [← Real.rpow_add_one hypos.ne']; ring_nf
  have e2 : x ^ (p - 2) * x = x ^ (p - 1) := by
    rcases eq_or_lt_of_le hx with hx0 | hxpos
    · rw [← hx0, Real.zero_rpow (by linarith : p - 1 ≠ 0)]; simp
    · rw [← Real.rpow_add_one hxpos.ne']; ring_nf
  have e3 : y ^ (p - 1 - 2) * y = y ^ (p - 2) := by
    rw [← Real.rpow_add_one hypos.ne']; ring_nf
  rw [e1, e2]
  have h1 : y ^ (p - 1) - x ^ (p - 1) ≤ (p - 1) * y ^ (p - 2) * (y - x) := by
    have : (p - 1) * (y ^ (p - 1 - 2) * y) * (x - y) = - ((p - 1) * y ^ (p - 2) * (y - x)) := by
      rw [e3]; ring
    linarith
  have h2 : 0 ≤ y - x := by linarith
  nlinarith

lemma d42_psi_odd (p : ℝ) (u : ℝ) : |(-u)| ^ (p - 2) * (-u) = -(|u| ^ (p - 2) * u) := by
  rw [abs_neg]; ring

/-- two-sided monotonicity estimate for `ψ`. -/
lemma d42_psi (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) :
    (|y| ^ (p - 2) * y - |x| ^ (p - 2) * x) * (y - x) ≤
      (p - 1) * (max |x| |y|) ^ (p - 2) * (y - x) ^ 2 := by
  have hp2 : 0 ≤ p - 2 := by linarith
  -- WLOG x ≤ y
  wlog hxy : x ≤ y generalizing x y
  · have := this y x (le_of_not_ge hxy)
    rw [max_comm]
    nlinarith [this]
  have hR : ∀ u v : ℝ, 0 ≤ u → u ≤ v → u ^ (p - 2) ≤ v ^ (p - 2) := fun u v hu huv =>
    Real.rpow_le_rpow hu huv hp2
  have hRnn : 0 ≤ (max |x| |y|) ^ (p - 2) := Real.rpow_nonneg (le_max_of_le_left (abs_nonneg _)) _
  rcases le_total 0 x with hx | hx
  · -- 0 ≤ x ≤ y
    have h := d42_psi_nonneg p hp x y hx hxy
    have hy : 0 ≤ y := hx.trans hxy
    have : y ^ (p - 2) ≤ (max |x| |y|) ^ (p - 2) := hR _ _ hy (by rw [abs_of_nonneg hy]; exact le_max_right _ _)
    have hp1 : 0 ≤ p - 1 := by linarith
    nlinarith [sq_nonneg (y - x), mul_le_mul_of_nonneg_left this hp1]
  rcases le_total 0 y with hy | hy
  · -- x ≤ 0 ≤ y
    have ha : |x| = -x := abs_of_nonpos hx
    have hb : |y| = y := abs_of_nonneg hy
    rw [ha, hb]
    have hRa : (-x) ^ (p - 2) ≤ (max (-x) y) ^ (p - 2) := hR _ _ (by linarith) (le_max_left _ _)
    have hRb : y ^ (p - 2) ≤ (max (-x) y) ^ (p - 2) := hR _ _ hy (le_max_right _ _)
    rw [ha, hb] at hRnn
    set K := (max (-x) y) ^ (p - 2)
    have h1 : ((-x) ^ (p - 2)) * (-x) ≤ K * (-x) := mul_le_mul_of_nonneg_right hRa (by linarith)
    have h2 : (y ^ (p - 2)) * y ≤ K * y := mul_le_mul_of_nonneg_right hRb hy
    have h3 : (y ^ (p - 2) * y - (-x) ^ (p - 2) * x) ≤ K * (y - x) := by nlinarith
    have h4 : 0 ≤ y - x := by linarith
    have h5 : K * (y - x) ^ 2 ≤ (p - 1) * K * (y - x) ^ 2 := by
      have : 0 ≤ K * (y - x) ^ 2 := mul_nonneg hRnn (sq_nonneg _)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h3 h4]
  · -- x ≤ y ≤ 0 : negate
    have h := d42_psi_nonneg p hp (-y) (-x) (by linarith) (by linarith)
    rw [d42_psi_odd, d42_psi_odd] at h
    have hR' : (-x) ^ (p - 2) ≤ (max |x| |y|) ^ (p - 2) :=
      hR _ _ (by linarith) (by rw [← abs_of_nonpos hx]; exact le_max_left _ _)
    have hp1 : 0 ≤ p - 1 := by linarith
    have e : (-(|x| ^ (p - 2) * x) - -(|y| ^ (p - 2) * y)) * (-x - -y)
        = (|y| ^ (p - 2) * y - |x| ^ (p - 2) * x) * (y - x) := by ring
    rw [e] at h
    have e2 : (-x - -y) ^ 2 = (y - x) ^ 2 := by ring
    rw [e2] at h
    nlinarith [sq_nonneg (y - x), mul_le_mul_of_nonneg_left hR' hp1]

/-- second-order Taylor-type bound for `|·|^p`, `p ≥ 2`. -/
lemma d42_taylor (p : ℝ) (hp : 2 ≤ p) (x y : ℝ) :
    |y| ^ p ≤ |x| ^ p + p * (|x| ^ (p - 2) * x) * (y - x) +
      p * (p - 1) * (max |x| |y|) ^ (p - 2) * (y - x) ^ 2 := by
  have h1 := d42_tangent p (by linarith) x y
  have h2 := d42_psi p hp x y
  have hp0 : 0 ≤ p := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hp0]




lemma d42_absorb (A K : ℝ≥0∞) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hA : A ≠ ⊤)
    (h : A ≤ K * A ^ (1 - θ)) : A ^ θ ≤ K := by
  rcases eq_or_ne A 0 with rfl | hA0
  · rw [ENNReal.zero_rpow_of_pos hθ0]; exact zero_le
  have hsplit : A = A ^ θ * A ^ (1 - θ) := by
    rw [← ENNReal.rpow_add _ _ hA0 hA]; simp
  have h1 : A ^ (1 - θ) ≠ 0 := by
    rcases eq_or_lt_of_le hθ1 with e | e
    · rw [e, sub_self, ENNReal.rpow_zero]; exact one_ne_zero
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA).ne'
  have h2 : A ^ (1 - θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hA
  nth_rewrite 1 [hsplit] at h
  exact (ENNReal.mul_le_mul_iff_left h1 h2).1 h

lemma d42_absorb' (A K : ℝ≥0∞) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hA : A ≠ ⊤)
    (h : A ≤ K * A ^ (1 - θ)) : A ≤ K ^ (1 / θ) := by
  have := d42_absorb A K θ hθ0 hθ1 hA h
  have h2 := ENNReal.rpow_le_rpow this (by positivity : (0:ℝ) ≤ 1 / θ)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hθ0.ne', ENNReal.rpow_one] at h2

/-- Doob's `L^p` inequality (finite-moment version). -/
lemma d42_doob {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (f : ℕ → Ω → ℝ) (hsub : Submartingale f ℱ P) (hnn : 0 ≤ f)
    (p : ℝ) (hp : 1 < p) (n : ℕ)
    (hfin : ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => f k ω) ^ p) ∂P ≠ ⊤) :
    ∫⁻ ω, ENNReal.ofReal (((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun k => f k ω) ^ p) ∂P ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∫⁻ ω, ENNReal.ofReal (f n ω ^ p) ∂P := by
  set g : Ω → ℝ := fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => f k ω with hg
  have hgm : Measurable g := Finset.measurable_range_sup'' fun k _ =>
    (hsub.stronglyMeasurable k).measurable.le (ℱ.le k)
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω =>
    (hnn n ω).trans (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_self n)))
  have hfm : Measurable (f n) := (hsub.stronglyMeasurable n).measurable.le (ℱ.le n)
  set ν := P.withDensity (fun ω => ENNReal.ofReal (f n ω)) with hν
  set A := ∫⁻ ω, ENNReal.ofReal (g ω ^ p) ∂P with hA
  set B := ∫⁻ ω, ENNReal.ofReal (f n ω ^ p) ∂P with hB
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have lc1 := lintegral_rpow_eq_lintegral_meas_le_mul (μ := P) (f := g)
    (Filter.Eventually.of_forall hg0) hgm.aemeasurable hp0
  have lc2 := lintegral_rpow_eq_lintegral_meas_le_mul (μ := ν) (f := g)
    (Filter.Eventually.of_forall hg0) hgm.aemeasurable hp1
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), P {a | t ≤ g a} * ENNReal.ofReal (t ^ (p - 1)) ≤
      ν {a | t ≤ g a} * ENNReal.ofReal (t ^ (p - 1 - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hmax := maximal_ineq hsub hnn (ε := t.toNNReal) n
    rw [Real.coe_toNNReal _ ht0.le] at hmax
    have hset : MeasurableSet {a | t ≤ g a} := measurableSet_le measurable_const hgm
    have hν' : ν {a | t ≤ g a} = ENNReal.ofReal (∫ ω in {a | t ≤ g a}, f n ω ∂P) := by
      rw [hν, withDensity_apply _ hset, ofReal_integral_eq_lintegral_ofReal]
      · exact (hsub.integrable n).integrableOn
      · exact Filter.Eventually.of_forall fun ω => hnn n ω
    have e : ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal t * ENNReal.ofReal (t ^ (p - 1 - 1)) := by
      rw [← ENNReal.ofReal_mul ht0.le, ← Real.rpow_one_add' ht0.le (by linarith)]
      ring_nf
    rw [e, hν', ← mul_assoc]
    gcongr
    rw [mul_comm]
    have : (t.toNNReal : ℝ≥0∞) = ENNReal.ofReal t := rfl
    rw [← this]
    exact hmax
  have step1 : A ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0, ν {a | t ≤ g a} *
      ENNReal.ofReal (t ^ (p - 1 - 1)) := by
    rw [hA, lc1]
    exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hpt) _
  have hνint : ∫⁻ ω, ENNReal.ofReal (g ω ^ (p - 1)) ∂ν =
      ∫⁻ ω, ENNReal.ofReal (f n ω) * ENNReal.ofReal (g ω ^ (p - 1)) ∂P := by
    rw [hν, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (by exact ENNReal.measurable_ofReal.comp (hgm.pow_const _))]
    rfl
  -- Hölder
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hhol := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq
    (f := fun ω => ENNReal.ofReal (f n ω)) (g := fun ω => ENNReal.ofReal (g ω ^ (p - 1)))
    (by fun_prop) (ENNReal.measurable_ofReal.comp (hgm.pow_const _)).aemeasurable
  have e1 : ∫⁻ a, ENNReal.ofReal (f n a) ^ p ∂P = B := by
    rw [hB]; congr 1; ext ω; rw [ENNReal.ofReal_rpow_of_nonneg (hnn n ω) hp0.le]
  have e2 : ∫⁻ a, ENNReal.ofReal (g a ^ (p - 1)) ^ (p / (p - 1)) ∂P = A := by
    rw [hA]; congr 1; ext ω
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hg0 ω) _) (by positivity),
      ← Real.rpow_mul (hg0 ω)]
    congr 2; field_simp
  rw [e1, e2] at hhol
  have e3 : 1 / (p / (p - 1)) = 1 - 1 / p := by field_simp
  rw [e3] at hhol
  have hmain : A ≤ (ENNReal.ofReal p / ENNReal.ofReal (p - 1) * B ^ (1 / p)) * A ^ (1 - 1 / p) := by
    calc A ≤ ENNReal.ofReal p * ∫⁻ t in Set.Ioi 0, ν {a | t ≤ g a} *
          ENNReal.ofReal (t ^ (p - 1 - 1)) := step1
      _ = ENNReal.ofReal p / ENNReal.ofReal (p - 1) *
          ∫⁻ ω, ENNReal.ofReal (g ω ^ (p - 1)) ∂ν := by
          rw [lc2, ← mul_assoc, ENNReal.div_mul_cancel (by simpa using hp1) ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal p / ENNReal.ofReal (p - 1) * (B ^ (1 / p) * A ^ (1 - 1 / p)) := by
          rw [hνint]; gcongr; exact hhol
      _ = _ := by ring
  have hab := d42_absorb' A _ (1 / p) (by positivity) (by rw [div_le_one hp0]; linarith) hfin hmain
  rw [one_div_one_div] at hab
  refine hab.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
    ENNReal.rpow_one, ← ENNReal.ofReal_div_of_pos hp1, ENNReal.ofReal_rpow_of_nonneg
      (by positivity) hp0.le]




lemma d42_smeas_sum {Ω : Type*} {m : MeasurableSpace Ω} (ξ : ℕ → Ω → ℝ) (k : ℕ)
    (h : ∀ i < k, StronglyMeasurable[m] (ξ i)) :
    StronglyMeasurable[m] (fun ω => ∑ i ∈ Finset.range k, ξ i ω) := by
  induction k with
  | zero => simpa using stronglyMeasurable_const
  | succ k ih =>
    simp only [Finset.sum_range_succ]
    exact (ih fun i hi => h i (by omega)).add (h k (by omega))

lemma d42_mart {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ) (hm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hint : ∀ i, Integrable (ξ i) P) (hce : ∀ i, P[ξ i | ℱ i] =ᵐ[P] 0) :
    Martingale (fun k ω => ∑ i ∈ Finset.range k, ξ i ω) ℱ P := by
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro k
    exact d42_smeas_sum ξ k fun i hi => (hm i).mono (ℱ.mono (by omega))
  · intro k
    exact integrable_finsetSum _ fun i _ => hint i
  · intro k
    have : (fun ω => ∑ i ∈ Finset.range (k + 1), ξ i ω) - (fun ω => ∑ i ∈ Finset.range k, ξ i ω)
        = ξ k := by
      funext ω; simp [Finset.sum_range_succ]
    rw [this]; exact hce k

lemma d42_submart {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ) (hm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hint : ∀ i, Integrable (ξ i) P) (hce : ∀ i, P[ξ i | ℱ i] =ᵐ[P] 0) :
    Submartingale (fun k ω => |∑ i ∈ Finset.range k, ξ i ω|) ℱ P := by
  have hM := d42_mart P ℱ ξ hm hint hce
  apply submartingale_nat
  · intro k
    exact (hM.stronglyAdapted k).norm
  · intro k
    exact (hM.integrable k).abs
  · intro k
    have h1 := hM.condExp_ae_eq (Nat.le_succ k)
    have h2 := norm_condExp_le (μ := P) (m := ℱ k) (fun ω => ∑ i ∈ Finset.range (k + 1), ξ i ω)
    filter_upwards [h1, h2] with ω e1 e2
    simp only [Real.norm_eq_abs] at e2
    rw [← e1]; exact e2

/-- elementary bounds -/
lemma d42_split (p a : ℝ) (hp : 2 ≤ p) (ha : 0 ≤ a) : a ^ (p - 2) * a ^ 2 = a ^ p := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h; rw [Real.zero_rpow (by linarith : p ≠ 0)]; simp
  · rw [← Real.rpow_natCast, ← Real.rpow_add h]; norm_num

lemma d42_young2 (p a b : ℝ) (hp : 2 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (p - 2) * b ^ 2 ≤ a ^ p + b ^ p := by
  have hp2 : 0 ≤ p - 2 := by linarith
  have hap := Real.rpow_nonneg ha p
  have hbp := Real.rpow_nonneg hb p
  rcases le_total a b with h | h
  · have : a ^ (p - 2) ≤ b ^ (p - 2) := Real.rpow_le_rpow ha h hp2
    have := mul_le_mul_of_nonneg_right this (sq_nonneg b)
    rw [d42_split p b hp hb] at this; linarith
  · have : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb h 2
    have := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg ha (p - 2))
    rw [d42_split p a hp ha] at this; linarith

lemma d42_young1 (p a b : ℝ) (hp : 2 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (p - 2) * a * b ≤ a ^ p + b ^ p := by
  have hp2 : 0 ≤ p - 2 := by linarith
  have hap := Real.rpow_nonneg ha p
  have hbp := Real.rpow_nonneg hb p
  have hc := Real.rpow_nonneg ha (p - 2)
  rcases le_total a b with h | h
  · have h1 : a ^ (p - 2) ≤ b ^ (p - 2) := Real.rpow_le_rpow ha h hp2
    have : a ^ (p - 2) * a * b ≤ b ^ (p - 2) * b ^ 2 := by
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h ha (Real.rpow_nonneg hb _)) hb
    rw [d42_split p b hp hb] at this; linarith
  · have : a ^ (p - 2) * a * b ≤ a ^ (p - 2) * a ^ 2 := by
      rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_left h (mul_nonneg hc ha)
    rw [d42_split p a hp ha] at this; linarith

/-- pointwise telescoped Taylor bound. -/
lemma d42_pw (p : ℝ) (hp : 2 ≤ p) (ξ : ℕ → ℝ) (N : ℕ) :
    |∑ i ∈ Finset.range N, ξ i| ^ p ≤
      ∑ i ∈ Finset.range N, p * (|∑ j ∈ Finset.range i, ξ j| ^ (p - 2) *
          ∑ j ∈ Finset.range i, ξ j) * ξ i +
        p * (p - 1) * ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => |∑ j ∈ Finset.range k, ξ j|) ^ (p - 2) *
          ∑ i ∈ Finset.range N, ξ i ^ 2 := by
  set R := (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    fun k => |∑ j ∈ Finset.range k, ξ j| with hR
  have hRk : ∀ k ≤ N, |∑ j ∈ Finset.range k, ξ j| ≤ R := fun k hk =>
    Finset.le_sup' (fun k => |∑ j ∈ Finset.range k, ξ j|) (Finset.mem_range.2 (by omega))
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hRk 0 (Nat.zero_le _))
  have hc : 0 ≤ p * (p - 1) * R ^ (p - 2) := by
    have := Real.rpow_nonneg hR0 (p - 2)
    have : 0 ≤ p * (p - 1) := by nlinarith
    positivity
  have key : ∀ n ≤ N, |∑ i ∈ Finset.range n, ξ i| ^ p ≤
      ∑ i ∈ Finset.range n, p * (|∑ j ∈ Finset.range i, ξ j| ^ (p - 2) *
          ∑ j ∈ Finset.range i, ξ j) * ξ i +
        p * (p - 1) * R ^ (p - 2) * ∑ i ∈ Finset.range n, ξ i ^ 2 := by
    intro n
    induction n with
    | zero => intro _; simp [Real.zero_rpow (by linarith : p ≠ 0)]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have ht := d42_taylor p hp (∑ j ∈ Finset.range n, ξ j) (∑ j ∈ Finset.range (n + 1), ξ j)
      have hmax : (max |∑ j ∈ Finset.range n, ξ j| |∑ j ∈ Finset.range (n + 1), ξ j|) ^ (p - 2)
          ≤ R ^ (p - 2) :=
        Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg _))
          (max_le (hRk n (by omega)) (hRk (n + 1) hn)) (by linarith)
      have hd : ∑ j ∈ Finset.range (n + 1), ξ j - ∑ j ∈ Finset.range n, ξ j = ξ n := by
        rw [Finset.sum_range_succ]; ring
      rw [hd] at ht
      rw [Finset.sum_range_succ (fun i => ξ i ^ 2) n, Finset.sum_range_succ (fun i => p * (|∑ j ∈ Finset.range i, ξ j| ^ (p - 2) * ∑ j ∈ Finset.range i, ξ j) * ξ i) n]
      have hpp : 0 ≤ p * (p - 1) := by nlinarith
      have h3 : p * (p - 1) * (max |∑ j ∈ Finset.range n, ξ j|
          |∑ j ∈ Finset.range (n + 1), ξ j|) ^ (p - 2) * ξ n ^ 2 ≤
          p * (p - 1) * R ^ (p - 2) * ξ n ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hpp) (sq_nonneg _)
      linarith
  exact key N le_rfl




lemma d42_intp {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (f : Ω → ℝ) (p : ℝ)
    (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) P) : Integrable (fun ω => |f ω| ^ p) P := by
  have := hf.integrable_norm_rpow (by simpa using hp) ENNReal.ofReal_ne_top
  simpa [ENNReal.toReal_ofReal hp.le] using this

lemma d42_expect {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ) (hm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hint : ∀ i, Integrable (ξ i) P) (hce : ∀ i, P[ξ i | ℱ i] =ᵐ[P] 0)
    (p : ℝ) (hp : 2 ≤ p) (N : ℕ) (hLp : ∀ i < N, MemLp (ξ i) (ENNReal.ofReal p) P) :
    Integrable (fun ω => ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => |∑ j ∈ Finset.range k, ξ j ω|) ^ p) P ∧
    ∫⁻ ω, ENNReal.ofReal (|∑ j ∈ Finset.range N, ξ j ω| ^ p) ∂P ≤
      ENNReal.ofReal (p * (p - 1)) * ∫⁻ ω, ENNReal.ofReal
        (((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => |∑ j ∈ Finset.range k, ξ j ω|) ^ (p - 2) *
            ∑ i ∈ Finset.range N, ξ i ω ^ 2) ∂P := by
  have hp0 : 0 < p := by linarith
  have hξm : ∀ i, Measurable (ξ i) := fun i => ((hm i).mono (ℱ.le _)).measurable
  have hMm : ∀ k, Measurable (fun ω => ∑ j ∈ Finset.range k, ξ j ω) := fun k =>
    (d42_smeas_sum ξ k fun i _ => (hm i).mono (ℱ.le _)).measurable
  have hMLp : ∀ k ≤ N, MemLp (fun ω => ∑ j ∈ Finset.range k, ξ j ω) (ENNReal.ofReal p) P :=
    fun k hk => memLp_finsetSum _ fun i hi => hLp i (by simp at hi; omega)
  have hMi : ∀ k ≤ N, Integrable (fun ω => |∑ j ∈ Finset.range k, ξ j ω| ^ p) P :=
    fun k hk => d42_intp P _ p hp0 (hMLp k hk)
  have hξi : ∀ i < N, Integrable (fun ω => |ξ i ω| ^ p) P := fun i hi => d42_intp P _ p hp0 (hLp i hi)
  set R : Ω → ℝ := fun ω => (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    fun k => |∑ j ∈ Finset.range k, ξ j ω| with hRdef
  have hRm : Measurable R := Finset.measurable_range_sup'' fun k _ =>
    continuous_abs.measurable.comp (hMm k)
  have hR0 : ∀ ω, 0 ≤ R ω := fun ω => (abs_nonneg _).trans
    (Finset.le_sup' (fun k => |∑ j ∈ Finset.range k, ξ j ω|) (Finset.mem_range.2 (Nat.succ_pos N)))
  have hRp : Integrable (fun ω => R ω ^ p) P := by
    refine Integrable.mono' (integrable_finsetSum (Finset.range (N + 1))
      fun k hk => hMi k (by simp at hk; omega)) (hRm.pow_const p).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hR0 ω) _)]
    obtain ⟨k, hk, hRk⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
      (fun k => |∑ j ∈ Finset.range k, ξ j ω|)
    rw [hRdef]; simp only; rw [hRk]
    exact Finset.single_le_sum (f := fun k => |∑ j ∈ Finset.range k, ξ j ω| ^ p)
      (fun k _ => Real.rpow_nonneg (abs_nonneg _) _) hk
  refine ⟨hRp, ?_⟩
  have hZ : Integrable (fun ω => R ω ^ (p - 2) * ∑ i ∈ Finset.range N, ξ i ω ^ 2) P := by
    refine Integrable.mono' (integrable_finsetSum (Finset.range N)
      fun i hi => hRp.add (hξi i (by simpa using hi))) ?_ ?_
    · exact ((hRm.pow_const _).mul (Finset.measurable_sum _ fun i _ => (hξm i).pow_const 2)).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hR0 ω) _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)), Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := d42_young2 p (R ω) |ξ i ω| hp (hR0 ω) (abs_nonneg _)
    rwa [sq_abs] at this
  have hψi : ∀ i < N, Integrable (fun ω => p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) *
      ∑ j ∈ Finset.range i, ξ j ω) * ξ i ω) P := by
    intro i hi
    refine Integrable.mono' (((hMi i hi.le).add (hξi i hi)).const_mul p) ?_ ?_
    · exact ((((continuous_abs.measurable.comp (hMm i)).pow_const _).mul (hMm i)).const_mul p
        |>.mul (hξm i)).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    have := d42_young1 p |∑ j ∈ Finset.range i, ξ j ω| |ξ i ω| hp (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hp0.le,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hp' : 0 ≤ p := hp0.le
    calc p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) * |∑ j ∈ Finset.range i, ξ j ω|) * |ξ i ω|
        = p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) * |∑ j ∈ Finset.range i, ξ j ω| * |ξ i ω|) := by ring
      _ ≤ p * (|∑ j ∈ Finset.range i, ξ j ω| ^ p + |ξ i ω| ^ p) := mul_le_mul_of_nonneg_left this hp'
  have hψ0 : ∀ i, ∫ ω, p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) *
      ∑ j ∈ Finset.range i, ξ j ω) * ξ i ω ∂P = 0 ∨ ¬ i < N := by
    intro i
    by_cases hi : i < N
    · left
      have hsm : StronglyMeasurable[ℱ i] (fun ω => p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) *
          ∑ j ∈ Finset.range i, ξ j ω)) := by
        have hc : Continuous (fun x : ℝ => p * (|x| ^ (p - 2) * x)) := by
          have : Continuous (fun x : ℝ => |x| ^ (p - 2)) :=
            continuous_abs.rpow_const fun _ => Or.inr (by linarith)
          fun_prop
        exact hc.comp_stronglyMeasurable
          (d42_smeas_sum ξ i fun j hj => (hm j).mono (ℱ.mono (by omega)))
      have hce' := condExp_mul_of_stronglyMeasurable_left (μ := P) hsm (hψi i hi) (hint i)
      have hce'' : P[(fun ω => p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) *
          ∑ j ∈ Finset.range i, ξ j ω) * ξ i ω) | ℱ i] =ᵐ[P] 0 := by
        refine hce'.trans ?_
        filter_upwards [hce i] with ω hω
        simp [hω]
      rw [← integral_condExp (ℱ.le i), integral_congr_ae hce'']
      simp
    · right; exact hi
  have hpw := fun ω => d42_pw p hp (fun j => ξ j ω) N
  have hpp : 0 ≤ p * (p - 1) := by nlinarith
  have hreal : ∫ ω, |∑ j ∈ Finset.range N, ξ j ω| ^ p ∂P ≤
      p * (p - 1) * ∫ ω, R ω ^ (p - 2) * ∑ i ∈ Finset.range N, ξ i ω ^ 2 ∂P := by
    calc ∫ ω, |∑ j ∈ Finset.range N, ξ j ω| ^ p ∂P
        ≤ ∫ ω, (∑ i ∈ Finset.range N, p * (|∑ j ∈ Finset.range i, ξ j ω| ^ (p - 2) *
          ∑ j ∈ Finset.range i, ξ j ω) * ξ i ω +
          p * (p - 1) * (R ω ^ (p - 2) * ∑ i ∈ Finset.range N, ξ i ω ^ 2)) ∂P := by
          refine integral_mono (hMi N le_rfl) ?_ fun ω => ?_
          · exact (integrable_finsetSum _ fun i hi => hψi i (by simpa using hi)).add
              (hZ.const_mul _)
          · have := hpw ω; simp only at this; rw [hRdef]; simp only; linarith
      _ = p * (p - 1) * ∫ ω, R ω ^ (p - 2) * ∑ i ∈ Finset.range N, ξ i ω ^ 2 ∂P := by
          rw [integral_add (integrable_finsetSum _ fun i hi => hψi i (by simpa using hi))
            (hZ.const_mul _), integral_finsetSum _ fun i hi => hψi i (by simpa using hi),
            integral_const_mul]
          rw [Finset.sum_eq_zero fun i hi => ?_]
          · ring
          · rcases hψ0 i with h | h
            · exact h
            · exact absurd (by simpa using hi) h
  rw [← ofReal_integral_eq_lintegral_ofReal (hMi N le_rfl)
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _),
    ← ofReal_integral_eq_lintegral_ofReal hZ (Filter.Eventually.of_forall fun ω =>
      mul_nonneg (Real.rpow_nonneg (hR0 ω) _) (Finset.sum_nonneg fun i _ => sq_nonneg _)),
    ← ENNReal.ofReal_mul hpp]
  exact ENNReal.ofReal_le_ofReal hreal




noncomputable def d42C (p : ℝ) : ℝ := ((p / (p - 1)) ^ p * (p * (p - 1))) ^ (p / 2)

lemma d42C_pos (p : ℝ) (hp : 2 ≤ p) : 0 < d42C p := by
  unfold d42C
  have h1 : 0 < p - 1 := by linarith
  have h2 : 0 < p := by linarith
  positivity

/-- Burkholder's inequality (upper half, `p ≥ 2`) for real martingale difference sequences. -/
theorem d42_burk_real {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ) (hm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (ξ i))
    (hint : ∀ i, Integrable (ξ i) P) (hce : ∀ i, P[ξ i | ℱ i] =ᵐ[P] 0)
    (p : ℝ) (hp : 2 ≤ p) (N : ℕ) (hLp : ∀ i < N, MemLp (ξ i) (ENNReal.ofReal p) P) :
    ∫⁻ ω, ENNReal.ofReal (((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => |∑ j ∈ Finset.range k, ξ j ω|) ^ p) ∂P ≤
      ENNReal.ofReal (d42C p) *
        ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ Finset.range N, ξ i ω ^ 2) ^ (p / 2)) ∂P := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨hRp, hBZ⟩ := d42_expect P ℱ ξ hm hint hce p hp N hLp
  set R : Ω → ℝ := fun ω => (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    fun k => |∑ j ∈ Finset.range k, ξ j ω| with hRdef
  set S2 : Ω → ℝ := fun ω => ∑ i ∈ Finset.range N, ξ i ω ^ 2 with hS2
  have hR0 : ∀ ω, 0 ≤ R ω := fun ω => (abs_nonneg _).trans
    (Finset.le_sup' (fun k => |∑ j ∈ Finset.range k, ξ j ω|) (Finset.mem_range.2 (Nat.succ_pos N)))
  have hS0 : ∀ ω, 0 ≤ S2 ω := fun ω => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hξm : ∀ i, Measurable (ξ i) := fun i => ((hm i).mono (ℱ.le _)).measurable
  have hMm : ∀ k, Measurable (fun ω => ∑ j ∈ Finset.range k, ξ j ω) := fun k =>
    (d42_smeas_sum ξ k fun i _ => (hm i).mono (ℱ.le _)).measurable
  have hRm : Measurable R := Finset.measurable_range_sup'' fun k _ =>
    continuous_abs.measurable.comp (hMm k)
  have hS2m : Measurable S2 := Finset.measurable_sum _ fun i _ => (hξm i).pow_const 2
  set A := ∫⁻ ω, ENNReal.ofReal (R ω ^ p) ∂P with hA
  set Y := ∫⁻ ω, ENNReal.ofReal (S2 ω ^ (p / 2)) ∂P with hY
  have hAfin : A ≠ ⊤ := (hRp.lintegral_lt_top).ne
  -- Doob
  have hdoob := d42_doob P ℱ _ (d42_submart P ℱ ξ hm hint hce)
    (fun k ω => abs_nonneg _) p hp1 N hAfin
  -- Hölder
  have hhol : ∫⁻ ω, ENNReal.ofReal (R ω ^ (p - 2) * S2 ω) ∂P ≤
      A ^ (1 - 2 / p) * Y ^ (2 / p) := by
    rcases eq_or_lt_of_le hp with h2 | h2
    · rw [← h2]
      have hz : ∀ ω, ENNReal.ofReal (R ω ^ ((2:ℝ) - 2) * S2 ω) = ENNReal.ofReal (S2 ω ^ ((2:ℝ) / 2)) := by
        intro ω; norm_num
      simp_rw [hz]
      rw [← h2] at hY
      rw [← hY, show (1:ℝ) - 2 / 2 = 0 by norm_num, show (2:ℝ) / 2 = 1 by norm_num,
        ENNReal.rpow_zero, ENNReal.rpow_one, one_mul]
    · have hpq : (p / (p - 2)).HolderConjugate (p / 2) := by
        rw [Real.holderConjugate_iff]
        constructor
        · rw [one_lt_div (by linarith)]; linarith
        · field_simp; ring
      have := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq
        (f := fun ω => ENNReal.ofReal (R ω ^ (p - 2))) (g := fun ω => ENNReal.ofReal (S2 ω))
        (ENNReal.measurable_ofReal.comp (hRm.pow_const _)).aemeasurable
        (ENNReal.measurable_ofReal.comp hS2m).aemeasurable
      have e0 : ∀ ω, ENNReal.ofReal (R ω ^ (p - 2) * S2 ω) =
          (fun ω => ENNReal.ofReal (R ω ^ (p - 2))) ω * (fun ω => ENNReal.ofReal (S2 ω)) ω := by
        intro ω; simp only; rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hR0 ω) _)]
      have e1 : ∫⁻ ω, ENNReal.ofReal (R ω ^ (p - 2)) ^ (p / (p - 2)) ∂P = A := by
        rw [hA]; congr 1; ext ω
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hR0 ω) _) (by
          apply div_nonneg <;> linarith), ← Real.rpow_mul (hR0 ω)]
        congr 2; field_simp
      have e2 : ∫⁻ ω, ENNReal.ofReal (S2 ω) ^ (p / 2) ∂P = Y := by
        rw [hY]; congr 1; ext ω
        rw [ENNReal.ofReal_rpow_of_nonneg (hS0 ω) (by linarith)]
      simp_rw [e0]
      refine this.trans (le_of_eq ?_)
      rw [e1, e2]
      congr 2
      · field_simp
      · field_simp
  have hchain : A ≤ (ENNReal.ofReal ((p / (p - 1)) ^ p) * ENNReal.ofReal (p * (p - 1)) * Y ^ (2 / p))
      * A ^ (1 - 2 / p) := by
    calc A ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) *
          ∫⁻ ω, ENNReal.ofReal (|∑ j ∈ Finset.range N, ξ j ω| ^ p) ∂P := hdoob
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * (ENNReal.ofReal (p * (p - 1)) *
          ∫⁻ ω, ENNReal.ofReal (R ω ^ (p - 2) * S2 ω) ∂P) := by gcongr
      _ ≤ ENNReal.ofReal ((p / (p - 1)) ^ p) * (ENNReal.ofReal (p * (p - 1)) *
          (A ^ (1 - 2 / p) * Y ^ (2 / p))) := by gcongr
      _ = _ := by ring
  have hab := d42_absorb' A _ (2 / p) (by positivity) (by rw [div_le_one hp0]; exact hp) hAfin hchain
  refine hab.trans (le_of_eq ?_)
  have hK : 0 ≤ (p / (p - 1)) ^ p := by
    apply Real.rpow_nonneg; apply div_nonneg <;> linarith
  have hc : 0 ≤ p * (p - 1) := by nlinarith
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    show 2 / p * (1 / (2 / p)) = 1 by field_simp, show 1 / (2 / p) = p / 2 by field_simp,
    ENNReal.rpow_one, ← ENNReal.ofReal_mul hK,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  rfl




lemma d42_norm_le_sum {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ₑ ≤ ∑ j, ‖v j‖ₑ := by
  have h : ‖v‖ ≤ ∑ j, ‖v j‖ := by
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ j, ‖v j‖ ^ 2) ≤ Real.sqrt ((∑ j, ‖v j‖) ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _)
      _ = ∑ j, ‖v j‖ := Real.sqrt_sq (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  rw [← ofReal_norm_eq_enorm]
  calc ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (∑ j, ‖v j‖) := ENNReal.ofReal_le_ofReal h
    _ = ∑ j, ‖v j‖ₑ := by
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
      exact Finset.sum_congr rfl fun j _ => ofReal_norm_eq_enorm _

lemma d42_enorm_rpow (x : ℝ) (q : ℝ) (hq : 0 ≤ q) : ‖x‖ₑ ^ q = ENNReal.ofReal (|x| ^ q) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq]

/-- vector-valued Burkholder inequality. -/
theorem d42_burk_vec (d : ℕ) {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (V : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ i, StronglyMeasurable[ℱ (i + 1)] (V i)) (hint : ∀ i, Integrable (V i) P)
    (hce : ∀ i, P[V i | ℱ i] =ᵐ[P] 0) (q : ℝ) (hq : 2 ≤ q) (N : ℕ) :
    ∫⁻ ω, (Finset.range (N + 1)).sup (fun k => ‖∑ i ∈ Finset.range k, V i ω‖ₑ ^ q) ∂P ≤
      ENNReal.ofReal (((d : ℝ) + 1) ^ q * d42C q) *
        ∫⁻ ω, (∑ i ∈ Finset.range N, ‖V i ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P := by
  have hq0 : 0 < q := by linarith
  have hC : 0 < ((d : ℝ) + 1) ^ q * d42C q := by
    have := d42C_pos q hq; positivity
  set Y := ∫⁻ ω, (∑ i ∈ Finset.range N, ‖V i ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P with hY
  by_cases hYtop : Y = ⊤
  · rw [hYtop, ENNReal.mul_top (by simpa using hC)]; exact le_top
  have hVm : ∀ i, StronglyMeasurable (V i) := fun i => (hm i).mono (ℱ.le _)
  -- coordinates
  set ξ : Fin d → ℕ → Ω → ℝ := fun j i ω => V i ω j with hξ
  have e : ∀ j i, ξ j i = fun ω => (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (V i ω) := by
    intro j i; funext ω; simp [hξ]
  have hξm : ∀ j i, StronglyMeasurable[ℱ (i + 1)] (ξ j i) := fun j i => by
    rw [e]; exact (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_stronglyMeasurable (hm i)
  have hξi : ∀ j i, Integrable (ξ j i) P := fun j i => by
    rw [e]; exact (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integrable_comp (hint i)
  have hξc : ∀ j i, P[ξ j i | ℱ i] =ᵐ[P] 0 := by
    intro j i
    have h1 := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).comp_condExp_comm
      (m := ℱ i) (hint i)
    have e : (⇑(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) ∘ V i) = ξ j i := by
      funext ω; simp [hξ]
    rw [e] at h1
    refine h1.symm.trans ?_
    filter_upwards [hce i] with ω hω
    simp [hω]
  have hpt : ∀ j i ω, ‖ξ j i ω‖ₑ ≤ ‖V i ω‖ₑ := fun j i ω => PiLp.enorm_apply_le _ _
  have hYle : ∀ i < N, ∀ ω, ‖V i ω‖ₑ ^ q ≤
      (∑ i ∈ Finset.range N, ‖V i ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) := by
    intro i hi ω
    calc ‖V i ω‖ₑ ^ q = (‖V i ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) := by
          rw [← ENNReal.rpow_mul]; congr 1; ring
      _ ≤ _ := ENNReal.rpow_le_rpow (Finset.single_le_sum (f := fun i => ‖V i ω‖ₑ ^ (2 : ℝ))
          (fun _ _ => zero_le) (Finset.mem_range.2 hi)) (by positivity)
  have hLp : ∀ j, ∀ i < N, MemLp (ξ j i) (ENNReal.ofReal q) P := by
    intro j i hi
    refine ⟨(hξi j i).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by simpa using hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) (lt_top_iff_ne_top.2 hYtop)
    exact (ENNReal.rpow_le_rpow (hpt j i ω) hq0.le).trans (hYle i hi ω)
  -- apply the real inequality coordinatewise
  have hreal := fun j => d42_burk_real P ℱ (ξ j) (hξm j) (hξi j) (hξc j) q hq N (hLp j)
  set Rj : Fin d → Ω → ℝ := fun j ω => (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
    fun k => |∑ i ∈ Finset.range k, ξ j i ω| with hRj
  have hS : ∀ j ω, ENNReal.ofReal ((∑ i ∈ Finset.range N, ξ j i ω ^ 2) ^ (q / 2)) ≤
      (∑ i ∈ Finset.range N, ‖V i ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) := by
    intro j ω
    rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
    refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    rw [← sq_abs, ← Real.rpow_two, ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      ← Real.enorm_eq_ofReal_abs]
    exact ENNReal.rpow_le_rpow (hpt j i ω) (by norm_num)
  have hRmeas : ∀ j, Measurable (Rj j) := fun j => Finset.measurable_range_sup'' fun k _ =>
    continuous_abs.measurable.comp (d42_smeas_sum (ξ j) k fun i _ =>
      (hξm j i).mono (ℱ.le _)).measurable
  -- pointwise bound
  have hpw : ∀ ω, (Finset.range (N + 1)).sup (fun k => ‖∑ i ∈ Finset.range k, V i ω‖ₑ ^ q) ≤
      ((Finset.univ : Finset (Fin d)).card : ℝ≥0∞) ^ (q - 1) *
        ∑ j, ENNReal.ofReal (Rj j ω ^ q) := by
    intro ω
    refine Finset.sup_le fun k hk => ?_
    calc ‖∑ i ∈ Finset.range k, V i ω‖ₑ ^ q
        ≤ (∑ j, ‖(∑ i ∈ Finset.range k, V i ω) j‖ₑ) ^ q :=
          ENNReal.rpow_le_rpow (d42_norm_le_sum _) hq0.le
      _ ≤ ((Finset.univ : Finset (Fin d)).card : ℝ≥0∞) ^ (q - 1) *
          ∑ j, ‖(∑ i ∈ Finset.range k, V i ω) j‖ₑ ^ q :=
          ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ (by linarith)
      _ ≤ _ := by
          gcongr with j
          rw [d42_enorm_rpow _ _ hq0.le]
          refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) ?_ hq0.le)
          have : (∑ i ∈ Finset.range k, V i ω) j = ∑ i ∈ Finset.range k, ξ j i ω := by simp [hξ]
          rw [this]
          exact Finset.le_sup' (fun k => |∑ i ∈ Finset.range k, ξ j i ω|) hk
  calc ∫⁻ ω, (Finset.range (N + 1)).sup (fun k => ‖∑ i ∈ Finset.range k, V i ω‖ₑ ^ q) ∂P
      ≤ ∫⁻ ω, ((Finset.univ : Finset (Fin d)).card : ℝ≥0∞) ^ (q - 1) *
        ∑ j, ENNReal.ofReal (Rj j ω ^ q) ∂P := lintegral_mono hpw
    _ = ((Finset.univ : Finset (Fin d)).card : ℝ≥0∞) ^ (q - 1) *
        ∑ j, ∫⁻ ω, ENNReal.ofReal (Rj j ω ^ q) ∂P := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (ENNReal.natCast_ne_top _)), lintegral_finsetSum (f := fun j ω => ENNReal.ofReal (Rj j ω ^ q))
          _ fun j _ => ENNReal.measurable_ofReal.comp ((hRmeas j).pow_const _)]
    _ ≤ ((Finset.univ : Finset (Fin d)).card : ℝ≥0∞) ^ (q - 1) *
        ∑ _j : Fin d, ENNReal.ofReal (d42C q) * Y := by
        gcongr with j
        exact (hreal j).trans (mul_le_mul_right (lintegral_mono fun ω => hS j ω) _)
    _ ≤ ENNReal.ofReal (((d : ℝ) + 1) ^ q * d42C q) * Y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ← mul_assoc]
        gcongr
        have hd1 : ((d : ℝ≥0∞)) ^ (q - 1) ≤ ENNReal.ofReal (((d : ℝ) + 1) ^ (q - 1)) := by
          rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith)]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith))
        have hd2 : (d : ℝ≥0∞) ≤ ENNReal.ofReal ((d : ℝ) + 1) := by
          rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (by linarith)
        calc (d : ℝ≥0∞) ^ (q - 1) * (d : ℝ≥0∞) * ENNReal.ofReal (d42C q)
            ≤ ENNReal.ofReal (((d : ℝ) + 1) ^ (q - 1)) * ENNReal.ofReal ((d : ℝ) + 1) *
              ENNReal.ofReal (d42C q) := by gcongr
          _ = ENNReal.ofReal (((d : ℝ) + 1) ^ q * d42C q) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [← Real.rpow_add_one (by positivity)]
            ring_nf




/-- shifted filtration -/
def d42_shift {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) (n : ℕ) :
    Filtration ℕ m0 :=
  ⟨fun i => ℱ (n + i), fun a b h => ℱ.mono (by omega), fun i => ℱ.le _⟩

lemma d42_enorm_smul_sq {d : ℕ} (x : ℝ) (V : EuclideanSpace ℝ (Fin d)) :
    ‖x • V‖ₑ ^ (2:ℝ) = ENNReal.ofReal (x ^ 2) * ‖V‖ₑ ^ (2:ℝ) := by
  rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1; rw [Real.rpow_two, sq_abs]

/-- Burkholder for weighted Robbins–Monro noise on a block `[n, m)`, with general deterministic
weights `w`. -/
theorem d42_block (d : ℕ) {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (U : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hUm : ∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (U (n + 1)))
    (hUi : ∀ n : ℕ, Integrable (U (n + 1)) P) (hUc : ∀ n : ℕ, P[U (n + 1) | ℱ n] =ᵐ[P] 0)
    (w : ℕ → ℝ) (q : ℝ) (hq : 2 ≤ q) (n m : ℕ) :
    ∫⁻ ω, (Finset.Ioc n m).sup
        (fun k => ‖∑ i ∈ Finset.Ico n k, w (i + 1) • U (i + 1) ω‖ₑ ^ q) ∂P
      ≤ ENNReal.ofReal (((d : ℝ) + 1) ^ q * d42C q) *
        ∫⁻ ω, (∑ i ∈ Finset.Ico n m,
          ENNReal.ofReal (w (i + 1) ^ 2) * ‖U (i + 1) ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P := by
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun i ω => w (n + i + 1) • U (n + i + 1) ω with hV
  have hVm : ∀ i, StronglyMeasurable[d42_shift ℱ n (i + 1)] (V i) := by
    intro i
    have h := (hUm (n + i)).const_smul (w (n + i + 1))
    exact h
  have hVi : ∀ i, Integrable (V i) P := fun i => (hUi (n + i)).smul (w (n + i + 1))
  have hVc : ∀ i, P[V i | d42_shift ℱ n i] =ᵐ[P] 0 := by
    intro i
    have h1 := condExp_smul (μ := P) (w (n + i + 1)) (U (n + i + 1)) (ℱ (n + i))
    refine h1.trans ?_
    filter_upwards [hUc (n + i)] with ω hω
    simp [hω]
  have hvec := d42_burk_vec d P (d42_shift ℱ n) V hVm hVi hVc q hq (m - n)
  refine le_trans (lintegral_mono fun ω => ?_) (hvec.trans (le_of_eq ?_))
  · refine Finset.sup_le fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.1 hk
    have e : ∑ i ∈ Finset.Ico n k, w (i + 1) • U (i + 1) ω = ∑ i ∈ Finset.range (k - n), V i ω := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [e]
    exact Finset.le_sup (f := fun k => ‖∑ i ∈ Finset.range k, V i ω‖ₑ ^ q)
      (Finset.mem_range.2 (by omega))
  · congr 1
    congr 1; funext ω
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hV]; simp only
    rw [d42_enorm_smul_sq]


theorem burkholder_eq13_core (d : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        IsRobbinsMonro P ℱ F γ x U →
        ∀ (n : ℕ) (T : ℝ), 0 < T →
          ∫⁻ ω, (Finset.Ioc n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T))).sup
              (fun k => ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω‖ₑ ^ q) ∂P
            ≤ ENNReal.ofReal C *
              ∫⁻ ω, (∑ i ∈ Finset.Ico n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
                  ENNReal.ofReal (γ (i + 1) ^ 2) * ‖U (i + 1) ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P := by
  refine ⟨((d : ℝ) + 1) ^ q * d42C q, by have := d42C_pos q hq; positivity, ?_⟩
  intro Ω m0 P _ ℱ F γ x U hRM n T _
  exact d42_block d P ℱ U hRM.2.2.2.1 hRM.2.2.2.2.1 hRM.2.2.2.2.2 γ q hq n _


end StochApproxDyn.MartingaleNoise

open StochApproxDyn.MartingaleNoise


theorem solution (d : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        IsRobbinsMonro P ℱ F γ x U →
        ∀ (n : ℕ) (T : ℝ), 0 < T →
          ∫⁻ ω, (Finset.Ioc n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T))).sup
              (fun k => ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω‖ₑ ^ q) ∂P
            ≤ ENNReal.ofReal C *
              ∫⁻ ω, (∑ i ∈ Finset.Ico n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
                  ENNReal.ofReal (γ (i + 1) ^ 2) * ‖U (i + 1) ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P := by
  exact burkholder_eq13_core d q hq
