-- Prove2me | solution 1 for PooledRationing.MaxWeighted.path_martingale_slln
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:37:19.532019+00:00
-- url     : https://prove2.me/submissions/a09e5df5-b601-4410-8ed4-2498d2f3a86a

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace MWSllnAux

/-- Hoeffding's lemma in lintegral form. -/
theorem hoeff {E : Type*} [MeasurableSpace E] (F : Measure E) [IsProbabilityMeasure F]
    (S : Set E) (hFS : ∀ᵐ x ∂F, x ∈ S) (G : E → ℝ) (hG : Measurable G) (M : ℝ)
    (hb : ∀ x ∈ S, |G x| ≤ M) (hc : ∫ x, G x ∂F = 0) (l : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (l * G x)) ∂F ≤ ENNReal.ofReal (Real.exp (l ^ 2 * M ^ 2 / 2)) := by
  have hbd : ∀ᵐ x ∂F, G x ∈ Set.Icc (-M) M := by
    filter_upwards [hFS] with x hx
    exact abs_le.mp (hb x hx)
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hG.aemeasurable hbd hc
  have hmgf := h.mgf_le l
  have hint := h.integrable_exp_mul l
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  refine (le_of_eq_of_le rfl hmgf).trans (le_of_eq ?_)
  congr 1
  have : ((‖M - -M‖₊ / 2) ^ 2 : NNReal) = (M ^ 2 : ℝ) := by
    push_cast
    rw [Real.norm_eq_abs, show M - -M = 2 * M by ring, abs_mul]
    rw [abs_two, mul_div_cancel_left₀ _ two_ne_zero, sq_abs]
  rw [this]
  ring

/-- `exp (-c T^b)` is summable over `T : ℕ` for `c, b > 0`. -/
theorem summable_exp_neg_rpow (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    Summable (fun T : ℕ => Real.exp (-(c * (T : ℝ) ^ b))) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (2 / b)
  have hkb : (2 : ℝ) ≤ k * b := by
    have := (div_le_iff₀ hb).mp hk
    linarith
  have hsum : Summable (fun T : ℕ => (k.factorial / c ^ k) * (1 / (T : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hsum ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hx : 0 ≤ c * (T : ℝ) ^ b := by positivity
  have hexp := Real.pow_div_factorial_le_exp _ hx k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hpow : (T : ℝ) ^ 2 ≤ ((T : ℝ) ^ b) ^ k := by
    rw [← Real.rpow_natCast ((T : ℝ) ^ b), ← Real.rpow_mul hT0.le]
    rw [show ((T : ℝ) ^ 2) = (T : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
    apply Real.rpow_le_rpow_of_exponent_le hT1
    push_cast; linarith
  rw [Real.exp_neg]
  have hpos : 0 < (c * (T : ℝ) ^ b) ^ k / k.factorial := by
    have : 0 < c * (T : ℝ) ^ b := by positivity
    positivity
  calc (Real.exp (c * (T : ℝ) ^ b))⁻¹ ≤ ((c * (T : ℝ) ^ b) ^ k / k.factorial)⁻¹ :=
        inv_anti₀ hpos hexp
    _ = k.factorial / c ^ k * (1 / ((T : ℝ) ^ b) ^ k) := by
        rw [mul_pow]; field_simp
    _ ≤ k.factorial / c ^ k * (1 / (T : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact one_div_le_one_div_of_le (by positivity) hpow

theorem trunc_meas {E : Type*} [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (Dseq : ℕ → Ω → E) (hDmeas : ∀ t, Measurable (Dseq t)) (x0 : E) (n : ℕ) :
    Measurable (fun ω (k : ℕ) => if k ∈ Finset.range n then Dseq k ω else x0) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases h : k ∈ Finset.range n
  · simp only [h, if_true]; exact hDmeas k
  · simp only [h, if_false]; exact measurable_const

/-- The exponential-moment bound for a path functional martingale. -/
theorem mgf_path {E : Type*} [MeasurableSpace E] (F : Measure E) [IsProbabilityMeasure F]
    (S : Set E) (hFS : ∀ᵐ x ∂F, x ∈ S) (x0 : E) (hx0 : x0 ∈ S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → E) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (hDS : ∀ t ω, Dseq t ω ∈ S)
    (Y : ℕ → (ℕ → E) → ℝ) (hYmeas : ∀ t, Measurable (Y t))
    (hYloc : ∀ t (d d' : ℕ → E), (∀ s ≤ t, d s = d' s) → Y t d = Y t d')
    (M : ℝ) (hYbdd : ∀ t (d : ℕ → E), (∀ s, d s ∈ S) → |Y t d| ≤ M)
    (hYcent : ∀ t (d : ℕ → E), (∀ s, d s ∈ S) → ∫ x, Y t (Function.update d t x) ∂F = 0)
    (l : ℝ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω))) ∂μ
      ≤ ENNReal.ofReal (Real.exp (l ^ 2 * M ^ 2 / 2)) ^ n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    set c := ENNReal.ofReal (Real.exp (l ^ 2 * M ^ 2 / 2)) with hcdef
    set trunc : Ω → ℕ → E := fun ω k => if k ∈ Finset.range n then Dseq k ω else x0 with htr
    have htrunc_meas : Measurable trunc := trunc_meas Dseq hDmeas x0 n
    let φ1 : ((Finset.range n) → E) → ℕ → E := fun v k =>
      if h : k ∈ Finset.range n then v ⟨k, h⟩ else x0
    have hφ1 : Measurable φ1 := by
      refine measurable_pi_lambda _ fun k => ?_
      by_cases h : k ∈ Finset.range n
      · simp only [φ1, h, dif_pos]; exact measurable_pi_apply _
      · simp only [φ1, h, dif_neg, not_false_eq_true]; exact measurable_const
    have hind0 := hindep.indepFun_finset (Finset.range n) {n} (by simp) hDmeas
    have hind1 := hind0.comp hφ1
      (measurable_pi_apply (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ)))
    have hcomp : (φ1 ∘ fun ω (i : Finset.range n) => Dseq i ω) = trunc := by
      funext ω k
      simp only [Function.comp, φ1, htr]
      by_cases h : k ∈ Finset.range n
      · simp [h]
      · simp [h]
    rw [hcomp] at hind1
    have hind : IndepFun trunc (Dseq n) μ := hind1
    have hmap : μ.map (fun ω => (trunc ω, Dseq n ω)) = (μ.map trunc).prod F := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map htrunc_meas.aemeasurable
        (hDmeas n).aemeasurable).mp hind, hlaw n]
    set A : (ℕ → E) → ℝ := fun h => ∑ t ∈ Finset.range n, Y t h with hA
    have hAm : Measurable A := Finset.measurable_sum _ fun t _ => hYmeas t
    set Φ : (ℕ → E) × E → ENNReal := fun p =>
      ENNReal.ofReal (Real.exp (l * A p.1)) *
        ENNReal.ofReal (Real.exp (l * Y n (Function.update p.1 n p.2))) with hΦdef
    have hΦ : Measurable Φ := by
      have h1 : Measurable (fun p : (ℕ → E) × E => ENNReal.ofReal (Real.exp (l * A p.1))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul (hAm.comp measurable_fst)))
      have h2 : Measurable (fun p : (ℕ → E) × E =>
          ENNReal.ofReal (Real.exp (l * Y n (Function.update p.1 n p.2)))) :=
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (measurable_const.mul ((hYmeas n).comp measurable_update')))
      exact h1.mul h2
    have htrS : ∀ ω s, trunc ω s ∈ S := by
      intro ω s
      simp only [htr]
      split_ifs
      · exact hDS s ω
      · exact hx0
    have hupdS : ∀ ω x, x ∈ S → ∀ s, Function.update (trunc ω) n x s ∈ S := by
      intro ω x hx s
      by_cases hs : s = n
      · subst hs; simp [hx]
      · rw [Function.update_of_ne hs]; exact htrS ω s
    have hAeq : ∀ ω, A (trunc ω) = A (fun k => Dseq k ω) := by
      intro ω
      refine Finset.sum_congr rfl fun t ht => hYloc t _ _ fun s hs => ?_
      have : s ∈ Finset.range n := by
        simp only [Finset.mem_range] at ht ⊢; omega
      show (if s ∈ Finset.range n then Dseq s ω else x0) = Dseq s ω
      rw [if_pos this]
    have hYeq : ∀ ω, Y n (fun k => Dseq k ω) = Y n (Function.update (trunc ω) n (Dseq n ω)) := by
      intro ω
      refine hYloc n _ _ fun s hs => ?_
      by_cases h : s = n
      · subst h; simp
      · rw [Function.update_of_ne h]
        have : s ∈ Finset.range n := by
          simp only [Finset.mem_range]; omega
        show Dseq s ω = (if s ∈ Finset.range n then Dseq s ω else x0)
        rw [if_pos this]
    have step1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range (n + 1),
        Y t (fun k => Dseq k ω))) ∂μ = ∫⁻ ω, Φ (trunc ω, Dseq n ω) ∂μ := by
      refine lintegral_congr fun ω => ?_
      simp only [hΦdef]
      rw [Finset.sum_range_succ, mul_add, Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_pos _).le, hAeq, hYeq]
    rw [step1, ← lintegral_map hΦ (htrunc_meas.prodMk (hDmeas n)), hmap,
      lintegral_prod _ hΦ.aemeasurable,
      lintegral_map (hΦ.lintegral_prod_right') htrunc_meas]
    calc ∫⁻ ω, ∫⁻ x, Φ (trunc ω, x) ∂F ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (l * A (trunc ω))) * c ∂μ := by
          refine lintegral_mono fun ω => ?_
          simp only [hΦdef]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact hoeff F S hFS (fun x => Y n (Function.update (trunc ω) n x))
            ((hYmeas n).comp (measurable_update _)) M
            (fun x hx => hYbdd n _ (hupdS ω x hx)) (hYcent n (trunc ω) (htrS ω)) l
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (l * A (fun k => Dseq k ω))) ∂μ) * c := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr fun ω => by rw [hAeq]
      _ ≤ c ^ n * c := by gcongr
      _ = c ^ (n + 1) := (pow_succ c n).symm

/-- One-sided Chernoff bound for a path functional martingale. -/
theorem tail_path {E : Type*} [MeasurableSpace E] (F : Measure E) [IsProbabilityMeasure F]
    (S : Set E) (hFS : ∀ᵐ x ∂F, x ∈ S) (x0 : E) (hx0 : x0 ∈ S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → E) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (hDS : ∀ t ω, Dseq t ω ∈ S)
    (Y : ℕ → (ℕ → E) → ℝ) (hYmeas : ∀ t, Measurable (Y t))
    (hYloc : ∀ t (d d' : ℕ → E), (∀ s ≤ t, d s = d' s) → Y t d = Y t d')
    (M : ℝ) (hM : 0 < M) (hYbdd : ∀ t (d : ℕ → E), (∀ s, d s ∈ S) → |Y t d| ≤ M)
    (hYcent : ∀ t (d : ℕ → E), (∀ s, d s ∈ S) → ∫ x, Y t (Function.update d t x) ∂F = 0)
    (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω)}
      ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2 / (2 * n * M ^ 2)))) := by
  have hpath : Measurable (fun ω (k : ℕ) => Dseq k ω) := measurable_pi_lambda _ hDmeas
  have hX : Measurable (fun ω => ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω)) :=
    Finset.measurable_sum _ fun t _ => (hYmeas t).comp hpath
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set l := ε / (n * M ^ 2) with hl
  have hl0 : 0 ≤ l := by positivity
  have hs : MeasurableSet {ω | ε ≤ ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω)} :=
    measurableSet_le measurable_const hX
  have hmgf := mgf_path F S hFS x0 hx0 μ Dseq hDmeas hindep hlaw hDS Y hYmeas hYloc M hYbdd
    hYcent l n
  calc μ {ω | ε ≤ ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω)}
      = ∫⁻ ω, {ω | ε ≤ ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω)}.indicator 1 ω ∂μ :=
        (lintegral_indicator_one hs).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-(l * ε))) *
          ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω))) ∂μ := by
        refine lintegral_mono fun ω => ?_
        by_cases h : ω ∈ {ω | ε ≤ ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω)}
        · rw [Set.indicator_of_mem h, Pi.one_apply, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← Real.exp_add]
          apply ENNReal.one_le_ofReal.mpr
          apply Real.one_le_exp
          have : ε ≤ ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω) := h
          nlinarith
        · rw [Set.indicator_of_notMem h]; exact bot_le
    _ = ENNReal.ofReal (Real.exp (-(l * ε))) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ∑ t ∈ Finset.range n, Y t (fun k => Dseq k ω))) ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Real.exp (-(l * ε))) * ENNReal.ofReal (Real.exp (l ^ 2 * M ^ 2 / 2)) ^ n := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-(ε ^ 2 / (2 * n * M ^ 2)))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_nat_mul, ← Real.exp_add]
        congr 2
        rw [hl]
        field_simp
        ring

theorem exponent_eq (ε M a : ℝ) (T : ℕ) (hT : (0 : ℝ) < T) :
    (ε * (T : ℝ) ^ a) ^ 2 / (2 * T * M ^ 2) = ε ^ 2 / (2 * M ^ 2) * (T : ℝ) ^ (2 * a - 1) := by
  rw [Real.rpow_sub_one hT.ne', show 2 * a = a + a by ring, Real.rpow_add hT]
  rcases eq_or_ne M 0 with hM | hM
  · subst hM; simp
  field_simp

theorem slln_core {E : Type*} [MeasurableSpace E] (F : Measure E) [IsProbabilityMeasure F]
    (S : Set E) (hFS : ∀ᵐ x ∂F, x ∈ S) (x0 : E) (hx0 : x0 ∈ S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → E) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (hDS : ∀ t ω, Dseq t ω ∈ S)
    (Z : ℕ → ℕ → (ℕ → E) → ℝ) (hZmeas : ∀ T t, Measurable (Z T t))
    (hZloc : ∀ T t (d d' : ℕ → E), (∀ s ≤ t, d s = d' s) → Z T t d = Z T t d')
    (M : ℝ) (hZbdd : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → |Z T t d| ≤ M)
    (hZcent : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → ∫ x, Z T t (Function.update d t x) ∂F = 0)
    (a : ℝ) (ha : 1 / 2 < a) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => (T : ℝ) ^ (-a) *
      ∑ t ∈ Finset.range T, Z T t (fun k => Dseq k ω)) atTop (𝓝 0) := by
  set M' := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  have hZbdd' : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → |Z T t d| ≤ M' := fun T t d hd =>
    (hZbdd T t d hd).trans (by rw [hM']; linarith [le_abs_self M])
  set X : ℕ → Ω → ℝ := fun T ω => ∑ t ∈ Finset.range T, Z T t (fun k => Dseq k ω) with hXdef
  -- the per-ε statement
  have key : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂μ, ∀ᶠ T : ℕ in atTop,
      ω ∉ {ω | ε ≤ |(T : ℝ) ^ (-a) * X T ω|} := by
    intro ε hε
    apply ae_eventually_notMem
    set c := ε ^ 2 / (2 * M' ^ 2) with hc
    have hcpos : 0 < c := by positivity
    have hb : 0 < 2 * a - 1 := by linarith
    have hsum := summable_exp_neg_rpow c (2 * a - 1) hcpos hb
    have hbound : ∀ T : ℕ, μ {ω | ε ≤ |(T : ℝ) ^ (-a) * X T ω|} ≤
        2 * ENNReal.ofReal (Real.exp (-(c * (T : ℝ) ^ (2 * a - 1)))) := by
      intro T
      rcases Nat.eq_zero_or_pos T with h0 | hTpos
      · subst h0
        have : {ω | ε ≤ |((0 : ℕ) : ℝ) ^ (-a) * X 0 ω|} = ∅ := by
          ext ω; simp [hXdef]; linarith
        rw [this, measure_empty]; exact bot_le
      have hT : (0 : ℝ) < T := by exact_mod_cast hTpos
      have hTa : 0 < (T : ℝ) ^ a := Real.rpow_pos_of_pos hT a
      have hsub : {ω | ε ≤ |(T : ℝ) ^ (-a) * X T ω|} ⊆
          {ω | ε * (T : ℝ) ^ a ≤ ∑ t ∈ Finset.range T, Z T t (fun k => Dseq k ω)} ∪
          {ω | ε * (T : ℝ) ^ a ≤ ∑ t ∈ Finset.range T, (fun t d => -Z T t d) t (fun k => Dseq k ω)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hT _), Real.rpow_neg hT.le,
          ← div_eq_inv_mul, le_div_iff₀ hTa] at hω
        simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib]
        rcases le_abs'.mp hω with h | h
        · right; simp only [hXdef] at h; linarith
        · left; exact h
      have hthr : 0 ≤ ε * (T : ℝ) ^ a := by positivity
      have h1 := tail_path F S hFS x0 hx0 μ Dseq hDmeas hindep hlaw hDS (Z T) (hZmeas T)
        (hZloc T) M' hM'pos (hZbdd' T) (hZcent T) T hTpos _ hthr
      have h2 := tail_path F S hFS x0 hx0 μ Dseq hDmeas hindep hlaw hDS (fun t d => -Z T t d)
        (fun t => (hZmeas T t).neg)
        (fun t d d' h => by simp only [hZloc T t d d' h]) M' hM'pos
        (fun t d hd => by rw [abs_neg]; exact hZbdd' T t d hd)
        (fun t d hd => by rw [integral_neg, hZcent T t d hd, neg_zero]) T hTpos _ hthr
      rw [exponent_eq ε M' a T hT] at h1 h2
      calc μ {ω | ε ≤ |(T : ℝ) ^ (-a) * X T ω|} ≤ _ := measure_mono hsub
        _ ≤ _ := measure_union_le _ _
        _ ≤ _ := add_le_add h1 h2
        _ = 2 * ENNReal.ofReal (Real.exp (-(c * (T : ℝ) ^ (2 * a - 1)))) := (two_mul _).symm
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun T => (Real.exp_pos _).le) hsum]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ T : ℕ in atTop,
      ω ∉ {ω | (1 / ((k : ℝ) + 1)) ≤ |(T : ℝ) ^ (-a) * X T ω|} := by
    rw [ae_all_iff]
    intro k
    exact key _ (by positivity)
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  filter_upwards [hω k] with T hT
  simp only [Set.mem_setOf_eq, not_le] at hT
  rw [Real.dist_eq, sub_zero]
  exact hT.trans hk

end MWSllnAux

open MWSllnAux

theorem solution
    {E : Type*} [MeasurableSpace E] (F : Measure E) [IsProbabilityMeasure F]
    (S : Set E) (hS : MeasurableSet S) (hFS : ∀ᵐ x ∂F, x ∈ S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Dseq : ℕ → Ω → E) (hDmeas : ∀ t, Measurable (Dseq t))
    (hindep : iIndepFun Dseq μ) (hlaw : ∀ t, μ.map (Dseq t) = F)
    (Z : ℕ → ℕ → (ℕ → E) → ℝ) (hZmeas : ∀ T t, Measurable (Z T t))
    (hZloc : ∀ T t (d d' : ℕ → E), (∀ s ≤ t, d s = d' s) → Z T t d = Z T t d')
    (M : ℝ) (hZbdd : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → |Z T t d| ≤ M)
    (hZcent : ∀ T t (d : ℕ → E), (∀ s, d s ∈ S) → ∫ x, Z T t (Function.update d t x) ∂F = 0)
    (a : ℝ) (ha : 1 / 2 < a) :
    ∀ᵐ ω ∂μ, Tendsto (fun T : ℕ => (T : ℝ) ^ (-a) *
      ∑ t ∈ Finset.range T, Z T t (fun k => Dseq k ω)) atTop (𝓝 0) := by
  classical
  obtain ⟨x0, hx0⟩ := hFS.exists
  set g : E → E := S.piecewise id (fun _ => x0) with hgdef
  have hg : Measurable g := Measurable.piecewise hS measurable_id measurable_const
  have hgS : ∀ x, g x ∈ S := by
    intro x
    by_cases hx : x ∈ S
    · simp [hgdef, Set.piecewise_eq_of_mem _ _ _ hx, hx]
    · simp [hgdef, Set.piecewise_eq_of_notMem _ _ _ hx, hx0]
  have hgF : g =ᵐ[F] id := by
    filter_upwards [hFS] with x hx
    simp [hgdef, Set.piecewise_eq_of_mem _ _ _ hx]
  set D' : ℕ → Ω → E := fun t => g ∘ Dseq t with hD'
  have hD'meas : ∀ t, Measurable (D' t) := fun t => hg.comp (hDmeas t)
  have hD'ind : iIndepFun D' μ := hindep.comp (fun _ => g) (fun _ => hg)
  have hD'law : ∀ t, μ.map (D' t) = F := by
    intro t
    rw [hD', ← Measure.map_map hg (hDmeas t), hlaw t, Measure.map_congr hgF, Measure.map_id]
  have hcore := slln_core F S hFS x0 hx0 μ D' hD'meas hD'ind hD'law (fun t ω => hgS _) Z hZmeas
    hZloc M hZbdd hZcent a ha
  have heq : ∀ᵐ ω ∂μ, ∀ t, D' t ω = Dseq t ω := by
    rw [ae_all_iff]
    intro t
    have h1 : ∀ᵐ x ∂(μ.map (Dseq t)), g x = x := by rw [hlaw t]; exact hgF
    exact ae_of_ae_map (hDmeas t).aemeasurable h1
  filter_upwards [hcore, heq] with ω hω he
  have : (fun k => D' k ω) = (fun k => Dseq k ω) := funext he
  simpa only [this] using hω
