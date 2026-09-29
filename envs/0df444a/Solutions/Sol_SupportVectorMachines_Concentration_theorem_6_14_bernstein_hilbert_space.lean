-- Prove2me | solution 1 for SupportVectorMachines.Concentration.theorem_6_14_bernstein_hilbert_space
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T07:00:46.984712+00:00
-- url     : https://prove2.me/submissions/da96fe94-da93-4024-a6e3-62cfdce8f97d

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace SupportVectorMachines.Concentration

lemma two_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => simp [Nat.factorial]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ, pow_succ]
    nlinarith

lemma exp_le_quad_pos {u : ℝ} (h0 : 0 ≤ u) (h3 : u < 3) :
    Real.exp u ≤ 1 + u + u ^ 2 / (2 * (1 - u / 3)) := by
  have hs := Real.summable_pow_div_factorial u
  have hexp : Real.exp u = ∑' k, u ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  have hsplit := hs.sum_add_tsum_nat_add 2
  have hr : 0 ≤ u / 3 := by positivity
  have hr1 : u / 3 < 1 := by linarith
  have hgs : Summable fun k : ℕ => u ^ 2 / 2 * (u / 3) ^ k :=
    (summable_geometric_of_lt_one hr hr1).mul_left _
  have hterm : ∀ k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ u ^ 2 / 2 * (u / 3) ^ k := by
    intro k
    have hf : (2 * 3 ^ k : ℝ) ≤ ((k + 2).factorial : ℝ) := by
      exact_mod_cast two_three_pow_le_factorial k
    have hpos : (0 : ℝ) < 2 * 3 ^ k := by positivity
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((k + 2).factorial : ℝ))]
    calc u ^ (k + 2) = u ^ 2 / 2 * (u / 3) ^ k * (2 * 3 ^ k) := by
          rw [div_pow]; field_simp; ring
      _ ≤ u ^ 2 / 2 * (u / 3) ^ k * ((k + 2).factorial : ℝ) :=
          mul_le_mul_of_nonneg_left hf (by positivity)
  have hle := (hs.comp_injective (add_left_injective 2)).tsum_le_tsum hterm hgs
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1] at hle
  rw [hexp, ← hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one]
  have e : u ^ 2 / 2 * (1 - u / 3)⁻¹ = u ^ 2 / (2 * (1 - u / 3)) := by
    field_simp
  have : ∑' k : ℕ, u ^ (k + 2) / ((k + 2).factorial : ℝ) ≤ u ^ 2 / (2 * (1 - u / 3)) := by
    rw [← e]; exact hle
  linarith

lemma exp_le_quad_neg {x : ℝ} (hx : x ≤ 0) : Real.exp x ≤ 1 + x + x ^ 2 / 2 := by
  have hanti : AntitoneOn (fun y => 1 + y + y ^ 2 / 2 - Real.exp y) (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact (by fun_prop : Continuous fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y).continuousOn
    · exact (by fun_prop : Differentiable ℝ fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
        |>.differentiableOn
    · intro y hy
      rw [interior_Iic] at hy
      have hd : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2 - Real.exp y)
          (1 + y - Real.exp y) y := by
        have := ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
          ((hasDerivAt_pow 2 y).div_const 2)).sub (Real.hasDerivAt_exp y))
        refine this.congr_deriv ?_
        simp only [Nat.cast_ofNat, id]
        ring
      rw [hd.deriv]
      linarith [Real.add_one_le_exp y]
  have := hanti hx (Set.mem_Iic.mpr le_rfl) hx
  simp at this
  linarith

lemma exp_le_quad {x c : ℝ} (hc0 : 0 ≤ c) (hc3 : c < 3) (hx : x ≤ c) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - c / 3)) := by
  have hden : 0 < 2 * (1 - c / 3) := by linarith
  rcases le_or_gt x 0 with hneg | hpos
  · have h1 := exp_le_quad_neg hneg
    have h2 : x ^ 2 / 2 ≤ x ^ 2 / (2 * (1 - c / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) hden
      linarith
    linarith
  · have h1 := exp_le_quad_pos hpos.le (by linarith)
    have h2 : x ^ 2 / (2 * (1 - x / 3)) ≤ x ^ 2 / (2 * (1 - c / 3)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg x) hden
      linarith
    linarith

/-- one-step exponential bound for a bounded real variable (no centering assumption). -/
lemma step_scalar {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (a : Ω' → ℝ) (ha : Measurable a) (B σ : ℝ) (hbound : ∀ᵐ y ∂ν, |a y| ≤ B)
    (hvar : ∫ y, (a y) ^ 2 ∂ν ≤ σ ^ 2) (lam : ℝ) (hl0 : 0 ≤ lam) (hl3 : lam * B < 3) :
    ∫ y, Real.exp (lam * (a y - ∫ z, a z ∂ν)) ∂ν ≤
      Real.exp (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))) := by
  have hB0 : 0 ≤ B := by
    obtain ⟨ω, hω⟩ := hbound.exists
    exact (abs_nonneg _).trans hω
  have hc0 : 0 ≤ lam * B := mul_nonneg hl0 hB0
  have hden : 0 < 2 * (1 - lam * B / 3) := by linarith
  have hXint : Integrable a ν :=
    Integrable.of_bound ha.aestronglyMeasurable B (by
      filter_upwards [hbound] with ω hω; rwa [Real.norm_eq_abs])
  have hX2int : Integrable (fun ω => (a ω) ^ 2) ν :=
    Integrable.of_bound (ha.pow_const 2).aestronglyMeasurable (B ^ 2) (by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
  have hEint : Integrable (fun ω => Real.exp (lam * a ω)) ν :=
    Integrable.of_bound (by fun_prop) (Real.exp (lam * B)) (by
      filter_upwards [hbound] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) hl0)
  set m := ∫ z, a z ∂ν with hm
  set K := 1 / (2 * (1 - lam * B / 3)) with hK
  have hpt : ∀ᵐ ω ∂ν, Real.exp (lam * a ω) ≤ 1 + lam * a ω + K * lam ^ 2 * (a ω) ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hx : lam * a ω ≤ lam * B := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hω) hl0
    have := exp_le_quad hc0 hl3 hx
    rw [hK]
    calc Real.exp (lam * a ω) ≤ 1 + lam * a ω + (lam * a ω) ^ 2 / (2 * (1 - lam * B / 3)) := this
      _ = _ := by field_simp
  have hA : Integrable (fun ω => 1 + lam * a ω) ν := (integrable_const 1).add (hXint.const_mul lam)
  have hB2 : Integrable (fun ω => K * lam ^ 2 * (a ω) ^ 2) ν := hX2int.const_mul (K * lam ^ 2)
  have hint2 : Integrable (fun ω => 1 + lam * a ω + K * lam ^ 2 * (a ω) ^ 2) ν := hA.add hB2
  have hmono := integral_mono_ae hEint hint2 hpt
  have hL : Integrable (fun ω => lam * a ω) ν := hXint.const_mul lam
  rw [integral_add hA hB2, integral_add (integrable_const 1) hL, integral_const_mul,
    integral_const_mul] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  set c := lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) with hcdef
  have hK0 : 0 ≤ K * lam ^ 2 := by rw [hK]; positivity
  have h2 : K * lam ^ 2 * ∫ ω, (a ω) ^ 2 ∂ν ≤ c := by
    have := mul_le_mul_of_nonneg_left hvar hK0
    have e : K * lam ^ 2 * σ ^ 2 = c := by rw [hK, hcdef]; field_simp
    linarith
  have hE : ∫ ω, Real.exp (lam * a ω) ∂ν ≤ 1 + lam * m + c := by linarith
  have hsplit : ∫ y, Real.exp (lam * (a y - m)) ∂ν =
      Real.exp (-(lam * m)) * ∫ y, Real.exp (lam * a y) ∂ν := by
    rw [← integral_const_mul]
    congr 1; funext y
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  calc Real.exp (-(lam * m)) * ∫ y, Real.exp (lam * a y) ∂ν
      ≤ Real.exp (-(lam * m)) * (1 + lam * m + c) :=
        mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
    _ ≤ Real.exp (-(lam * m)) * Real.exp (lam * m + c) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (lam * m + c)])
          (Real.exp_pos _).le
    _ = Real.exp c := by rw [← Real.exp_add]; ring_nf

section Pair

variable {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [MeasurableSpace H]

lemma indep_lintegral (P : Measure Ω) [IsProbabilityMeasure P] {T Y : Ω → H}
    (hT : Measurable T) (hY : Measurable Y) (hind : IndepFun T Y P)
    (g : H × H → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, g (T ω, Y ω) ∂P = ∫⁻ x, ∫⁻ y, g (x, y) ∂(P.map Y) ∂(P.map T) := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hY.aemeasurable).1 hind
  have := lintegral_map hg (hT.prodMk hY) (μ := P)
  rw [← this, hmap, lintegral_prod _ hg.aemeasurable]

lemma indep_integral (P : Measure Ω) [IsProbabilityMeasure P] {T Y : Ω → H}
    (hT : Measurable T) (hY : Measurable Y) (hind : IndepFun T Y P)
    (g : H × H → ℝ) (hg : Integrable g ((P.map T).prod (P.map Y))) :
    ∫ ω, g (T ω, Y ω) ∂P = ∫ x, ∫ y, g (x, y) ∂(P.map Y) ∂(P.map T) := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hY.aemeasurable).1 hind
  rw [← hmap] at hg
  have := integral_map (hT.prodMk hY).aemeasurable hg.aestronglyMeasurable
  rw [← this, hmap, integral_prod _ (hmap ▸ hg)]

end Pair


section Conc

variable {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H]

lemma conc_induct {ι : Type*} [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ι → Ω → H) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P) (B σ : ℝ)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B) (hvar : ∀ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ σ ^ 2)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl3 : lam * B < 3) (s : Finset ι) :
    ∀ f : H → ℝ, LipschitzWith 1 f →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (f (∑ i ∈ s, ξ i ω) -
          ∫ ω', f (∑ i ∈ s, ξ i ω') ∂P))) ∂P ≤
        ENNReal.ofReal (Real.exp (s.card * (lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3))))) := by
  have hξint : ∀ i, Integrable (ξ i) P := fun i =>
    Integrable.of_bound (hmeas i).aestronglyMeasurable B (hbound i)
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | insert j s hj ih =>
    intro f hf
    set c := lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) with hc
    set T : Ω → H := fun ω => ∑ i ∈ s, ξ i ω with hTdef
    set Y := ξ j with hYdef
    have hTm : Measurable T := Finset.measurable_sum s (fun i _ => hmeas i)
    have hYm : Measurable Y := hmeas j
    have hind : IndepFun T Y P := by
      have := hindep.indepFun_finsetSum_of_notMem hmeas hj
      rw [Finset.sum_fn] at this
      exact this
    have hTint : Integrable (fun ω => ‖T ω‖) P := by
      refine (integrable_finset_sum s (fun i _ => (hξint i).norm)).mono' hTm.norm.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      simpa [T] using norm_sum_le s (fun i => ξ i ω)
    have hfc : Continuous f := hf.continuous
    have hfle : ∀ x y, |f x - f y| ≤ ‖x - y‖ := fun x y => by
      have := hf.dist_le_mul x y; simpa [Real.dist_eq, dist_eq_norm] using this
    have hfY : ∀ x, Integrable (fun ω => f (x + Y ω)) P := by
      intro x
      refine ((integrable_const (|f x|)).add (hξint j).norm).mono'
        (hfc.measurable.comp (measurable_const.add hYm)).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      have := hfle (x + Y ω) x
      rw [add_sub_cancel_left] at this
      rw [Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (f (x + Y ω)) (f x)
      have : |f x| ≥ -|f x| := by linarith [abs_nonneg (f x)]
      simp only [Pi.add_apply]
      linarith [abs_sub_abs_le_abs_sub (f (x + Y ω)) (f x), hfle (x + Y ω) x,
        show ‖x + Y ω - x‖ = ‖Y ω‖ by rw [add_sub_cancel_left]]
    set h : H → ℝ := fun x => ∫ ω, f (x + Y ω) ∂P with hhdef
    have hh : LipschitzWith 1 h := by
      refine LipschitzWith.of_dist_le_mul fun x x' => ?_
      simp only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
      rw [hhdef, ← integral_sub (hfY x) (hfY x')]
      calc |∫ ω, (f (x + Y ω) - f (x' + Y ω)) ∂P| ≤ ∫ ω, |f (x + Y ω) - f (x' + Y ω)| ∂P :=
            abs_integral_le_integral_abs
        _ ≤ ∫ _ω, ‖x - x'‖ ∂P := by
            refine integral_mono ((hfY x).sub (hfY x')).abs (integrable_const _) fun ω => ?_
            have := hfle (x + Y ω) (x' + Y ω)
            rwa [add_sub_add_right_eq_sub] at this
        _ = ‖x - x'‖ := by simp
    have hhc : Continuous h := hh.continuous
    have hS : ∀ ω, ∑ i ∈ insert j s, ξ i ω = T ω + Y ω := fun ω => by
      rw [Finset.sum_insert hj, add_comm]
    -- Fubini for the mean
    have hmean : ∫ ω, f (∑ i ∈ insert j s, ξ i ω) ∂P = ∫ ω, h (T ω) ∂P := by
      simp_rw [hS]
      have hg : Integrable (fun p : H × H => f (p.1 + p.2)) ((P.map T).prod (P.map Y)) := by
        have h1 : Integrable (fun x : H => ‖x‖) (P.map T) :=
          (integrable_map_measure continuous_norm.aestronglyMeasurable hTm.aemeasurable).2 hTint
        have h2 : Integrable (fun y : H => ‖y‖) (P.map Y) :=
          (integrable_map_measure continuous_norm.aestronglyMeasurable hYm.aemeasurable).2
            (hξint j).norm
        refine (((integrable_const |f 0|).add (h1.comp_fst _)).add (h2.comp_snd _)).mono'
          (by fun_prop : Continuous fun p : H × H => f (p.1 + p.2)).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun p => ?_
        rw [Real.norm_eq_abs]
        have := hfle (p.1 + p.2) 0
        rw [sub_zero] at this
        have := norm_add_le p.1 p.2
        simp only [Pi.add_apply]
        linarith [abs_sub_abs_le_abs_sub (f (p.1 + p.2)) (f 0)]
      rw [indep_integral P hTm hYm hind (fun p => f (p.1 + p.2)) hg]
      rw [← integral_map hTm.aemeasurable hhc.aestronglyMeasurable]
      congr 1; funext x
      show ∫ y, f (x + y) ∂(P.map Y) = ∫ ω, f (x + Y ω) ∂P
      rw [integral_map hYm.aemeasurable
        (by fun_prop : Continuous fun y => f (x + y)).aestronglyMeasurable]
    rw [hmean]
    simp_rw [hS]
    set m := ∫ ω, h (T ω) ∂P with hmdef
    -- the factorization
    set g : H × H → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (lam * (h p.1 - m))) *
      ENNReal.ofReal (Real.exp (lam * (f (p.1 + p.2) - h p.1))) with hgdef
    have hgm : Measurable g := by
      have c1 : Continuous fun p : H × H => Real.exp (lam * (h p.1 - m)) := by fun_prop
      have c2 : Continuous fun p : H × H => Real.exp (lam * (f (p.1 + p.2) - h p.1)) := by
        fun_prop
      exact (ENNReal.measurable_ofReal.comp c1.measurable).mul
        (ENNReal.measurable_ofReal.comp c2.measurable)
    have hfac : ∀ ω, ENNReal.ofReal (Real.exp (lam * (f (T ω + Y ω) - m))) = g (T ω, Y ω) := by
      intro ω
      simp only [hgdef]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
    simp_rw [hfac]
    rw [indep_lintegral P hTm hYm hind g hgm]
    -- inner bound
    have hinner : ∀ x, ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (f (x + y) - h x))) ∂(P.map Y) ≤
        ENNReal.ofReal (Real.exp c) := by
      intro x
      have hm1 : Measurable fun y => ENNReal.ofReal (Real.exp (lam * (f (x + y) - h x))) :=
        ENNReal.measurable_ofReal.comp
          (by fun_prop : Continuous fun y => Real.exp (lam * (f (x + y) - h x))).measurable
      rw [lintegral_map hm1 hYm]
      set a : Ω → ℝ := fun ω => f (x + Y ω) - f x with hadef
      have ham : Measurable a := (hfc.measurable.comp (measurable_const.add hYm)).sub measurable_const
      have hint_a : ∫ ω, a ω ∂P = h x - f x := by
        rw [hadef, integral_sub (hfY x) (integrable_const _)]; simp [hhdef]
      have hab : ∀ ω, |a ω| ≤ ‖Y ω‖ := fun ω => by
        have := hfle (x + Y ω) x; rwa [add_sub_cancel_left] at this
      have hstep := step_scalar P a ham B σ
        (by filter_upwards [hbound j] with ω hω; exact (hab ω).trans hω)
        (by
          refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
            (Integrable.of_bound (by fun_prop) (B ^ 2) ?_) (Filter.Eventually.of_forall fun ω => ?_)) (hvar j)
          · filter_upwards [hbound j] with ω hω
            rw [Real.norm_eq_abs, abs_pow, abs_norm]
            exact pow_le_pow_left₀ (norm_nonneg _) hω 2
          · show a ω ^ 2 ≤ ‖Y ω‖ ^ 2
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hab ω) 2)
        lam hl0 hl3
      rw [hint_a] at hstep
      have heq : (fun ω => Real.exp (lam * (a ω - (h x - f x)))) =
          fun ω => Real.exp (lam * (f (x + Y ω) - h x)) := by
        funext ω; simp only [hadef]; ring_nf
      rw [heq] at hstep
      have hexpint : Integrable (fun ω => Real.exp (lam * (f (x + Y ω) - h x))) P := by
        refine Integrable.of_bound (by fun_prop) (Real.exp (lam * (B + |f x - h x|))) ?_
        filter_upwards [hbound j] with ω hω
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
        apply mul_le_mul_of_nonneg_left _ hl0
        have := hab ω
        have := abs_le.mp this
        have := le_abs_self (f x - h x)
        simp only [hadef] at *
        linarith
      rw [← ofReal_integral_eq_lintegral_ofReal hexpint
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
      exact ENNReal.ofReal_le_ofReal hstep
    calc ∫⁻ x, ∫⁻ y, g (x, y) ∂(P.map Y) ∂(P.map T)
        = ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (h x - m))) *
            ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (f (x + y) - h x))) ∂(P.map Y) ∂(P.map T) := by
          congr 1; funext x
          simp only [hgdef]
          rw [lintegral_const_mul]
          exact ENNReal.measurable_ofReal.comp
            (by fun_prop : Continuous fun y => Real.exp (lam * (f (x + y) - h x))).measurable
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (h x - m))) * ENNReal.ofReal (Real.exp c)
            ∂(P.map T) := by
          gcongr with x
          exact hinner x
      _ = (∫⁻ x, ENNReal.ofReal (Real.exp (lam * (h x - m))) ∂(P.map T)) *
            ENNReal.ofReal (Real.exp c) := by
          rw [lintegral_mul_const]
          exact ENNReal.measurable_ofReal.comp
            (by fun_prop : Continuous fun x => Real.exp (lam * (h x - m))).measurable
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (h (T ω) - m))) ∂P) *
            ENNReal.ofReal (Real.exp c) := by
          have hm2 : Measurable fun x => ENNReal.ofReal (Real.exp (lam * (h x - m))) :=
            ENNReal.measurable_ofReal.comp
              (by fun_prop : Continuous fun x => Real.exp (lam * (h x - m))).measurable
          rw [lintegral_map hm2 hTm]
      _ ≤ ENNReal.ofReal (Real.exp (s.card * c)) * ENNReal.ofReal (Real.exp c) := by
          gcongr
          exact ih h hh
      _ = ENNReal.ofReal (Real.exp ((insert j s).card * c)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            Finset.card_insert_of_notMem hj]
          push_cast; ring_nf


lemma second_moment {ι : Type*} [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ι → Ω → H) (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P) (B σ : ℝ)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B) (hvar : ∀ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ σ ^ 2)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (s : Finset ι) :
    ∫ ω, ‖∑ i ∈ s, ξ i ω‖ ^ 2 ∂P ≤ s.card * σ ^ 2 := by
  have hξint : ∀ i, Integrable (ξ i) P := fun i =>
    Integrable.of_bound (hmeas i).aestronglyMeasurable B (hbound i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    set T : Ω → H := fun ω => ∑ i ∈ s, ξ i ω with hTdef
    set Y := ξ j with hYdef
    have hTm : Measurable T := Finset.measurable_sum s (fun i _ => hmeas i)
    have hYm : Measurable Y := hmeas j
    have hind : IndepFun T Y P := by
      have := hindep.indepFun_finsetSum_of_notMem hmeas hj
      rw [Finset.sum_fn] at this
      exact this
    have hTb : ∀ᵐ ω ∂P, ‖T ω‖ ≤ s.card * B := by
      have : ∀ᵐ ω ∂P, ∀ i ∈ s, ‖ξ i ω‖ ≤ B := (Filter.eventually_all_finset s).2 fun i _ => hbound i
      filter_upwards [this] with ω hω
      calc ‖T ω‖ ≤ ∑ i ∈ s, ‖ξ i ω‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hω
        _ = s.card * B := by simp
    have hTint : Integrable T P := Integrable.of_bound hTm.aestronglyMeasurable _ hTb
    have hS : ∀ ω, ‖∑ i ∈ insert j s, ξ i ω‖ ^ 2 = ‖T ω‖ ^ 2 + 2 * ⟪T ω, Y ω⟫ + ‖Y ω‖ ^ 2 :=
      fun ω => by rw [Finset.sum_insert hj, add_comm]; exact norm_add_sq_real _ _
    simp_rw [hS]
    have hT2 : Integrable (fun ω => ‖T ω‖ ^ 2) P :=
      Integrable.of_bound (hTm.norm.pow_const 2).aestronglyMeasurable ((s.card * B) ^ 2) (by
        filter_upwards [hTb] with ω hω
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
    have hY2 : Integrable (fun ω => ‖Y ω‖ ^ 2) P :=
      Integrable.of_bound (hYm.norm.pow_const 2).aestronglyMeasurable (B ^ 2) (by
        filter_upwards [hbound j] with ω hω
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
    have h1 : Integrable (fun x : H => ‖x‖) (P.map T) :=
      (integrable_map_measure continuous_norm.aestronglyMeasurable hTm.aemeasurable).2 hTint.norm
    have h2 : Integrable (fun y : H => ‖y‖) (P.map Y) :=
      (integrable_map_measure continuous_norm.aestronglyMeasurable hYm.aemeasurable).2
        (hξint j).norm
    have hgi : Integrable (fun p : H × H => ⟪p.1, p.2⟫) ((P.map T).prod (P.map Y)) := by
      refine (h1.mul_prod h2).mono' (by fun_prop : Continuous fun p : H × H => ⟪p.1, p.2⟫).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun p => ?_
      rw [Real.norm_eq_abs]
      exact abs_real_inner_le_norm _ _
    have hTY : Integrable (fun ω => ⟪T ω, Y ω⟫) P := by
      have hmap := (indepFun_iff_map_prod_eq_prod_map_map hTm.aemeasurable hYm.aemeasurable).1 hind
      rw [← hmap] at hgi
      exact (integrable_map_measure hgi.aestronglyMeasurable (hTm.prodMk hYm).aemeasurable).1 hgi
    have hzero : ∫ ω, ⟪T ω, Y ω⟫ ∂P = 0 := by
      rw [indep_integral P hTm hYm hind (fun p => ⟪p.1, p.2⟫) hgi]
      have hYi : Integrable (fun y : H => y) (P.map Y) :=
        (integrable_map_measure aestronglyMeasurable_id hYm.aemeasurable).2 (hξint j)
      have hY0 : ∫ y, y ∂(P.map Y) = 0 := by
        exact (integral_map hYm.aemeasurable aestronglyMeasurable_id).trans (hmean j)
      have : ∀ x : H, ∫ y, ⟪(x, y).1, (x, y).2⟫ ∂(P.map Y) = 0 := fun x => by
        show ∫ y, ⟪x, y⟫ ∂(P.map Y) = 0
        rw [integral_inner hYi x, hY0, inner_zero_right]
      simp only [this, integral_zero]
    rw [integral_add (f := fun ω => ‖T ω‖ ^ 2 + 2 * ⟪T ω, Y ω⟫) (g := fun ω => ‖Y ω‖ ^ 2)
      (hT2.add (hTY.const_mul 2)) hY2,
      integral_add (f := fun ω => ‖T ω‖ ^ 2) (g := fun ω => 2 * ⟪T ω, Y ω⟫) hT2 (hTY.const_mul 2),
      integral_const_mul, hzero, Finset.card_insert_of_notMem hj]
    have := hvar j
    push_cast
    linarith

theorem bern_hilbert_main (P : Measure Ω) [IsProbabilityMeasure P]
    (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B)
    (hvar : ∀ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + Real.sqrt (σ ^ 2 / n) + 2 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, ξ i ω‖} ≤ Real.exp (-τ) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set S : Ω → H := fun ω => ∑ i, ξ i ω with hSdef
  have hSm : Measurable S := Finset.measurable_sum _ (fun i _ => hmeas i)
  have hSb : ∀ᵐ ω ∂P, ‖S ω‖ ≤ n * B := by
    have : ∀ᵐ ω ∂P, ∀ i, ‖ξ i ω‖ ≤ B := ae_all_iff.mpr hbound
    filter_upwards [this] with ω hω
    calc ‖S ω‖ ≤ ∑ i, ‖ξ i ω‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hω i
      _ = n * B := by simp
  -- first moment bound
  set r := (n : ℝ) * Real.sqrt (σ ^ 2 / n) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 = n * σ ^ 2 := by
    rw [hr, mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  set E := ∫ ω, ‖S ω‖ ∂P with hE
  have hES : E ≤ r := by
    have h2 := second_moment P ξ hmeas hindep B σ hbound hvar hmean Finset.univ
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have hmem : MemLp (fun ω => ‖S ω‖) 2 P :=
      MemLp.of_bound hSm.norm.aestronglyMeasurable (n * B) (by
        filter_upwards [hSb] with ω hω; rwa [Real.norm_eq_abs, abs_norm])
    have hv := variance_nonneg (fun ω => ‖S ω‖) P
    rw [variance_eq_sub hmem] at hv
    have e2 : P[(fun ω => ‖S ω‖) ^ 2] = ∫ ω, ‖∑ i, ξ i ω‖ ^ 2 ∂P := rfl
    rw [e2] at hv
    have hE2 : E ^ 2 ≤ r ^ 2 := by rw [hr2]; linarith
    nlinarith
  -- parameters as in the scalar case
  set a := (n : ℝ) * Real.sqrt (2 * σ ^ 2 * τ / n) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = 2 * n * σ ^ 2 * τ := by
    rw [ha, mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  set b := 2 * B * τ / 3 with hb
  have hb0 : 0 < b := by positivity
  set T := a + b with hT
  set D := n * σ ^ 2 + B * T / 3 with hD
  have hDpos : 0 < D := by positivity
  set lam := T / D with hlam
  have hl0 : 0 ≤ lam := by positivity
  have hl3 : lam * B < 3 := by
    rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hDpos, hD]
    nlinarith [mul_pos hnR (pow_pos hσ 2)]
  have hset : {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + Real.sqrt (σ ^ 2 / n) + 2 * B * τ / (3 * n) ≤
      ‖(1 / (n : ℝ)) • ∑ i, ξ i ω‖} = {ω | T + r ≤ ‖S ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / n), one_div,
      ← div_eq_inv_mul, le_div_iff₀ hnR]
    have e : (Real.sqrt (2 * σ ^ 2 * τ / n) + Real.sqrt (σ ^ 2 / n) + 2 * B * τ / (3 * n)) * n
        = T + r := by rw [hT, ha, hb, hr]; field_simp; ring
    rw [e]
  rw [hset]
  have hint : Integrable (fun ω => Real.exp (lam * ‖S ω‖)) P := by
    refine Integrable.of_bound (by fun_prop) (Real.exp (lam * (n * B))) ?_
    filter_upwards [hSb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hω hl0
  have hch := measure_ge_le_exp_mul_mgf (X := fun ω => ‖S ω‖) (μ := P) (T + r) hl0 hint
  -- centred exponential moment
  set c := lam ^ 2 * σ ^ 2 / (2 * (1 - lam * B / 3)) with hc
  have hconc := conc_induct P ξ hmeas hindep B σ hbound hvar lam hl0 hl3 Finset.univ
    (fun x => ‖x‖) lipschitzWith_one_norm
  simp only [Finset.card_univ, Fintype.card_fin] at hconc
  have hint2 : Integrable (fun ω => Real.exp (lam * (‖S ω‖ - E))) P := by
    refine Integrable.of_bound (by fun_prop) (Real.exp (lam * (n * B + |E|))) ?_
    filter_upwards [hSb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    apply mul_le_mul_of_nonneg_left _ hl0
    linarith [neg_abs_le E]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le),
    ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le] at hconc
  have hmgf : mgf (fun ω => ‖S ω‖) P lam = Real.exp (lam * E) *
      ∫ ω, Real.exp (lam * (‖S ω‖ - E)) ∂P := by
    unfold mgf
    rw [← integral_const_mul]
    congr 1; funext ω
    rw [← Real.exp_add]; ring_nf
  rw [hmgf] at hch
  refine hch.trans ?_
  calc Real.exp (-lam * (T + r)) * (Real.exp (lam * E) * ∫ ω, Real.exp (lam * (‖S ω‖ - E)) ∂P)
      ≤ Real.exp (-lam * (T + r)) * (Real.exp (lam * E) * Real.exp (n * c)) := by
        gcongr
    _ = Real.exp (-lam * T + n * c + lam * (E - r)) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-lam * T + n * c) := by
        rw [Real.exp_le_exp]
        have : lam * (E - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hl0 (by linarith)
        linarith
    _ ≤ Real.exp (-τ) := by
        rw [Real.exp_le_exp]
        have hD0 : D ≠ 0 := hDpos.ne'
        have h1 : 1 - lam * B / 3 = n * σ ^ 2 / D := by
          rw [hlam, eq_div_iff hD0]
          field_simp
          rw [hD]; ring
        rw [hc, h1]
        have hkey : -lam * T + n * (lam ^ 2 * σ ^ 2 / (2 * (n * σ ^ 2 / D))) =
            -(T ^ 2 / (2 * D)) := by
          rw [hlam]
          have : (n : ℝ) * σ ^ 2 ≠ 0 := by positivity
          field_simp
          ring
        rw [hkey, neg_le_neg_iff, le_div_iff₀ (by positivity)]
        have hab : 0 ≤ a * b := mul_nonneg ha0 hb0.le
        rw [hD, hT]
        nlinarith [ha2]


theorem hoeffding_hilbert_main (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ) (hB : 0 < B) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | B * Real.sqrt (2 * τ / n) + B * Real.sqrt (1 / n) + 4 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖} ≤ Real.exp (-τ) := by
  set c : Fin n → H := fun i => ∫ ω', ξ i ω' ∂P with hcdef
  have hξint : ∀ i, Integrable (ξ i) P := fun i =>
    Integrable.of_bound (hmeas i).aestronglyMeasurable B (hbound i)
  have hc : ∀ i, ‖c i‖ ≤ B := fun i => by
    have := norm_integral_le_of_norm_le_const (hbound i)
    simpa using this
  set η : Fin n → Ω → H := fun i ω => ξ i ω - c i with hηdef
  have hηm : ∀ i, Measurable (η i) := fun i => (hmeas i).sub measurable_const
  have hηind : iIndepFun η P :=
    hindep.comp (fun i x => x - c i) (fun i => measurable_id.sub measurable_const)
  have hηmean : ∀ i, ∫ ω, η i ω ∂P = 0 := fun i => by
    simp only [hηdef]
    rw [integral_sub (hξint i) (integrable_const _)]
    simp [hcdef]
  have hηb : ∀ i, ∀ᵐ ω ∂P, ‖η i ω‖ ≤ 2 * B := fun i => by
    filter_upwards [hbound i] with ω hω
    calc ‖ξ i ω - c i‖ ≤ ‖ξ i ω‖ + ‖c i‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hc i]
  have hηvar : ∀ i, ∫ ω, ‖η i ω‖ ^ 2 ∂P ≤ B ^ 2 := fun i => by
    have hx2 : Integrable (fun ω => ‖ξ i ω‖ ^ 2) P :=
      Integrable.of_bound ((hmeas i).norm.pow_const 2).aestronglyMeasurable (B ^ 2) (by
        filter_upwards [hbound i] with ω hω
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
    have hin : Integrable (fun ω => ⟪c i, ξ i ω⟫) P := (hξint i).const_inner (c i)
    have e1 : ∀ ω, ‖η i ω‖ ^ 2 = ‖ξ i ω‖ ^ 2 - 2 * ⟪c i, ξ i ω⟫ + ‖c i‖ ^ 2 := fun ω => by
      simp only [hηdef]; rw [norm_sub_sq_real, real_inner_comm]
    simp_rw [e1]
    rw [integral_add (f := fun ω => ‖ξ i ω‖ ^ 2 - 2 * ⟪c i, ξ i ω⟫) (g := fun _ => ‖c i‖ ^ 2)
        (hx2.sub (hin.const_mul 2)) (integrable_const _),
      integral_sub (f := fun ω => ‖ξ i ω‖ ^ 2) (g := fun ω => 2 * ⟪c i, ξ i ω⟫) hx2
        (hin.const_mul 2),
      integral_const_mul, integral_inner (hξint i) (c i), real_inner_self_eq_norm_sq]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ B ^ 2 := by
      have := integral_mono_ae hx2 (integrable_const (B ^ 2)) (by
        filter_upwards [hbound i] with ω hω; exact pow_le_pow_left₀ (norm_nonneg _) hω 2)
      simpa using this
    nlinarith [sq_nonneg ‖c i‖]
  have h := bern_hilbert_main P (2 * B) B (by positivity) hB n hn η hηm hηind hηmean hηb
    hηvar τ hτ
  have e1 : Real.sqrt (2 * B ^ 2 * τ / n) = B * Real.sqrt (2 * τ / n) := by
    rw [show 2 * B ^ 2 * τ / n = B ^ 2 * (2 * τ / n) by ring, Real.sqrt_mul (sq_nonneg B),
      Real.sqrt_sq hB.le]
  have e2 : Real.sqrt (B ^ 2 / n) = B * Real.sqrt (1 / n) := by
    rw [show B ^ 2 / n = B ^ 2 * (1 / n) by ring, Real.sqrt_mul (sq_nonneg B),
      Real.sqrt_sq hB.le]
  have e3 : 2 * (2 * B) * τ / (3 * n) = 4 * B * τ / (3 * n) := by ring
  rw [e1, e2, e3] at h
  exact h

end Conc

end SupportVectorMachines.Concentration

open SupportVectorMachines.Concentration

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
    (B σ : ℝ) (hB : 0 < B) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) (ξ : Fin n → Ω → H)
    (hmeas : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0) (hbound : ∀ i, ∀ᵐ ω ∂P, ‖ξ i ω‖ ≤ B)
    (hvar : ∀ i, ∫ ω, ‖ξ i ω‖ ^ 2 ∂P ≤ σ ^ 2) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | Real.sqrt (2 * σ ^ 2 * τ / n) + Real.sqrt (σ ^ 2 / n) + 2 * B * τ / (3 * n) ≤
        ‖(1 / (n : ℝ)) • ∑ i, ξ i ω‖} ≤ Real.exp (-τ) := by
  exact bern_hilbert_main P B σ hB hσ n hn ξ hmeas hindep hmean hbound hvar τ hτ
