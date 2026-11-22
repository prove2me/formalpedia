-- Prove2me | solution 1 for SchauderBasis.exists_schauderBasis_Lp_fourier
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:14:49.376816+00:00
-- url     : https://prove2.me/submissions/0e851c14-11d6-477b-bd08-51fbbeada367

import Mathlib
import Theorems.Thm_FourierSeries_exists_rieszProjection_norm_le

open Filter Topology MeasureTheory AddCircle ENNReal

set_option autoImplicit false

namespace Sol_SchauderBasis_exists_schauderBasis_Lp_fourier

def zeta (n : ℕ) : ℤ := if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)

lemma zeta_injective : Function.Injective zeta := by
  intro i j h
  simp only [zeta, Nat.odd_iff] at h
  split_ifs at h <;> omega

lemma zeta_surjective : Function.Surjective zeta := by
  intro n
  refine ⟨if 0 < n then 2 * n.toNat - 1 else 2 * (-n).toNat, ?_⟩
  simp only [zeta, Nat.odd_iff]
  split_ifs <;> omega

lemma lt_iff_zeta (N j : ℕ) :
    j < N ↔ (-(((N : ℤ) - 1) / 2) ≤ zeta j ∧ zeta j ≤ (N : ℤ) / 2) := by
  simp only [zeta, Nat.odd_iff]
  split_ifs <;> omega

lemma mem_of_natAbs_le (N M : ℕ) (n : ℤ) (hn : n.natAbs ≤ M) (hN : 2 * M + 1 ≤ N) :
    (-(((N : ℤ) - 1) / 2) ≤ n ∧ n ≤ (N : ℤ) / 2) := by
  omega

variable {T : ℝ} [hT : Fact (0 < T)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit hT in
lemma norm_fourier_apply (k : ℤ) (x : AddCircle T) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

lemma norm_toLp_eq_of_norm_eq (f g : C(AddCircle T, ℂ)) (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ‖ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ f‖ =
      ‖ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ g‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ f),
    eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ g)]
  congr 1
  exact eLpNorm_congr_norm_ae (ae_of_all _ h)

lemma norm_sum_shift (s : Finset ℤ) (c : ℤ → ℂ) (k : ℤ) :
    ‖∑ n ∈ s, c n • fourierLp (T := T) p (n + k)‖ = ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖ := by
  have h1 : ∑ n ∈ s, c n • fourierLp (T := T) p (n + k) =
      ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ
        (∑ n ∈ s, c n • fourier (n + k)) := by
    simp only [map_sum, map_smul]
  have h2 : ∑ n ∈ s, c n • fourierLp (T := T) p n =
      ContinuousMap.toLp (E := ℂ) p (haarAddCircle (T := T)) ℂ
        (∑ n ∈ s, c n • fourier n) := by
    simp only [map_sum, map_smul]
  rw [h1, h2]
  apply norm_toLp_eq_of_norm_eq
  intro x
  have : (∑ n ∈ s, c n • fourier (T := T) (n + k)) x = (∑ n ∈ s, c n • fourier (T := T) n) x * fourier k x := by
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, fourier_add, Finset.sum_mul, mul_assoc]
  rw [this, norm_mul, norm_fourier_apply, mul_one]


lemma halfline_bound (C : ℝ)
    (hC : ∀ (s : Finset ℤ) (c : ℤ → ℂ), ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖)
    (a : ℤ) (s : Finset ℤ) (c : ℤ → ℂ) :
    ‖∑ n ∈ s with a ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖ := by
  have h := hC (s.map (Equiv.subRight a).toEmbedding) (fun m => c (m + a))
  have e1 : ∑ m ∈ s.map (Equiv.subRight a).toEmbedding, c (m + a) • fourierLp (T := T) p m =
      ∑ n ∈ s, c n • fourierLp (T := T) p (n + -a) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [sub_eq_add_neg]
  have e2 : ∑ m ∈ s.map (Equiv.subRight a).toEmbedding with 0 ≤ m,
        c (m + a) • fourierLp (T := T) p m =
      ∑ n ∈ s with a ≤ n, c n • fourierLp (T := T) p (n + -a) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Equiv.coe_toEmbedding, Equiv.subRight_apply, sub_add_cancel, sub_nonneg]
    rw [sub_eq_add_neg]
  rw [e1, e2, norm_sum_shift, norm_sum_shift] at h
  exact h

lemma interval_bound (C : ℝ)
    (hC : ∀ (s : Finset ℤ) (c : ℤ → ℂ), ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖)
    (a b : ℤ) (s : Finset ℤ) (c : ℤ → ℂ) :
    ‖∑ n ∈ s with (a ≤ n ∧ n ≤ b), c n • fourierLp (T := T) p n‖ ≤
        (2 * C) * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖ := by
  have hsplit : ∑ n ∈ s with (a ≤ n ∧ n ≤ b), c n • fourierLp (T := T) p n =
      ∑ n ∈ s with a ≤ n, c n • fourierLp (T := T) p n -
        ∑ n ∈ s with max a (b + 1) ≤ n, c n • fourierLp (T := T) p n := by
    rw [eq_sub_iff_add_eq, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : a ≤ n <;> by_cases h2 : n ≤ b <;> simp [h1, h2]
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have := halfline_bound C hC a s c
  have := halfline_bound C hC (max a (b + 1)) s c
  linarith


/-- The `m`-th Fourier coefficient as a linear functional on `L^p`. -/
noncomputable def coefL (m : ℤ) : Lp ℂ p (haarAddCircle (T := T)) →ₗ[ℂ] ℂ where
  toFun f := fourierCoeff (⇑f) m
  map_add' f g := by
    rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),
      fourierCoeff.add ((Lp.memLp f).integrable Fact.out) ((Lp.memLp g).integrable Fact.out)]
    rfl
  map_smul' c f := by
    rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f)]
    exact fourierCoeff.const_smul _ c m

lemma norm_coefL_le (m : ℤ) (f : Lp ℂ p (haarAddCircle (T := T))) :
    ‖coefL m f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  show ‖∫ t, fourier (-m) t • (f : AddCircle T → ℂ) t ∂haarAddCircle‖ ≤ ‖f‖
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∀ t, ‖fourier (-m) t • (f : AddCircle T → ℂ) t‖ = ‖(f : AddCircle T → ℂ) t‖ := by
    intro t
    rw [norm_smul, norm_fourier_apply, one_mul]
  simp_rw [h1]
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (Fact.out : 1 ≤ p) (Lp.aestronglyMeasurable f))

/-- The `m`-th Fourier coefficient as a continuous linear functional on `L^p`. -/
noncomputable def coef (m : ℤ) : StrongDual ℂ (Lp ℂ p (haarAddCircle (T := T))) :=
  (coefL m).mkContinuous 1 (norm_coefL_le m)

lemma coef_fourierLp (m n : ℤ) :
    coef (T := T) (p := p) m (fourierLp (T := T) p n) = (Pi.single n (1 : ℂ) : ℤ → ℂ) m := by
  show fourierCoeff (⇑(fourierLp (T := T) p n)) m = _
  rw [fourierCoeff_congr_ae (coeFn_fourierLp p n), fourierCoeff_fourier]


/-- The `N`-th partial sum operator of the Fourier series in the order `zeta`. -/
noncomputable def Q (N : ℕ) :
    Lp ℂ p (haarAddCircle (T := T)) →L[ℂ] Lp ℂ p (haarAddCircle (T := T)) :=
  ∑ i ∈ Finset.range N, (coef (T := T) (p := p) (zeta i)).smulRight (fourierLp (T := T) p (zeta i))

lemma Q_apply (N : ℕ) (x : Lp ℂ p (haarAddCircle (T := T))) :
    Q N x = ∑ i ∈ Finset.range N, coef (zeta i) x • fourierLp (T := T) p (zeta i) := by
  simp [Q, ContinuousLinearMap.smulRight_apply]

lemma Q_fourierLp (N : ℕ) (n : ℤ) :
    Q (T := T) (p := p) N (fourierLp (T := T) p n) =
      if (-(((N : ℤ) - 1) / 2) ≤ n ∧ n ≤ (N : ℤ) / 2) then fourierLp (T := T) p n else 0 := by
  obtain ⟨j, rfl⟩ := zeta_surjective n
  rw [Q_apply]
  have : ∀ i, coef (T := T) (p := p) (zeta i) (fourierLp (T := T) p (zeta j)) •
      fourierLp (T := T) p (zeta i) = if i = j then fourierLp (T := T) p (zeta j) else 0 := by
    intro i
    rw [coef_fourierLp, Pi.single_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (zeta_injective.ne h), if_neg h, zero_smul]
  simp_rw [this]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, lt_iff_zeta]

lemma Q_trig (N : ℕ) (s : Finset ℤ) (c : ℤ → ℂ) :
    Q (T := T) (p := p) N (∑ n ∈ s, c n • fourierLp (T := T) p n) =
      ∑ n ∈ s with (-(((N : ℤ) - 1) / 2) ≤ n ∧ n ≤ (N : ℤ) / 2), c n • fourierLp (T := T) p n := by
  rw [map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, Q_fourierLp]
  split_ifs <;> simp

lemma mem_closure_span (hp' : p ≠ ∞) (x : Lp ℂ p (haarAddCircle (T := T))) :
    x ∈ closure (Submodule.span ℂ (Set.range (fourierLp (T := T) p)) : Set _) := by
  rw [← Submodule.topologicalClosure_coe, span_fourierLp_closure_eq_top hp']
  trivial

lemma Q_bound (hp' : p ≠ ∞) (C : ℝ)
    (hC : ∀ (s : Finset ℤ) (c : ℤ → ℂ), ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖)
    (N : ℕ) (x : Lp ℂ p (haarAddCircle (T := T))) :
    ‖Q N x‖ ≤ (2 * C) * ‖x‖ := by
  have hcl : IsClosed {y : Lp ℂ p (haarAddCircle (T := T)) | ‖Q N y‖ ≤ (2 * C) * ‖y‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  refine closure_minimal ?_ hcl (mem_closure_span hp' x)
  intro y hy
  obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  simp only [Set.mem_ofPred_eq, Finsupp.sum]
  rw [Q_trig]
  exact interval_bound C hC _ _ _ _

lemma Q_tendsto (hp' : p ≠ ∞) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (s : Finset ℤ) (c : ℤ → ℂ), ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        C * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖)
    (x : Lp ℂ p (haarAddCircle (T := T))) :
    Tendsto (fun N => Q N x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : 0 ≤ 2 * C := by positivity
  obtain ⟨g, hg, hxg⟩ := Metric.mem_closure_iff.mp (mem_closure_span hp' x) (ε / (2 * C + 2))
    (by positivity)
  obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
  refine ⟨2 * d.support.sup Int.natAbs + 1, fun N hN => ?_⟩
  have hQg : Q N (d.sum fun i a => a • fourierLp (T := T) p i) =
      d.sum fun i a => a • fourierLp (T := T) p i := by
    simp only [Finsupp.sum]
    rw [Q_trig]
    congr 1
    apply Finset.filter_true_of_mem
    intro n hn
    exact mem_of_natAbs_le N _ n (Finset.le_sup (f := Int.natAbs) hn) hN
  set g := d.sum fun i a => a • fourierLp (T := T) p i
  rw [dist_eq_norm]
  have hsplit : Q N x - x = Q N (x - g) + (g - x) := by rw [map_sub, hQg]; abel
  rw [hsplit]
  have hb := Q_bound hp' C hC N (x - g)
  have hdist : ‖x - g‖ < ε / (2 * C + 2) := by rwa [← dist_eq_norm]
  have h2 : (2 * C + 1) * (ε / (2 * C + 2)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  calc ‖Q N (x - g) + (g - x)‖ ≤ ‖Q N (x - g)‖ + ‖g - x‖ := norm_add_le _ _
    _ ≤ (2 * C) * ‖x - g‖ + ‖x - g‖ := by rw [norm_sub_rev g x]; linarith
    _ = (2 * C + 1) * ‖x - g‖ := by ring
    _ ≤ (2 * C + 1) * (ε / (2 * C + 2)) := by gcongr
    _ < ε := h2

lemma hasSum_cond_iff {X : Type*} [NormedAddCommGroup X] (f : ℕ → X) (x : X) :
    HasSum f x (SummationFilter.conditional ℕ) ↔
      Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (𝓝 x) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

end Sol_SchauderBasis_exists_schauderBasis_Lp_fourier

open Sol_SchauderBasis_exists_schauderBasis_Lp_fourier SchauderBasis

theorem solution (T : ℝ) [Fact (0 < T)] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : 1 < p) (hp' : p ≠ ∞) :
    ∃ b : SchauderBasis ℂ (Lp ℂ p (haarAddCircle (T := T))),
      ∀ n : ℕ, b.basis n = fourierLp (T := T) p (if Odd n then (((n + 1) / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) := by
  obtain ⟨C, hC⟩ := FourierSeries.exists_rieszProjection_norm_le T p hp hp'
  have hC' : ∀ (s : Finset ℤ) (c : ℤ → ℂ),
      ‖∑ n ∈ s with 0 ≤ n, c n • fourierLp (T := T) p n‖ ≤
        max C 0 * ‖∑ n ∈ s, c n • fourierLp (T := T) p n‖ := fun s c =>
    (hC s c).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨{ basis := fun n => fourierLp (T := T) p (zeta n)
            coord := fun n => coef (zeta n)
            ortho := ?_
            expansion := ?_ }, fun n => rfl⟩
  · intro i j
    rw [coef_fourierLp]
    have h : ∀ (inst : DecidableEq ℕ),
        (Pi.single (zeta j) (1 : ℂ) : ℤ → ℂ) (zeta i) = @Pi.single ℕ (fun _ => ℂ) _ inst j 1 i := by
      intro inst
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne (zeta_injective.ne hij), Pi.single_eq_of_ne hij]
    exact h _
  · intro x
    rw [hasSum_cond_iff]
    have := Q_tendsto hp' (max C 0) (le_max_right _ _) hC' x
    simpa only [Q_apply] using this
