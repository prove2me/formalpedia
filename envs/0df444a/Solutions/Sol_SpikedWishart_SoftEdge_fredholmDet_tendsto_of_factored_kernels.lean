-- Prove2me | solution 1 for SpikedWishart.SoftEdge.fredholmDet_tendsto_of_factored_kernels
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T09:19:08.066196+00:00
-- url     : https://prove2.me/submissions/7cedbbd5-7781-44dc-ba1b-aace73e4ccf1

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Airy

set_option autoImplicit false

namespace Lib5e

open Matrix InnerProductSpace

/-- R1. Hadamard's inequality for real square matrices: `|det A| ≤ ∏ᵢ ‖row i‖₂`. -/
theorem hadamard_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    |A.det| ≤ ∏ i, Real.sqrt (∑ j, A i j ^ 2) := by
  classical
  let f : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (A i)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  let g := gramSchmidtOrthonormalBasis hcard f
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have h1 : e.toBasis.det f = A.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  have h2 : e.toBasis.det f = e.toBasis.det g * g.toBasis.det f := by
    have := congrArg (fun F => F f) (AlternatingMap.eq_smul_basis_det (e := g.toBasis) e.toBasis.det)
    simpa using this
  have h3 : |e.toBasis.det g| = 1 := by
    rcases e.det_to_matrix_orthonormalBasis_real g with h | h <;> simp [h]
  rw [← h1, h2, abs_mul, h3, one_mul, gramSchmidtOrthonormalBasis_det, Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
  calc |inner ℝ (g i) (f i)| ≤ ‖g i‖ * ‖f i‖ := abs_real_inner_le_norm _ _
    _ = ‖f i‖ := by rw [g.orthonormal.1 i, one_mul]
    _ = Real.sqrt (∑ j, A i j ^ 2) := by
        rw [EuclideanSpace.norm_eq]; simp [f, Real.norm_eq_abs, sq_abs]

/-- R4. Conjugating a kernel by a nonvanishing function does not change the Fredholm minors. -/
theorem det_conj {n : ℕ} (a : ℝ → ℝ) (ha : ∀ t, a t ≠ 0) (K : ℝ → ℝ → ℝ) (u : Fin n → ℝ) :
    (Matrix.of fun i j => a (u i) * K (u i) (u j) / a (u j)).det =
      (Matrix.of fun i j => K (u i) (u j)).det := by
  have hM : (Matrix.of fun i j => a (u i) * K (u i) (u j) / a (u j)) =
      Matrix.diagonal (fun i => a (u i)) * (Matrix.of fun i j => K (u i) (u j)) *
        Matrix.diagonal (fun i => (a (u i))⁻¹) := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, div_eq_mul_inv]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp [ha]

/-- Scaling every entry of an `n × n` matrix by `s` multiplies the determinant by `s ^ n`. -/
theorem det_smul_kernel {n : ℕ} (s : ℝ) (K : ℝ → ℝ → ℝ) (u : Fin n → ℝ) :
    (Matrix.of fun i j => s * K (u i) (u j)).det = s ^ n * (Matrix.of fun i j => K (u i) (u j)).det := by
  have : (Matrix.of fun i j => s * K (u i) (u j)) = s • (Matrix.of fun i j => K (u i) (u j)) := by
    ext i j; simp
  rw [this, Matrix.det_smul, Fintype.card_fin]

/-- R2a. Fredholm minor bound from a row-decaying kernel bound, via Hadamard. -/
theorem minor_bound {n : ℕ} (K : ℝ → ℝ → ℝ) (C a x : ℝ) (hC : 0 ≤ C)
    (hK : ∀ u v, x < u → x < v → |K u v| ≤ C * Real.exp (-a * u))
    (u : Fin n → ℝ) (hu : ∀ i, x < u i) :
    |(Matrix.of fun i j => K (u i) (u j)).det| ≤
      Real.sqrt n ^ n * C ^ n * ∏ i, Real.exp (-a * u i) := by
  refine (hadamard_det_le _).trans ?_
  have hrow : ∀ i, Real.sqrt (∑ j, (Matrix.of fun i j => K (u i) (u j)) i j ^ 2) ≤
      Real.sqrt n * (C * Real.exp (-a * u i)) := by
    intro i
    have h0 : 0 ≤ C * Real.exp (-a * u i) := mul_nonneg hC (Real.exp_pos _).le
    rw [← Real.sqrt_sq h0, ← Real.sqrt_mul (Nat.cast_nonneg n)]
    apply Real.sqrt_le_sqrt
    calc ∑ j, (Matrix.of fun i j => K (u i) (u j)) i j ^ 2
        ≤ ∑ _j : Fin n, (C * Real.exp (-a * u i)) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          simp only [Matrix.of_apply]
          have h := hK (u i) (u j) (hu i) (hu j)
          have h1 : K (u i) (u j) ^ 2 = |K (u i) (u j)| ^ 2 := (sq_abs _).symm
          rw [h1]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = n * (C * Real.exp (-a * u i)) ^ 2 := by simp
  calc (∏ i, Real.sqrt (∑ j, (Matrix.of fun i j => K (u i) (u j)) i j ^ 2))
      ≤ ∏ i : Fin n, (Real.sqrt n * (C * Real.exp (-a * u i))) :=
        Finset.prod_le_prod (fun i _ => Real.sqrt_nonneg _) (fun i _ => hrow i)
    _ = Real.sqrt n ^ n * C ^ n * ∏ i, Real.exp (-a * u i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        simp [Finset.prod_const]
        ring

/-- R2b. `Σ √n^n B^n / n!` converges (Hadamard bound is summable against `1/n!`). -/
theorem summable_sqrt_pow_div_factorial (B : ℝ) (hB : 0 ≤ B) :
    Summable (fun n : ℕ => Real.sqrt n ^ n * B ^ n / n.factorial) := by
  have hs : Summable (fun n : ℕ =>
      ((2 * Real.exp 1 * B ^ 2) ^ n / n.factorial + (1 / 2 : ℝ) ^ n) / 2) :=
    ((Real.summable_pow_div_factorial _).add summable_geometric_two).div_const 2
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hnn : (n : ℝ) ^ n ≤ Real.exp 1 ^ n * n.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) (Nat.cast_nonneg _) n
    rw [div_le_iff₀ hfac] at h
    calc (n : ℝ) ^ n ≤ Real.exp n * n.factorial := h
      _ = Real.exp 1 ^ n * n.factorial := by rw [← Real.exp_nat_mul, mul_one]
  have e1 : (Real.sqrt n ^ n) ^ 2 = (n : ℝ) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  set t := Real.sqrt n ^ n * B ^ n / n.factorial with ht
  set X := (2 * Real.exp 1 * B ^ 2) ^ n / n.factorial with hXd
  set Y := (1 / 2 : ℝ) ^ n with hYd
  have ht0 : 0 ≤ t := by positivity
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXY : X * Y = Real.exp 1 ^ n * (B ^ n) ^ 2 / n.factorial := by
    rw [hXd, hYd, div_mul_eq_mul_div, ← mul_pow]
    congr 1
    rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]
    congr 1
    ring
  have ht2 : t ^ 2 = (n : ℝ) ^ n * (B ^ n) ^ 2 / (n.factorial : ℝ) ^ 2 := by
    rw [ht, div_pow, mul_pow, e1]
  have hsq : t ^ 2 ≤ X * Y := by
    rw [ht2, hXY, div_le_div_iff₀ (by positivity) hfac]
    have h := mul_le_mul_of_nonneg_right hnn (by positivity : 0 ≤ (B ^ n) ^ 2 * (n.factorial : ℝ))
    calc (n : ℝ) ^ n * (B ^ n) ^ 2 * n.factorial = (n : ℝ) ^ n * ((B ^ n) ^ 2 * n.factorial) := by ring
      _ ≤ Real.exp 1 ^ n * n.factorial * ((B ^ n) ^ 2 * n.factorial) := h
      _ = Real.exp 1 ^ n * (B ^ n) ^ 2 * (n.factorial : ℝ) ^ 2 := by ring
  nlinarith [sq_nonneg (X - Y)]



open MeasureTheory Filter Topology Set

/-- The Fredholm minor `u ↦ det[K(u_i,u_j)]` is measurable when the kernel is. -/
theorem measurable_minor {n : ℕ} (K : ℝ → ℝ → ℝ) (hK : Measurable (Function.uncurry K)) :
    Measurable (fun u : Fin n → ℝ => (Matrix.of fun i j => K (u i) (u j)).det) := by
  have h : (fun u : Fin n → ℝ => (Matrix.of fun i j => K (u i) (u j)).det) =
      fun u => ∑ σ : Equiv.Perm (Fin n),
        (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, K (u (σ i)) (u i)) := by
    funext u
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Units.smul_def, zsmul_eq_mul]
    simp
  rw [h]
  refine Finset.measurable_sum _ (fun σ _ => ?_)
  refine Measurable.const_mul (Finset.measurable_prod _ (fun i _ => ?_)) _
  have hf : Measurable (fun u : Fin n → ℝ => (u (σ i), u i)) := by fun_prop
  exact hK.comp hf

theorem integrable_exp_prod (a x : ℝ) (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun u : Fin n → ℝ => ∏ i, Real.exp (-a * u i)) (Set.univ.pi fun _ => Ioi x) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi x) :=
    integrableOn_exp_mul_Ioi (by linarith) x
  unfold IntegrableOn
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (f := fun _ t => Real.exp (-a * t)) (fun _ => h1)

theorem integral_exp_prod (a x : ℝ) (ha : 0 < a) (n : ℕ) :
    ∫ u in Set.univ.pi (fun _ : Fin n => Ioi x), ∏ i, Real.exp (-a * u i) =
      (Real.exp (-a * x) / a) ^ n := by
  rw [volume_pi, Measure.restrict_pi_pi]
  have h := integral_fintype_prod_eq_pow (ι := Fin n) (fun t : ℝ => Real.exp (-a * t))
    (μ := volume.restrict (Ioi x))
  refine h.trans ?_
  rw [integral_exp_mul_Ioi (by linarith), Fintype.card_fin, neg_div_neg_eq]

/-- R2c. Bound on the `n`-th Fredholm term from a row-decaying kernel bound. -/
theorem term_bound {n : ℕ} (K : ℝ → ℝ → ℝ) (C a x : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hK : ∀ u v, x < u → x < v → |K u v| ≤ C * Real.exp (-a * u)) :
    |∫ u in Set.univ.pi (fun _ : Fin n => Ioi x), (Matrix.of fun i j => K (u i) (u j)).det| ≤
      Real.sqrt n ^ n * (C * (Real.exp (-a * x) / a)) ^ n := by
  have hS : MeasurableSet (Set.univ.pi (fun _ : Fin n => Ioi x)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hb : ∀ᵐ u ∂(volume.restrict (Set.univ.pi (fun _ : Fin n => Ioi x))),
      ‖(Matrix.of fun i j => K (u i) (u j)).det‖ ≤
        Real.sqrt n ^ n * C ^ n * ∏ i, Real.exp (-a * u i) := by
    rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall (fun u hu => by
      rw [Real.norm_eq_abs]; exact minor_bound K C a x hC hK u (fun i => hu i (Set.mem_univ i)))
  have h := norm_integral_le_of_norm_le
    ((integrable_exp_prod a x ha n).const_mul (Real.sqrt n ^ n * C ^ n)) hb
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_prod a x ha n, mul_pow, mul_assoc]

/-- R3a. Dominated convergence for one Fredholm term. -/
theorem term_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {n : ℕ}
    (K : ι → ℝ → ℝ → ℝ) (Kinf : ℝ → ℝ → ℝ) (C a x : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hmeas : ∀ᶠ i in l, Measurable (Function.uncurry (K i)))
    (hK : ∀ᶠ i in l, ∀ u v, x < u → x < v → |K i u v| ≤ C * Real.exp (-a * u))
    (hlim : ∀ u v, x < u → x < v → Tendsto (fun i => K i u v) l (𝓝 (Kinf u v))) :
    Tendsto (fun i => ∫ u in Set.univ.pi (fun _ : Fin n => Ioi x),
        (Matrix.of fun p q => K i (u p) (u q)).det) l
      (𝓝 (∫ u in Set.univ.pi (fun _ : Fin n => Ioi x),
        (Matrix.of fun p q => Kinf (u p) (u q)).det)) := by
  have hS : MeasurableSet (Set.univ.pi (fun _ : Fin n => Ioi x)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.sqrt n ^ n * C ^ n * ∏ p, Real.exp (-a * u p)) ?_ ?_
    ((integrable_exp_prod a x ha n).const_mul _) ?_
  · filter_upwards [hmeas] with i hi
    exact (measurable_minor (K i) hi).aestronglyMeasurable
  · filter_upwards [hK] with i hi
    rw [ae_restrict_iff' hS]
    exact Filter.Eventually.of_forall (fun u hu => by
      rw [Real.norm_eq_abs]; exact minor_bound (K i) C a x hC hi u (fun p => hu p (Set.mem_univ p)))
  · rw [ae_restrict_iff' hS]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) := continuous_id.matrix_det
    refine (hcont.tendsto _).comp ?_
    refine tendsto_pi_nhds.2 (fun p => tendsto_pi_nhds.2 (fun q => ?_))
    exact hlim _ _ (hu p (Set.mem_univ p)) (hu q (Set.mem_univ q))

/-- R3. Tannery for the Fredholm series: kernels converging pointwise on `(x,∞)²` under a uniform
row-decay bound have converging Fredholm determinants (series form of `fredholmDet`). -/
theorem fredholm_series_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (K : ι → ℝ → ℝ → ℝ) (Kinf : ℝ → ℝ → ℝ) (C a x : ℝ) (hC : 0 ≤ C) (ha : 0 < a)
    (hmeas : ∀ᶠ i in l, Measurable (Function.uncurry (K i)))
    (hK : ∀ᶠ i in l, ∀ u v, x < u → x < v → |K i u v| ≤ C * Real.exp (-a * u))
    (hlim : ∀ u v, x < u → x < v → Tendsto (fun i => K i u v) l (𝓝 (Kinf u v))) :
    Tendsto (fun i => ∑' n : ℕ, ((-1 : ℝ) ^ n / (n.factorial : ℝ)) *
        ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
          (Matrix.of fun p q : Fin n => K i (u p) (u q)).det) l
      (𝓝 (∑' n : ℕ, ((-1 : ℝ) ^ n / (n.factorial : ℝ)) *
        ∫ u in Set.pi Set.univ (fun _ : Fin n => Set.Ioi x),
          (Matrix.of fun p q : Fin n => Kinf (u p) (u q)).det)) := by
  have hB : 0 ≤ C * (Real.exp (-a * x) / a) := mul_nonneg hC (div_nonneg (Real.exp_pos _).le ha.le)
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℕ => Real.sqrt n ^ n * (C * (Real.exp (-a * x) / a)) ^ n / n.factorial)
    (summable_sqrt_pow_div_factorial _ hB)
    (fun n => (term_tendsto K Kinf C a x hC ha hmeas hK hlim).const_mul _) ?_
  filter_upwards [hK] with i hi
  intro n
  have h1 : |(-1 : ℝ) ^ n / (n.factorial : ℝ)| = 1 / n.factorial := by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [Real.norm_eq_abs, abs_mul, h1, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (term_bound (n := n) (K i) C a x hC ha hi) hf.le


open MeasureTheory Filter Topology Set

/-- R5. Affine change of variables `u = ξ₀ + s w` (`s > 0`) in the `n`-th Fredholm term. -/
theorem term_affine {n : ℕ} (K : ℝ → ℝ → ℝ) (ξ0 s x : ℝ) (hs : 0 < s) :
    ∫ u in Set.univ.pi (fun _ : Fin n => Ioi (ξ0 + s * x)),
        (Matrix.of fun p q => K (u p) (u q)).det =
      ∫ w in Set.univ.pi (fun _ : Fin n => Ioi x),
        (Matrix.of fun p q => s * K (ξ0 + s * w p) (ξ0 + s * w q)).det := by
  set S := Set.univ.pi (fun _ : Fin n => Ioi (ξ0 + s * x)) with hSdef
  set S' := Set.univ.pi (fun _ : Fin n => Ioi x) with hS'def
  let F : (Fin n → ℝ) → ℝ := fun u => (Matrix.of fun p q => K (u p) (u q)).det
  let c : Fin n → ℝ := fun _ => ξ0
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hS' : MeasurableSet S' := MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hmem : ∀ w : Fin n → ℝ, (c + s • w ∈ S ↔ w ∈ S') := by
    intro w
    show (∀ p ∈ Set.univ, (c + s • w) p ∈ Ioi (ξ0 + s * x)) ↔ (∀ p ∈ Set.univ, w p ∈ Ioi x)
    refine forall₂_congr (fun p _ => ?_)
    show ξ0 + s * x < ξ0 + s * w p ↔ x < w p
    constructor
    · intro h
      exact lt_of_mul_lt_mul_left (by linarith) hs.le
    · intro h
      have := mul_lt_mul_of_pos_left h hs
      linarith
  have h1 : ∀ w : Fin n → ℝ,
      (Matrix.of fun p q => s * K (ξ0 + s * w p) (ξ0 + s * w q)).det = s ^ n * F (c + s • w) := by
    intro w
    exact det_smul_kernel s (fun a b => K (ξ0 + s * a) (ξ0 + s * b)) w
  have hsn : 0 < s ^ n := pow_pos hs n
  have hcs : ∫ w, S.indicator F (c + s • w) = |(s ^ n)⁻¹| * ∫ u, S.indicator F u := by
    have h := Measure.integral_comp_smul (volume : Measure (Fin n → ℝ))
      (fun y => S.indicator F (c + y)) s
    beta_reduce at h
    rw [h, integral_add_left_eq_self (μ := volume) (f := S.indicator F) c,
      Module.finrank_fin_fun, smul_eq_mul]
  calc ∫ u in S, F u = ∫ u, S.indicator F u := (integral_indicator hS).symm
    _ = s ^ n * (|(s ^ n)⁻¹| * ∫ u, S.indicator F u) := by
        rw [abs_of_pos (inv_pos.2 hsn), ← mul_assoc, mul_inv_cancel₀ hsn.ne', one_mul]
    _ = s ^ n * ∫ w, S.indicator F (c + s • w) := by rw [hcs]
    _ = ∫ w, S'.indicator (fun w => s ^ n * F (c + s • w)) w := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        by_cases hw : w ∈ S'
        · simp only [Set.indicator_of_mem hw, Set.indicator_of_mem ((hmem w).2 hw)]
        · simp only [Set.indicator_of_notMem hw,
            Set.indicator_of_notMem (fun h => hw ((hmem w).1 h)), mul_zero]
    _ = ∫ w in S', s ^ n * F (c + s • w) := integral_indicator hS'
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
        exact (h1 w).symm

end Lib5e


namespace Lib5e

open MeasureTheory Filter Topology Set

theorem norm_le_two_of_close {f g : ℂ} {B δ : ℝ} (h1 : ‖f - g‖ ≤ B * δ) (h2 : ‖g‖ ≤ B)
    (hδ : δ ≤ 1) (hB : 0 ≤ B) : ‖f‖ ≤ 2 * B := by
  have h3 : B * δ ≤ B := mul_le_of_le_one_right hB hδ
  calc ‖f‖ = ‖g + (f - g)‖ := by rw [add_sub_cancel]
    _ ≤ ‖g‖ + ‖f - g‖ := norm_add_le _ _
    _ ≤ 2 * B := by linarith

/-- KL. If `Hₙ → H∞`, `Jₙ → J∞` on `[x, ∞)` with errors `C e^{-cw} δₙ`, `δₙ → 0`, and the limits are
bounded by `C e^{-cw}`, then the kernels `Re ∫₀^∞ Hₙ(u+y) Jₙ(v+y) dy` are measurable, uniformly
bounded by `C' e^{-cu}` on `(x, ∞)²`, and converge pointwise to `Re ∫₀^∞ H∞(u+y) J∞(v+y) dy`. -/
theorem kernel_limit {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (Hn Jn : ι → ℝ → ℂ) (Hi Ji : ℝ → ℂ) (δ : ι → ℝ) (C c x : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hδ : Tendsto δ l (𝓝 0)) (hδ1 : ∀ᶠ i in l, 0 ≤ δ i ∧ δ i ≤ 1)
    (hHn : ∀ᶠ i in l, ∀ w, x ≤ w → ‖Hn i w - Hi w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hJn : ∀ᶠ i in l, ∀ w, x ≤ w → ‖Jn i w - Ji w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hHi : ∀ w, x ≤ w → ‖Hi w‖ ≤ C * Real.exp (-c * w))
    (hJi : ∀ w, x ≤ w → ‖Ji w‖ ≤ C * Real.exp (-c * w))
    (hHc : ∀ᶠ i in l, Continuous (Hn i)) (hJc : ∀ᶠ i in l, Continuous (Jn i)) :
    (∀ᶠ i in l, Measurable (Function.uncurry fun u v : ℝ =>
        (∫ y in Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re)) ∧
    (∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ i in l, ∀ u v : ℝ, x < u → x < v →
        |(∫ y in Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re| ≤ C' * Real.exp (-c * u)) ∧
    (∀ u v : ℝ, x < u → x < v →
      Tendsto (fun i => (∫ y in Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re) l
        (𝓝 (∫ y in Ioi (0 : ℝ), Hi (u + y) * Ji (v + y)).re)) := by
  have hHb : ∀ᶠ i in l, ∀ w, x ≤ w → ‖Hn i w‖ ≤ 2 * (C * Real.exp (-c * w)) := by
    filter_upwards [hHn, hδ1] with i hi hd w hw
    exact norm_le_two_of_close (hi w hw) (hHi w hw) hd.2 (by positivity)
  have hJb : ∀ᶠ i in l, ∀ w, x ≤ w → ‖Jn i w‖ ≤ 2 * (C * Real.exp (-c * w)) := by
    filter_upwards [hJn, hδ1] with i hi hd w hw
    exact norm_le_two_of_close (hi w hw) (hJi w hw) hd.2 (by positivity)
  have hprod : ∀ u v y : ℝ, Real.exp (-c * (u + y)) * Real.exp (-c * (v + y)) =
      Real.exp (-c * u) * Real.exp (-c * v) * Real.exp (-(2 * c) * y) := by
    intro u v y
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hint : IntegrableOn (fun y : ℝ => Real.exp (-(2 * c) * y)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hPb : ∀ᶠ i in l, ∀ u v : ℝ, x < u → x < v → ∀ y : ℝ, 0 < y →
      ‖Hn i (u + y) * Jn i (v + y)‖ ≤
        4 * C ^ 2 * Real.exp (-c * u) * Real.exp (-c * v) * Real.exp (-(2 * c) * y) := by
    filter_upwards [hHb, hJb] with i hH hJ u v hu hv y hy
    rw [norm_mul]
    have h1 := hH (u + y) (by linarith)
    have h2 := hJ (v + y) (by linarith)
    calc ‖Hn i (u + y)‖ * ‖Jn i (v + y)‖
        ≤ (2 * (C * Real.exp (-c * (u + y)))) * (2 * (C * Real.exp (-c * (v + y)))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = 4 * C ^ 2 * (Real.exp (-c * (u + y)) * Real.exp (-c * (v + y))) := by ring
      _ = 4 * C ^ 2 * Real.exp (-c * u) * Real.exp (-c * v) * Real.exp (-(2 * c) * y) := by
          rw [hprod]; ring
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hHc, hJc] with i hH hJ
    have hcont : Continuous (Function.uncurry fun (p : ℝ × ℝ) (y : ℝ) => Hn i (p.1 + y) * Jn i (p.2 + y)) :=
      (hH.comp (continuous_fst.fst.add continuous_snd)).mul (hJ.comp (continuous_fst.snd.add continuous_snd))
    have hsm := hcont.stronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioi (0 : ℝ)))
    exact Complex.measurable_re.comp hsm.measurable
  · set I0 : ℝ := ∫ y in Ioi (0 : ℝ), Real.exp (-(2 * c) * y) with hI0
    have hI0nn : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun y _ => (Real.exp_pos _).le)
    refine ⟨4 * C ^ 2 * Real.exp (-c * x) * I0, by positivity, ?_⟩
    filter_upwards [hPb] with i hP u v hu hv
    have hev : Real.exp (-c * v) ≤ Real.exp (-c * x) := Real.exp_le_exp.2 (by nlinarith)
    calc |(∫ y in Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re|
        ≤ ‖∫ y in Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)‖ := Complex.abs_re_le_norm _
      _ ≤ ∫ y in Ioi (0 : ℝ), 4 * C ^ 2 * Real.exp (-c * u) * Real.exp (-c * v) *
            Real.exp (-(2 * c) * y) := by
          refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
          rw [ae_restrict_iff' measurableSet_Ioi]
          exact Filter.Eventually.of_forall (fun y hy => hP u v hu hv y hy)
      _ = 4 * C ^ 2 * Real.exp (-c * u) * Real.exp (-c * v) * I0 := integral_const_mul _ _
      _ ≤ 4 * C ^ 2 * Real.exp (-c * x) * I0 * Real.exp (-c * u) := by
          have hK : 0 ≤ 4 * C ^ 2 * Real.exp (-c * u) * I0 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hev hK]
  · intro u v hu hv
    have hlimH : ∀ w, x ≤ w → Tendsto (fun i => Hn i w) l (𝓝 (Hi w)) := by
      intro w hw
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun i => C * Real.exp (-c * w) * δ i) l (𝓝 0) := by
        simpa using hδ.const_mul (C * Real.exp (-c * w))
      refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ h0
      filter_upwards [hHn] with i hi using hi w hw
    have hlimJ : ∀ w, x ≤ w → Tendsto (fun i => Jn i w) l (𝓝 (Ji w)) := by
      intro w hw
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h0 : Tendsto (fun i => C * Real.exp (-c * w) * δ i) l (𝓝 0) := by
        simpa using hδ.const_mul (C * Real.exp (-c * w))
      refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ h0
      filter_upwards [hJn] with i hi using hi w hw
    have hT := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun y => 4 * C ^ 2 * Real.exp (-c * u) * Real.exp (-c * v) * Real.exp (-(2 * c) * y))
      (F := fun i y => Hn i (u + y) * Jn i (v + y)) (f := fun y => Hi (u + y) * Ji (v + y))
      (by
        filter_upwards [hHc, hJc] with i hH hJ
        exact ((hH.comp (continuous_const.add continuous_id)).mul
          (hJ.comp (continuous_const.add continuous_id))).aestronglyMeasurable)
      (by
        filter_upwards [hPb] with i hP
        rw [ae_restrict_iff' measurableSet_Ioi]
        exact Filter.Eventually.of_forall (fun y hy => hP u v hu hv y hy))
      (hint.const_mul _)
      (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Filter.Eventually.of_forall (fun y hy => ?_)
        have hy' : (0 : ℝ) < y := hy
        exact (hlimH (u + y) (by linarith)).mul (hlimJ (v + y) (by linarith)))
    exact (Complex.continuous_re.tendsto _).comp hT

open SpikedWishart.SoftEdge in
theorem fredholm_factored_aux (Hn Jn : ℕ → ℝ → ℂ) (Hi Ji : ℝ → ℂ) (δ : ℕ → ℝ) (C c x : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδ1 : ∀ᶠ i in Filter.atTop, 0 ≤ δ i ∧ δ i ≤ 1)
    (hHn : ∀ᶠ i in Filter.atTop, ∀ w, x ≤ w → ‖Hn i w - Hi w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hJn : ∀ᶠ i in Filter.atTop, ∀ w, x ≤ w → ‖Jn i w - Ji w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hHi : ∀ w, x ≤ w → ‖Hi w‖ ≤ C * Real.exp (-c * w))
    (hJi : ∀ w, x ≤ w → ‖Ji w‖ ≤ C * Real.exp (-c * w))
    (hHc : ∀ᶠ i in Filter.atTop, Continuous (Hn i))
    (hJc : ∀ᶠ i in Filter.atTop, Continuous (Jn i)) :
    Filter.Tendsto
      (fun i => fredholmDet (fun u v => (∫ y in Set.Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re) x)
      Filter.atTop
      (nhds (fredholmDet (fun u v => (∫ y in Set.Ioi (0 : ℝ), Hi (u + y) * Ji (v + y)).re) x)) := by
  obtain ⟨hm, ⟨C', hC', hb⟩, hl⟩ := kernel_limit Hn Jn Hi Ji δ C c x hC hc hδ hδ1 hHn hJn hHi hJi hHc hJc
  unfold fredholmDet
  exact fredholm_series_tendsto (fun i u v => (∫ y in Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re)
    (fun u v => (∫ y in Ioi (0 : ℝ), Hi (u + y) * Ji (v + y)).re) C' c x hC' hc hm hb hl

end Lib5e

open SpikedWishart.SoftEdge MeasureTheory in
theorem solution (Hn Jn : ℕ → ℝ → ℂ) (Hi Ji : ℝ → ℂ) (δ : ℕ → ℝ) (C c x : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hδ1 : ∀ᶠ i in Filter.atTop, 0 ≤ δ i ∧ δ i ≤ 1)
    (hHn : ∀ᶠ i in Filter.atTop, ∀ w, x ≤ w → ‖Hn i w - Hi w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hJn : ∀ᶠ i in Filter.atTop, ∀ w, x ≤ w → ‖Jn i w - Ji w‖ ≤ C * Real.exp (-c * w) * δ i)
    (hHi : ∀ w, x ≤ w → ‖Hi w‖ ≤ C * Real.exp (-c * w))
    (hJi : ∀ w, x ≤ w → ‖Ji w‖ ≤ C * Real.exp (-c * w))
    (hHc : ∀ᶠ i in Filter.atTop, Continuous (Hn i))
    (hJc : ∀ᶠ i in Filter.atTop, Continuous (Jn i)) :
    Filter.Tendsto
      (fun i => fredholmDet (fun u v => (∫ y in Set.Ioi (0 : ℝ), Hn i (u + y) * Jn i (v + y)).re) x)
      Filter.atTop
      (nhds (fredholmDet (fun u v => (∫ y in Set.Ioi (0 : ℝ), Hi (u + y) * Ji (v + y)).re) x)) := by
  exact Lib5e.fredholm_factored_aux Hn Jn Hi Ji δ C c x hC hc hδ hδ1 hHn hJn hHi hJi hHc hJc
