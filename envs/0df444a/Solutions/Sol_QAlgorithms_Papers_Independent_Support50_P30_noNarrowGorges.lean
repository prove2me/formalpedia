-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.noNarrowGorges
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:19:03.366279+00:00
-- url     : https://prove2.me/submissions/0f92df44-20fb-41c6-b3bc-74504fc4b42a

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30
noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

open scoped Matrix ComplexOrder
section S169E1
open scoped MatrixOrder
theorem S169E_quad {ι : Type*} [Fintype ι] [DecidableEq ι] (O : Matrix ι ι ℂ) (w : ι → ℂ) :
    ‖star w ⬝ᵥ (O *ᵥ w)‖ ≤ QAlgorithms.specNorm O * ∑ j, ‖w j‖ ^ 2 := by
  set x : EuclideanSpace ℂ ι := WithLp.toLp 2 w
  have h1 : star w ⬝ᵥ (O *ᵥ w) = inner ℂ x ((EuclideanSpace.equiv ι ℂ).symm (O *ᵥ x)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
  rw [h1]
  refine (norm_inner_le_norm _ _).trans ?_
  have h2 := Matrix.l2_opNorm_mulVec O x
  have hx : ‖x‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  unfold QAlgorithms.specNorm
  calc ‖x‖ * ‖(EuclideanSpace.equiv ι ℂ).symm (O *ᵥ x)‖ ≤ ‖x‖ * (‖O‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖O‖ * ‖x‖ ^ 2 := by ring
    _ = _ := by rw [hx]

theorem S169E_trbound {ι : Type*} [Fintype ι] [DecidableEq ι] (σ O : Matrix ι ι ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1) : |(σ * O).trace.re| ≤ QAlgorithms.specNorm O := by
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hσ.nonneg
  rw [Matrix.star_eq_conjTranspose] at hD
  set w : ι → ι → ℂ := fun k j => star (D k j)
  have hkk : ∀ k, (D * O * Dᴴ) k k = star (w k) ⬝ᵥ (O *ᵥ w k) := by
    intro k
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, w,
      Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have htr' : (σ * O).trace = ∑ k, star (w k) ⬝ᵥ (O *ᵥ w k) := by
    rw [hD, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [Matrix.trace]; exact Finset.sum_congr rfl fun k _ => hkk k
  have hnorm : ∑ k, ∑ j, ‖w k j‖ ^ 2 = 1 := by
    have : σ.trace = ∑ k, ∑ j, ((‖w k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [hD, Matrix.trace_mul_comm, Matrix.trace]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [norm_star, Complex.star_def, Complex.mul_conj']; push_cast; rfl
    rw [htr] at this
    have := congrArg Complex.re this
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at this
    linarith
  rw [htr']
  calc |(∑ k, star (w k) ⬝ᵥ (O *ᵥ w k)).re| ≤ ‖∑ k, star (w k) ⬝ᵥ (O *ᵥ w k)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ∑ k, ‖star (w k) ⬝ᵥ (O *ᵥ w k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, QAlgorithms.specNorm O * ∑ j, ‖w k j‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => S169E_quad O (w k)
    _ = QAlgorithms.specNorm O := by rw [← Finset.mul_sum, hnorm, mul_one]
end S169E1
set_option backward.isDefEq.respectTransparency false in
theorem S169E_exp_cont {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun A : Matrix ι ι ℂ => NormedSpace.exp A) := by
  open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous

theorem S169E_layer_unitary {n : ℕ} (H : QnnOperator n) (hH : H.IsHermitian) (t : ℝ) :
    qnnLayer H t ∈ Matrix.unitaryGroup (QAlgorithms.Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  unfold qnnLayer
  rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hH.eq,
    ← Matrix.exp_add_of_commute]
  · have : star (-Complex.I * (t : ℂ)) • H + (-Complex.I * (t : ℂ)) • H = 0 := by
      rw [← add_smul]; simp [Complex.star_def]
    rw [this, NormedSpace.exp_zero]
  · exact (Commute.refl H).smul_left _ |>.smul_right _

theorem S169E_circuit_unitary {n L : ℕ} (H : Fin L → QnnOperator n) (hH : ∀ j, (H j).IsHermitian)
    (t : Fin L → ℝ) : circuit H t ∈ Matrix.unitaryGroup (QAlgorithms.Qubits n) ℂ := by
  unfold circuit QAlgorithms.orderedProd
  apply Submonoid.list_prod_mem
  intro x hx
  rw [List.mem_reverse, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  exact S169E_layer_unitary _ (hH j) _

theorem S169E_circuit_cont {n L : ℕ} (H : Fin L → QnnOperator n) :
    Continuous (fun t : Fin L → ℝ => circuit H t) := by
  unfold circuit QAlgorithms.orderedProd
  have e : ∀ t : Fin L → ℝ, (List.ofFn fun j => qnnLayer (H j) (t j)).reverse =
      (List.finRange L).reverse.map (fun j => qnnLayer (H j) (t j)) := by
    intro t; rw [List.ofFn_eq_map, List.map_reverse]
  simp_rw [e]
  apply continuous_list_prod
  intro j _
  unfold qnnLayer
  exact S169E_exp_cont.comp (((continuous_const.mul
    (Complex.continuous_ofReal.comp (continuous_apply j))).smul continuous_const))


theorem S169E_prob (L : ℕ) : IsProbabilityMeasure (uniformParameters L) := by
  have h0 : IsProbabilityMeasure ((ENNReal.ofReal (1 / (2 * Real.pi))) •
      (volume : Measure ℝ).restrict (Set.Icc 0 (2 * Real.pi))) := by
    constructor
    simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [sub_zero, one_div, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
  unfold uniformParameters
  infer_instance

theorem S169E_var {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, |f x| ≤ K) (δ : ℝ) :
    variance μ f ≤ δ ^ 2 + 4 * K ^ 2 * (μ {x | δ ≤ |f x - ∫ t, f t ∂μ|}).toReal := by
  set m := ∫ t, f t ∂μ with hm
  have hint : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable K (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hK x)
  have hint2 : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (K ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hK x) 2)
  have hmK : |m| ≤ K := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := K)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hK x)
    simpa [Real.norm_eq_abs] using this
  have hvar : variance μ f = ∫ x, (f x - m) ^ 2 ∂μ := by
    unfold variance
    have e : ∀ x, (f x - m) ^ 2 = f x ^ 2 - 2 * m * f x + m ^ 2 := fun x => by ring
    simp_rw [e]
    rw [integral_add (f := fun x => f x ^ 2 - 2 * m * f x) (g := fun _ => m ^ 2)
      (hint2.sub (hint.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * m * f x) hint2 (hint.const_mul _),
      integral_const_mul, integral_const]
    simp [← hm]; ring
  set S := {x | δ ≤ |f x - m|} with hS
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const ((hf.sub measurable_const).abs)
  rw [hvar]
  have hpt : ∀ x, (f x - m) ^ 2 ≤ δ ^ 2 + 4 * K ^ 2 * S.indicator 1 x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      have : |f x - m| ≤ 2 * K := (abs_sub _ _).trans (by linarith [hK x])
      have h2 : (f x - m) ^ 2 ≤ (2 * K) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      nlinarith [sq_nonneg δ]
    · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      simp only [hS, Set.mem_setOf_eq, not_le] at hx
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hx.le 2
  have hint3 : Integrable (fun x => (f x - m) ^ 2) μ :=
    Integrable.of_bound ((hf.sub measurable_const).pow_const 2).aestronglyMeasurable ((2 * K) ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [hK x])) 2)
  have hint4 : Integrable (fun x => δ ^ 2 + 4 * K ^ 2 * S.indicator 1 x) μ :=
    (integrable_const _).add (((integrable_const (1:ℝ)).indicator hSm).const_mul _)
  calc ∫ x, (f x - m) ^ 2 ∂μ ≤ ∫ x, (δ ^ 2 + 4 * K ^ 2 * S.indicator 1 x) ∂μ :=
        integral_mono hint3 hint4 hpt
    _ = δ ^ 2 + 4 * K ^ 2 * (μ S).toReal := by
        rw [integral_add (f := fun _ => δ ^ 2) (g := fun x => 4 * K ^ 2 * S.indicator 1 x)
          (integrable_const _) (((integrable_const (1:ℝ)).indicator hSm).const_mul _),
          integral_const, integral_const_mul, integral_indicator_one hSm]
        simp [measureReal_def]

theorem S169_main (K : ℝ) (hK : 0 < K) (L : ℕ → ℕ)
    (H : (n : ℕ) → Fin (L n) → QnnOperator n) (hH : ∀ n j, (H n j).IsHermitian)
    (hHeq : ∀ n j, PermutationEquivariant (H n j))
    (rho : (n : ℕ) → QnnDensity n) (O : (n : ℕ) → QnnOperator n)
    (hO : ∀ n, (O n).IsHermitian) (hOeq : ∀ n, PermutationEquivariant (O n))
    (hbound : ∀ n, QAlgorithms.specNorm (O n) ≤ K)
    (hvariance : InversePolynomialLower
      (fun n => variance (uniformParameters (L n)) (fun t => qnnLoss (circuit (H n) t) (rho n).val (O n)))) :
    ¬ HasNarrowGorge L (fun n t => qnnLoss (circuit (H n) t) (rho n).val (O n)) := by
  rintro ⟨-, C, b, hC, hb, N1, htail⟩
  obtain ⟨c, hc, k, N2, hvar⟩ := hvariance
  have hfK : ∀ n t, |qnnLoss (circuit (H n) t) (rho n).val (O n)| ≤ K := by
    intro n t
    have hU := S169E_circuit_unitary (H n) (hH n) t
    rw [Matrix.mem_unitaryGroup_iff'] at hU
    have hσ : (circuit (H n) t * (rho n).val * (circuit (H n) t)ᴴ).PosSemidef :=
      (rho n).2.1.mul_mul_conjTranspose_same _
    have htr : (circuit (H n) t * (rho n).val * (circuit (H n) t)ᴴ).trace = 1 := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        hU, Matrix.mul_one]
      exact (rho n).2.2
    exact (S169E_trbound _ (O n) hσ htr).trans (hbound n)
  have hfc : ∀ n, Continuous (fun t => qnnLoss (circuit (H n) t) (rho n).val (O n)) := by
    intro n
    have := S169E_circuit_cont (H n)
    unfold qnnLoss
    exact Complex.continuous_re.comp ((((this.matrix_mul continuous_const).matrix_mul
      this.matrix_conjTranspose).matrix_mul continuous_const).matrix_trace)
  have hsb : 1 < Real.sqrt b := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) hb
  set r := (Real.sqrt b)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hsb
  have hbr : b * r = Real.sqrt b := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ b by linarith)
    rw [hr]; field_simp; linarith
  have key : ∀ n ≥ max N1 N2, c / (n:ℝ) ^ k ≤ (1 + 4 * K ^ 2 * C) * r ^ n := by
    intro n hn
    have := S169E_prob (L n)
    set δ := Real.sqrt (r ^ n)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (pow_pos hr0 n)
    have hδ2 : δ ^ 2 = r ^ n := Real.sq_sqrt (pow_pos hr0 n).le
    have h1 := hvar n (le_of_max_le_right hn)
    have h2 := S169E_var (uniformParameters (L n)) _ (hfc n).measurable K hK.le (hfK n) δ
    have h3 := htail n (le_of_max_le_left hn) δ hδ
    have h4 : C / (b ^ n * δ ^ 2) = C * r ^ n := by
      rw [hδ2, ← mul_pow, hbr]
      have : Real.sqrt b ^ n * r ^ n = 1 := by
        rw [← mul_pow, hr, mul_inv_cancel₀ (by positivity), one_pow]
      field_simp
      nlinarith [this]
    rw [h4] at h3
    calc c / (n:ℝ) ^ k ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ r ^ n + 4 * K ^ 2 * (C * r ^ n) := by
          rw [hδ2]; gcongr
      _ = (1 + 4 * K ^ 2 * C) * r ^ n := by ring
  have hlim := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by rw [abs_of_pos hr0]; exact hr1)
  have hpos : 0 < c / (1 + 4 * K ^ 2 * C) := by positivity
  have hev := (hlim.eventually (gt_mem_nhds hpos)).and
    (Filter.eventually_ge_atTop (max (max N1 N2) 1))
  obtain ⟨n, hn2, hn1⟩ := hev.exists
  have hn0 : (0:ℝ) < (n:ℝ) ^ k := by
    have : (1:ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn1
    positivity
  have := key n (le_of_max_le_left hn1)
  rw [div_le_iff₀ hn0] at this
  rw [lt_div_iff₀ (by positivity)] at hn2
  nlinarith
end QAlgorithms.Papers.Independent.Support50.P30

end

open MeasureTheory
open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P30 in
theorem solution (K : ℝ) (hK : 0 < K) (L : ℕ → ℕ)
    (H : (n : ℕ) → Fin (L n) → QnnOperator n) (hH : ∀ n j, (H n j).IsHermitian)
    (hHeq : ∀ n j, PermutationEquivariant (H n j))
    (rho : (n : ℕ) → QnnDensity n) (O : (n : ℕ) → QnnOperator n)
    (hO : ∀ n, (O n).IsHermitian) (hOeq : ∀ n, PermutationEquivariant (O n))
    (hbound : ∀ n, QAlgorithms.specNorm (O n) ≤ K)
    (hvariance : InversePolynomialLower
      (fun n => variance (uniformParameters (L n)) (fun t => qnnLoss (circuit (H n) t) (rho n).val (O n)))) :
    ¬ HasNarrowGorge L (fun n t => qnnLoss (circuit (H n) t) (rho n).val (O n)) :=
  S169_main K hK L H hH hHeq rho O hO hOeq hbound hvariance
