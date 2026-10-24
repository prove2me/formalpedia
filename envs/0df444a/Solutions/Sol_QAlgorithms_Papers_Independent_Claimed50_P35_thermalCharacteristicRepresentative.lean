-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P35.thermalCharacteristicRepresentative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:15:44.745852+00:00
-- url     : https://prove2.me/submissions/f3ce5f46-168e-4024-a587-bc4c2a4434eb

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory Finset

open scoped Topology ENNReal NNReal BigOperators

namespace X7D15TC

/-- finite Laguerre polynomial `L_n(x) = Σ_k C(n,k) (-x)^k / k!` -/
def EL (m : ℕ) (x : ℝ) : ℝ := ∑ i ∈ range (m + 1), (m.choose i : ℝ) * (-x) ^ i / i.factorial

def ff (r x : ℝ) (p : ℕ × ℕ) : ℝ := r ^ p.1 * ((p.1.choose p.2 : ℝ) * (-x) ^ p.2 / p.2.factorial)

lemma choose_geom (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (n.choose k : ℝ) * r ^ n) (r ^ k / (1 - r) ^ (k + 1)) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k
    (r := r) (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  have h2 : HasSum (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ (n + k)) (r ^ k / (1 - r) ^ (k + 1)) := by
    have := h.mul_left (r ^ k)
    have e : (fun n : ℕ => ((n + k).choose k : ℝ) * r ^ (n + k)) =
        fun i => r ^ k * (((i + k).choose k : ℝ) * r ^ i) := by
      funext n; rw [pow_add]; ring
    rw [e, show r ^ k / (1 - r) ^ (k + 1) = r ^ k * (1 / (1 - r) ^ (k + 1)) by ring]
    exact this
  rw [← hasSum_nat_add_iff' k]
  convert h2 using 1
  · ext n; simp
  · rw [sub_eq_self]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt hi]; simp

lemma ff_abs (r x : ℝ) (hr0 : 0 ≤ r) (p : ℕ × ℕ) :
    ‖ff r x p‖ = ff r (-|x|) p := by
  unfold ff
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 _), neg_neg]
  congr 1
  rw [abs_div, abs_mul, abs_pow, abs_neg]
  simp

lemma ff_fiber_k (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    HasSum (fun n : ℕ => ff r x (n, k)) ((-x) ^ k / k.factorial * (r ^ k / (1 - r) ^ (k + 1))) := by
  have := (choose_geom k hr0 hr1).mul_left ((-x) ^ k / k.factorial)
  have e : (fun n : ℕ => ff r x (n, k)) = fun n => (-x) ^ k / k.factorial * ((n.choose k : ℝ) * r ^ n) := by
    funext n; unfold ff; ring
  rw [e]; exact this

lemma exp_part (r x : ℝ) (hr1 : r < 1) :
    HasSum (fun k : ℕ => (-x) ^ k / k.factorial * (r ^ k / (1 - r) ^ (k + 1)))
      (Real.exp (-x * r / (1 - r)) / (1 - r)) := by
  have hpos : 0 < 1 - r := by linarith
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-x * r / (1 - r))
  rw [← Real.exp_eq_exp_ℝ] at h
  have := h.div_const (1 - r)
  have e : (fun k : ℕ => (-x) ^ k / k.factorial * (r ^ k / (1 - r) ^ (k + 1))) =
      fun k => (-x * r / (1 - r)) ^ k / k.factorial / (1 - r) := by
    funext k
    rw [div_pow, mul_pow, pow_succ]
    field_simp
  rw [e]; exact this

lemma ff_summable (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : Summable (ff r x) := by
  apply Summable.of_norm
  have e : (fun p => ‖ff r x p‖) = ff r (-|x|) := funext (ff_abs r x hr0)
  rw [e]
  have hnn : ∀ p, 0 ≤ ff r (-|x|) p := by
    intro p; unfold ff; rw [neg_neg]; positivity
  have hsw : Summable (fun q : ℕ × ℕ => ff r (-|x|) q.swap) := by
    rw [summable_prod_of_nonneg (fun q => hnn _)]
    refine ⟨fun k => (ff_fiber_k r (-|x|) hr0 hr1 k).summable, ?_⟩
    have e2 : (fun k : ℕ => ∑' n, ff r (-|x|) (k, n).swap) =
        fun k => (-(-|x|)) ^ k / k.factorial * (r ^ k / (1 - r) ^ (k + 1)) := by
      ext k; exact (ff_fiber_k r (-|x|) hr0 hr1 k).tsum_eq
    rw [e2]
    exact (exp_part r (-|x|) hr1).summable
  exact (Equiv.prodComm ℕ ℕ).symm.summable_iff.mp hsw

lemma ff_fiber_n (r x : ℝ) (n : ℕ) : ∑' k, ff r x (n, k) = r ^ n * EL n x := by
  rw [tsum_eq_sum (s := range (n + 1))]
  · unfold ff EL; rw [Finset.mul_sum]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    unfold ff
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- Laguerre generating function. -/
lemma laguerre_gen (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => r ^ n * EL n x) (Real.exp (-x * r / (1 - r)) / (1 - r)) := by
  have hs := ff_summable r x hr0 hr1
  have h1 := hs.hasSum.prod_fiberwise (fun b => (hs.prod_factor b).hasSum)
  have hsw : Summable (fun q : ℕ × ℕ => ff r x q.swap) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hs
  have h2 := hsw.hasSum.prod_fiberwise (fun b => (hsw.prod_factor b).hasSum)
  have e2 : (fun k : ℕ => ∑' n, ff r x (k, n).swap) =
      fun k => (-x) ^ k / k.factorial * (r ^ k / (1 - r) ^ (k + 1)) := by
    ext k; exact (ff_fiber_k r x hr0 hr1 k).tsum_eq
  rw [e2] at h2
  have hv : ∑' q : ℕ × ℕ, ff r x q.swap = ∑' q, ff r x q :=
    (Equiv.prodComm ℕ ℕ).tsum_eq (ff r x)
  rw [hv] at h2
  have := h2.unique (exp_part r x hr1)
  rw [← this]
  have e : (fun n : ℕ => r ^ n * EL n x) = fun n => ∑' k, ff r x (n, k) := by
    funext n; exact (ff_fiber_n r x n).symm
  rw [e]; exact h1


open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

def X7_diagFun (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (x : Hilbert ℕ) : Hilbert ℕ :=
  ⟨fun k => w k * x k, by
        refine Memℓp.mono (g := fun k => C * ‖x k‖) ?_ ?_
        · have := (lp.memℓp x).norm.const_smul C
          convert this using 1
          ext k; simp [smul_eq_mul]
        · intro k; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)⟩

theorem X7_diagFun_apply (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (x : Hilbert ℕ) (k : ℕ) :
    X7_diagFun w C hC x k = w k * x k := rfl

/-- diagonal operator with bounded weights -/
def X7_diagOp (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) : Hilbert ℕ →L[ℂ] Hilbert ℕ :=
  LinearMap.mkContinuous
    { toFun := X7_diagFun w C hC
      map_add' := fun x y => by ext k; simp [X7_diagFun_apply, mul_add]
      map_smul' := fun c x => by ext k; simp [X7_diagFun_apply]; ring }
    C (by
      intro x
      have h0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      have : ‖X7_diagFun w C hC x‖ ≤ ‖(C : ℂ) • x‖ := by
        apply lp.norm_mono (by norm_num)
        intro i
        rw [X7_diagFun_apply, lp.coeFn_smul, Pi.smul_apply, norm_mul, norm_smul]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
      refine this.trans (le_of_eq ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0])

theorem X7_diagOp_apply (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (x : Hilbert ℕ) (k : ℕ) :
    X7_diagOp w C hC x k = w k * x k := rfl

theorem X7_diagOp_ext {w v : ℕ → ℂ} {C C' : ℝ} (hC : ∀ k, ‖w k‖ ≤ C) (hC' : ∀ k, ‖v k‖ ≤ C')
    (h : ∀ k, w k = v k) : X7_diagOp w C hC = X7_diagOp v C' hC' := by
  ext x k; simp [X7_diagOp_apply, h k]

theorem X7_diagOp_mul (w v : ℕ → ℂ) (C C' : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (hC' : ∀ k, ‖v k‖ ≤ C')
    (hCC : ∀ k, ‖w k * v k‖ ≤ C * C') :
    X7_diagOp w C hC * X7_diagOp v C' hC' = X7_diagOp (fun k => w k * v k) (C * C') hCC := by
  ext x k; simp [X7_diagOp_apply, mul_assoc]

theorem X7_diagOp_adjoint (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C)
    (hC' : ∀ k, ‖star (w k)‖ ≤ C) :
    ContinuousLinearMap.adjoint (X7_diagOp w C hC) = X7_diagOp (fun k => star (w k)) C hC' := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; ext k
  simp only [X7_diagOp_apply, RCLike.inner_apply, map_mul, RCLike.star_def]
  simp only [Complex.conj_conj]; ring

theorem X7_diagOp_single [DecidableEq ℕ] (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (j : ℕ) :
    X7_diagOp w C hC (lp.single 2 j 1) = w j • lp.single 2 j 1 := by
  ext k
  rw [X7_diagOp_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem X7_single_eq_smul [DecidableEq ℕ] (j : ℕ) (c : ℂ) :
    lp.single 2 j c = c • (lp.single 2 j 1 : Hilbert ℕ) := by
  ext k
  rw [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, lp.single_apply]
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem X7_clm_ext_single [DecidableEq ℕ] (A B : Hilbert ℕ →L[ℂ] Hilbert ℕ)
    (h : ∀ j, A (lp.single 2 j 1) = B (lp.single 2 j 1)) : A = B := by
  ext1 x
  have hx := lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) x
  have hA := hx.mapL A
  have hB := hx.mapL B
  refine hA.unique ?_
  convert hB using 1
  ext1 j
  show A (lp.single 2 j (x j)) = B (lp.single 2 j (x j))
  rw [X7_single_eq_smul, map_smul, map_smul, h]

theorem X7_bo_eq (X : Matrix ℕ ℕ ℂ) (A : Hilbert ℕ →L[ℂ] Hilbert ℕ) (h : operatorCoeff A = X) :
    boundedOperator X = A := by
  have hex : ∃ A : Hilbert ℕ →L[ℂ] Hilbert ℕ, operatorCoeff A = X := ⟨A, h⟩
  unfold boundedOperator
  rw [dif_pos hex]
  apply @X7_clm_ext_single (fun a b => Classical.propDecidable (a = b))
  intro j
  have h1 := hex.choose_spec
  ext k
  have e1 := congrFun (congrFun h1 k) j
  have e2 := congrFun (congrFun h k) j
  unfold operatorCoeff at e1 e2
  exact e1.trans e2.symm


lemma X7_g68i_cs_lp (a b : Hilbert ℕ) (s : Finset ℕ) :
    ∑ i ∈ s, ‖a i‖ * ‖b i‖ ≤ ‖a‖ * ‖b‖ := by
  have h2 : ∀ f : Hilbert ℕ, Real.sqrt (∑ i ∈ s, ‖f i‖ ^ 2) ≤ ‖f‖ := by
    intro f
    have := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) f s
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    rw [Real.sqrt_le_left]
    · exact this
    · exact norm_nonneg _
  exact (Real.sum_mul_le_sqrt_mul_sqrt s _ _).trans
    (mul_le_mul (h2 a) (h2 b) (Real.sqrt_nonneg _) (norm_nonneg _))

lemma X7_g68i_smul_apply (c : ℂ) (v : Hilbert ℕ) (k : ℕ) : (c • v) k = c * v k := rfl

lemma X7_g68i_diag_ts (d : ℕ → ℝ) (hs : Summable (fun n => |d n|)) (X : Matrix ℕ ℕ ℂ)
    (hX : ∀ i j, X i j = if i = j then (d i : ℂ) else 0) :
    IsTraceClass X ∧ traceSize X = ENNReal.ofReal (∑' n, |d n|) := by
  let e : NuclearExpansion X :=
    { left := fun n => (d n : ℂ) • lp.single 2 n (1 : ℂ)
      right := fun n => lp.single 2 n (1 : ℂ)
      summable := by
        refine hs.congr (fun n => ?_)
        rw [norm_smul, lp.norm_single (p := 2) (by norm_num)]
        simp
      coefficients := by
        intro i j
        simp only [X7_g68i_smul_apply]
        rw [hX, tsum_eq_single i]
        · by_cases hij : i = j
          · subst hij; simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply]
          · simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply, hij, Ne.symm hij]
        · intro n hn
          simp [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply, Pi.single_apply, Ne.symm hn] }
  refine ⟨⟨e⟩, le_antisymm ?_ ?_⟩
  · refine iInf_le_of_le e (le_of_eq ?_)
    congr 1
    refine tsum_congr (fun n => ?_)
    simp only [e]
    rw [norm_smul, lp.norm_single (p := 2) (by norm_num)]
    simp
  · refine le_iInf (fun f => ENNReal.ofReal_le_ofReal ?_)
    refine Real.tsum_le_of_sum_le (fun n => abs_nonneg _) (fun s => ?_)
    have hb : ∀ i, |d i| ≤ ∑' n, ‖f.left n i‖ * ‖f.right n i‖ := by
      intro i
      have hc := f.coefficients i i
      rw [hX, if_pos rfl] at hc
      have hb1 : ∀ n, ‖f.left n i * star (f.right n i)‖ ≤ ‖f.left n‖ * ‖f.right n‖ := by
        intro n
        rw [norm_mul, norm_star]
        exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
          (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
      have hsm : Summable (fun n => ‖f.left n i * star (f.right n i)‖) :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb1 f.summable
      have : |d i| = ‖(d i : ℂ)‖ := by simp
      rw [this, hc]
      refine (norm_tsum_le_tsum_norm hsm).trans (le_of_eq ?_)
      refine tsum_congr (fun n => ?_)
      rw [norm_mul, norm_star]
    have hsm2 : ∀ i, Summable (fun n => ‖f.left n i‖ * ‖f.right n i‖) := by
      intro i
      refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) f.summable
      exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
          (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
    calc ∑ i ∈ s, |d i| ≤ ∑ i ∈ s, ∑' n, ‖f.left n i‖ * ‖f.right n i‖ :=
          Finset.sum_le_sum (fun i _ => hb i)
      _ = ∑' n, ∑ i ∈ s, ‖f.left n i‖ * ‖f.right n i‖ :=
          (Summable.tsum_finsetSum (fun i _ => hsm2 i)).symm
      _ ≤ ∑' n, ‖f.left n‖ * ‖f.right n‖ := by
          refine Summable.tsum_le_tsum (fun n => X7_g68i_cs_lp _ _ s) ?_ f.summable
          exact summable_sum (fun i _ => hsm2 i)


lemma diag_D (ξ : ℂ) (i : ℕ) :
    QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix ξ i i =
      ((Real.exp (-Complex.normSq ξ / 2) * EL i (Complex.normSq ξ) : ℝ) : ℂ) := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P39.displacementMatrix EL
  rw [min_self]
  have hw : ∀ m : ℕ, ξ ^ m * (-star ξ) ^ m = (((-Complex.normSq ξ) ^ m : ℝ) : ℂ) := by
    intro m
    rw [← mul_pow]
    congr 1
    rw [mul_neg, Complex.star_def, Complex.mul_conj]; push_cast; ring
  have hsq : Real.sqrt ((i.factorial : ℝ) * (i.factorial : ℝ)) = i.factorial :=
    Real.sqrt_mul_self (by positivity)
  rw [hsq]
  rw [← Finset.sum_range_reflect (fun k => (i.choose k : ℝ) * (-Complex.normSq ξ) ^ k / k.factorial) (i + 1)]
  push_cast
  rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hji : j ≤ i := by omega
  rw [hw]; push_cast
  have hc : (i.choose (i - j) : ℂ) = (i.factorial : ℂ) / ((j.factorial : ℂ) * ((i - j).factorial : ℂ)) := by
    rw [Nat.choose_symm hji]
    have := Nat.choose_mul_factorial_mul_factorial hji
    have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have h2 : ((i - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (i - j).factorial_ne_zero
    rw [eq_div_iff (mul_ne_zero h1 h2)]
    rw [← mul_assoc]; exact_mod_cast this
  rw [hc]
  congr 1
  have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h2 : ((i - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (i - j).factorial_ne_zero
  push_cast
  field_simp

end X7D15TC

end

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open X7D15TC in
theorem solution (k Nc hbar : ℝ)
    (hk : 0 ≤ k) (hNc : 0 ≤ Nc) (hhbar : 0 < hbar) (hk1 : k ^ 2 ≠ 1) :
    RealizedDensity (generalizedThermal (1 / 2 + Nc / |k ^ 2 - 1|)) ∧
    ∀ z : ℂ, oneModeCharacteristic hbar
      (generalizedThermal (1 / 2 + Nc / |k ^ 2 - 1|)) z =
        oneModeMultiplier k Nc hbar (defectRescale k z) ∧
      oneModeMultiplier k Nc hbar (defectRescale k z) = Complex.exp (((-hbar * (|k ^ 2 - 1| / 2 + Nc) /
          (2 * |k ^ 2 - 1|) * Complex.normSq z : ℝ) : ℂ)) := by
  have hd : 0 < |k ^ 2 - 1| := abs_pos.mpr (sub_ne_zero.mpr hk1)
  set c := Nc / |k ^ 2 - 1| with hc
  have hc0 : 0 ≤ c := div_nonneg hNc hd.le
  set r := c / (1 + c) with hr
  have hr0 : 0 ≤ r := div_nonneg hc0 (by linarith)
  have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
  have h1r : 1 - r = 1 / (1 + c) := by rw [hr]; field_simp; ring
  set p : ℕ → ℝ := fun n => (1 - r) * r ^ n with hp
  have hp0 : ∀ n, 0 ≤ p n := fun n => mul_nonneg (by linarith) (pow_nonneg hr0 n)
  have hX : ∀ i j, generalizedThermal (1 / 2 + c) i j = if i = j then ((p i : ℝ) : ℂ) else 0 := by
    intro i j
    simp only [generalizedThermal, thermalMatrix, hp]
    split_ifs with h
    · subst h
      congr 2
      · rw [h1r]; field_simp; ring
      · rw [hr]; congr 1; field_simp; ring
    · rfl
  have hps : HasSum p 1 := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 - r)
    rwa [mul_inv_cancel₀ (by linarith)] at this
  have hpabs : Summable (fun n => |p n|) := by
    refine hps.summable.congr (fun n => ?_)
    rw [abs_of_nonneg (hp0 n)]
  have hC : ∀ n, ‖((p n : ℝ) : ℂ)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 n)]
    exact le_hasSum hps n (fun m _ => hp0 m)
  refine ⟨⟨⟨(X7_g68i_diag_ts p hpabs _ hX).1, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro s z
    have hq : (∑ i ∈ s, ∑ j ∈ s, star (z i) * generalizedThermal (1 / 2 + c) i j * z j) =
        ((∑ i ∈ s, p i * Complex.normSq (z i) : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      simp only [hX, mul_ite, ite_mul, mul_zero, zero_mul]
      rw [Finset.sum_ite_eq s i (fun j => star (z i) * ((p i : ℝ) : ℂ) * z j), if_pos hi]
      rw [Complex.normSq_eq_conj_mul_self]
      simp only [Complex.star_def]; ring
    rw [hq, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨rfl, Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (Complex.normSq_nonneg _))⟩
  · have e : (fun i => (generalizedThermal (1 / 2 + c) i i).re) = p := by
      funext i; rw [hX, if_pos rfl, Complex.ofReal_re]
    rw [e]; exact hps.summable
  · have e : (fun i => (generalizedThermal (1 / 2 + c) i i).re) = p := by
      funext i; rw [hX, if_pos rfl, Complex.ofReal_re]
    rw [e]; exact hps.tsum_eq
  · have hco : operatorCoeff (X7_diagOp (fun n => ((p n : ℝ) : ℂ)) 1 hC) = generalizedThermal (1 / 2 + c) := by
      ext i j
      unfold operatorCoeff
      have h1 := @X7_diagOp_single (fun a b => Classical.propDecidable (a = b)) (fun n => ((p n : ℝ) : ℂ)) 1 hC j
      have h2 := congrArg (fun f : Hilbert ℕ => f i) h1
      refine h2.trans ?_
      rw [hX]
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [X7_bo_eq _ _ hco, hco]
  · intro z
    have hmul : oneModeMultiplier k Nc hbar (defectRescale k z) = Complex.exp (((-hbar * (|k ^ 2 - 1| / 2 + Nc) /
          (2 * |k ^ 2 - 1|) * Complex.normSq z : ℝ) : ℂ)) := by
      unfold oneModeMultiplier defectRescale
      congr 2
      have hn : Complex.normSq ((if k ≤ 1 then z else star z) / (Real.sqrt |k ^ 2 - 1| : ℂ)) =
          Complex.normSq z / |k ^ 2 - 1| := by
        rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hd.le]
        split_ifs
        · rfl
        · rw [Complex.star_def, Complex.normSq_conj]
      rw [hn]; field_simp
    refine ⟨?_, hmul⟩
    rw [hmul]
    set ξ : ℂ := Complex.I * (Real.sqrt (hbar / 2) : ℂ) * z with hξ
    set x := Complex.normSq ξ with hx
    have hxv : x = hbar / 2 * Complex.normSq z := by
      rw [hx, hξ, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by linarith)]; ring
    have hterm : ∀ i, (∑' j, generalizedThermal (1 / 2 + c) i j * displacementMatrix ξ j i) =
        (((1 - r) * Real.exp (-x / 2) * (r ^ i * EL i x) : ℝ) : ℂ) := by
      intro i
      rw [tsum_eq_single i]
      · rw [hX, if_pos rfl, diag_D]; simp only [hp]; push_cast; ring
      · intro j hj; rw [hX, if_neg (Ne.symm hj), zero_mul]
    unfold oneModeCharacteristic tracePair
    rw [← hξ]
    simp_rw [hterm]
    rw [← Complex.ofReal_tsum]
    have hs := (laguerre_gen r x hr0 hr1).mul_left ((1 - r) * Real.exp (-x / 2))
    rw [hs.tsum_eq, ← Complex.ofReal_exp]
    congr 1
    rw [mul_div_assoc', mul_comm (1 - r), mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ (by linarith : (1:ℝ) - r ≠ 0),
      ← Real.exp_add]
    congr 1
    have hrr : r / (1 - r) = c := by rw [h1r, hr]; field_simp
    rw [mul_div_assoc, hrr, hxv, hc]
    field_simp
    ring
