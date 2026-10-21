-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P45.formation_function_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:43:34.172979+00:00
-- url     : https://prove2.me/submissions/4c5fe383-e6c9-461b-905e-bf50bb55d99a

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Next46.P45
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)
open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits)


namespace g62d_ns

def diagFun (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (x : Hilbert ℕ) : Hilbert ℕ :=
  ⟨fun k => w k * x k, by
        refine Memℓp.mono (g := fun k => C * ‖x k‖) ?_ ?_
        · have := (lp.memℓp x).norm.const_smul C
          convert this using 1
          ext k; simp [smul_eq_mul]
        · intro k; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)⟩

theorem diagFun_apply (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (x : Hilbert ℕ) (k : ℕ) :
    diagFun w C hC x k = w k * x k := rfl

/-- diagonal operator with bounded weights -/
def diagOp (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) : Hilbert ℕ →L[ℂ] Hilbert ℕ :=
  LinearMap.mkContinuous
    { toFun := diagFun w C hC
      map_add' := fun x y => by ext k; simp [diagFun_apply, mul_add]
      map_smul' := fun c x => by ext k; simp [diagFun_apply]; ring }
    C (by
      intro x
      have h0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      have : ‖diagFun w C hC x‖ ≤ ‖(C : ℂ) • x‖ := by
        apply lp.norm_mono (by norm_num)
        intro i
        rw [diagFun_apply, lp.coeFn_smul, Pi.smul_apply, norm_mul, norm_smul]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)
      refine this.trans (le_of_eq ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0])

theorem diagOp_apply (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (x : Hilbert ℕ) (k : ℕ) :
    diagOp w C hC x k = w k * x k := rfl

theorem diagOp_ext {w v : ℕ → ℂ} {C C' : ℝ} (hC : ∀ k, ‖w k‖ ≤ C) (hC' : ∀ k, ‖v k‖ ≤ C')
    (h : ∀ k, w k = v k) : diagOp w C hC = diagOp v C' hC' := by
  ext x k; simp [diagOp_apply, h k]

theorem diagOp_mul (w v : ℕ → ℂ) (C C' : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (hC' : ∀ k, ‖v k‖ ≤ C')
    (hCC : ∀ k, ‖w k * v k‖ ≤ C * C') :
    diagOp w C hC * diagOp v C' hC' = diagOp (fun k => w k * v k) (C * C') hCC := by
  ext x k; simp [diagOp_apply, mul_assoc]

theorem diagOp_adjoint (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C)
    (hC' : ∀ k, ‖star (w k)‖ ≤ C) :
    ContinuousLinearMap.adjoint (diagOp w C hC) = diagOp (fun k => star (w k)) C hC' := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; ext k
  simp only [diagOp_apply, RCLike.inner_apply, map_mul, RCLike.star_def]
  simp only [Complex.conj_conj]; ring

theorem diagOp_single [DecidableEq ℕ] (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (j : ℕ) :
    diagOp w C hC (lp.single 2 j 1) = w j • lp.single 2 j 1 := by
  ext k
  rw [diagOp_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem mem_spectrum_diag (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (j : ℕ) :
    w j ∈ spectrum ℂ (diagOp w C hC) := by
  rw [spectrum.mem_iff]
  rintro ⟨u, hu⟩
  have h1 : (algebraMap ℂ (Hilbert ℕ →L[ℂ] Hilbert ℕ) (w j) - diagOp w C hC)
      (lp.single 2 j 1) = 0 := by
    rw [ContinuousLinearMap.sub_apply, diagOp_single]
    simp [Algebra.algebraMap_eq_smul_one]
  have h2 : (u⁻¹ * u : Hilbert ℕ →L[ℂ] Hilbert ℕ) (lp.single 2 j 1) = 0 := by
    rw [ContinuousLinearMap.mul_apply, hu, h1, map_zero]
  rw [Units.inv_mul, ContinuousLinearMap.one_apply] at h2
  have := congrArg (fun f : Hilbert ℕ => f j) h2
  simp at this


theorem diagOp_norm_le (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) (h0 : 0 ≤ C) :
    ‖diagOp w C hC‖ ≤ C := by
  unfold diagOp
  exact LinearMap.mkContinuous_norm_le _ h0 _

/-- the diagonal functional calculus hom -/
def diagHom (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) :
    C(spectrum ℂ (diagOp w C hC), ℂ) →⋆ₐ[ℂ] (Hilbert ℕ →L[ℂ] Hilbert ℕ) where
  toFun g := diagOp (fun k => g ⟨w k, mem_spectrum_diag w C hC k⟩) ‖g‖
    (fun k => ContinuousMap.norm_coe_le_norm g _)
  map_one' := by ext x k; simp [diagOp_apply]
  map_mul' f g := by ext x k; simp [diagOp_apply, mul_assoc]
  map_zero' := by ext x k; simp [diagOp_apply]
  map_add' f g := by ext x k; simp [diagOp_apply, add_mul]
  commutes' r := by ext x k; simp [diagOp_apply, Algebra.algebraMap_eq_smul_one]
  map_star' g := by
    rw [ContinuousLinearMap.star_eq_adjoint, diagOp_adjoint _ _ _
      (fun k => by rw [norm_star]; exact ContinuousMap.norm_coe_le_norm g _)]
    exact diagOp_ext _ _ (fun k => rfl)

theorem diagHom_apply (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C)
    (g : C(spectrum ℂ (diagOp w C hC), ℂ)) (x : Hilbert ℕ) (k : ℕ) :
    diagHom w C hC g x k = g ⟨w k, mem_spectrum_diag w C hC k⟩ * x k := rfl

theorem diagHom_cont (w : ℕ → ℂ) (C : ℝ) (hC : ∀ k, ‖w k‖ ≤ C) :
    Continuous (diagHom w C hC) := by
  have := AddMonoidHomClass.continuous_of_bound ((diagHom w C hC).toAlgHom.toLinearMap) 1 (fun g => by
    rw [one_mul]
    exact diagOp_norm_le _ _ _ ((norm_nonneg _).trans (ContinuousMap.norm_coe_le_norm g ⟨w 0, mem_spectrum_diag w C hC 0⟩)))
  exact this

theorem cfc_diag (w : ℕ → ℝ) (C : ℝ) (hC : ∀ k, ‖((w k : ℝ) : ℂ)‖ ≤ C)
    (f : ℂ → ℂ) (hf : Continuous f) (x : Hilbert ℕ) (k : ℕ) :
    cfc f (diagOp (fun k => (w k : ℂ)) C hC) x k = f (w k) * x k := by
  have hsa : IsSelfAdjoint (diagOp (fun k => (w k : ℂ)) C hC) := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, diagOp_adjoint _ _ _
      (fun k => by rw [norm_star]; exact hC k)]
    exact diagOp_ext _ _ (fun k => by simp)
  rw [cfc_apply f _ hsa.isStarNormal (hf.continuousOn)]
  rw [cfcHom_eq_of_continuous_of_map_id hsa.isStarNormal (diagHom _ C hC) (diagHom_cont _ C hC)
    (by ext y j; simp [diagHom_apply, diagOp_apply])]
  rfl


theorem single_eq_smul [DecidableEq ℕ] (j : ℕ) (c : ℂ) :
    lp.single 2 j c = c • (lp.single 2 j 1 : Hilbert ℕ) := by
  ext k
  rw [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, lp.single_apply]
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem clm_ext_single [DecidableEq ℕ] (A B : Hilbert ℕ →L[ℂ] Hilbert ℕ)
    (h : ∀ j, A (lp.single 2 j 1) = B (lp.single 2 j 1)) : A = B := by
  ext1 x
  have hx := lp.hasSum_single (E := fun _ : ℕ => ℂ) (p := 2) (by norm_num) x
  have hA := hx.mapL A
  have hB := hx.mapL B
  refine hA.unique ?_
  convert hB using 1
  ext1 j
  show A (lp.single 2 j (x j)) = B (lp.single 2 j (x j))
  rw [single_eq_smul, map_smul, map_smul, h]

theorem bo_eq (X : Matrix ℕ ℕ ℂ) (A : Hilbert ℕ →L[ℂ] Hilbert ℕ) (h : operatorCoeff A = X) :
    boundedOperator X = A := by
  have hex : ∃ A : Hilbert ℕ →L[ℂ] Hilbert ℕ, operatorCoeff A = X := ⟨A, h⟩
  unfold boundedOperator
  rw [dif_pos hex]
  apply @clm_ext_single (fun a b => Classical.propDecidable (a = b))
  intro j
  have h1 := hex.choose_spec
  ext k
  have e1 := congrFun (congrFun h1 k) j
  have e2 := congrFun (congrFun h k) j
  unfold operatorCoeff at e1 e2
  exact e1.trans e2.symm

theorem cfc_diag_single [DecidableEq ℕ] (w : ℕ → ℝ) (C : ℝ) (hC : ∀ k, ‖((w k : ℝ) : ℂ)‖ ≤ C)
    (f : ℂ → ℂ) (hf : Continuous f) (k : ℕ) :
    cfc f (diagOp (fun k => (w k : ℂ)) C hC) (lp.single 2 k 1) k = f (w k) := by
  rw [cfc_diag w C hC f hf]; simp

theorem sEB_diag (p : ℕ → ℝ) (C : ℝ) (hC : ∀ k, ‖((p k : ℝ) : ℂ)‖ ≤ C) :
    spectralEntropyBits (fun i j => if i = j then ((p i : ℝ) : ℂ) else 0) =
      (∑' i, ENNReal.ofReal (-p i * Real.log (p i))) / ENNReal.ofReal (Real.log 2) := by
  have hb : boundedOperator (fun i j => if i = j then ((p i : ℝ) : ℂ) else 0) =
      diagOp (fun k => (p k : ℂ)) C hC := by
    apply bo_eq
    ext i j
    unfold operatorCoeff
    have h1 := @diagOp_single (fun a b => Classical.propDecidable (a = b)) (fun k => (p k : ℂ)) C hC j
    have h2 := congrArg (fun f : Hilbert ℕ => f i) h1
    refine h2.trans ?_
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  simp only [spectralEntropyBits, hb]
  congr 1
  congr 1
  ext i
  have hc : Continuous (fun z : ℂ => ((-z.re * Real.log z.re : ℝ) : ℂ)) := by
    have : (fun z : ℂ => ((-z.re * Real.log z.re : ℝ) : ℂ)) =
        fun z => ((-(z.re * Real.log z.re) : ℝ) : ℂ) := by ext; simp [neg_mul]
    rw [this]
    exact Complex.continuous_ofReal.comp ((Real.continuous_mul_log.comp Complex.continuous_re).neg)
  have h1 := @cfc_diag_single (Classical.decEq ℕ) p C hC
    (fun z : ℂ => ((-z.re * Real.log z.re : ℝ) : ℂ)) hc i
  have h2 := congrArg (fun z : ℂ => ENNReal.ofReal z.re) h1
  refine h2.trans ?_
  simp

def Psi (x : ℝ) : ℝ :=
  ((1 + x) ^ 2 * Real.log (1 + x) - (1 - x) ^ 2 * Real.log (1 - x)) / (2 * x) - Real.log (4 * x)

def Psi1 (x : ℝ) : ℝ := -((1 - x ^ 2) * (Real.log (1 + x) - Real.log (1 - x))) / (2 * x ^ 2)

def Psi2 (x : ℝ) : ℝ := (Real.log (1 + x) - Real.log (1 - x) - x) / x ^ 3

theorem hasDerivAt_log1p (x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + x)) x := by
  have h := ((hasDerivAt_id x).const_add 1).log (by simp; linarith)
  simpa using h

theorem hasDerivAt_log1m (x : ℝ) (hx : x < 1) :
    HasDerivAt (fun x => Real.log (1 - x)) (-(1 / (1 - x))) x := by
  have h := ((hasDerivAt_id x).const_sub 1).log (by simp; linarith)
  simp only [id] at h
  convert h using 1; ring

theorem Psi_deriv (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : HasDerivAt Psi (Psi1 x) x := by
  have hA := (((hasDerivAt_id x).const_add 1).pow 2).mul (hasDerivAt_log1p x (by linarith))
  have hB := (((hasDerivAt_id x).const_sub 1).pow 2).mul (hasDerivAt_log1m x h1)
  have hD := (hA.sub hB).div ((hasDerivAt_id x).const_mul 2) (by simp; positivity)
  have hL := ((hasDerivAt_id x).const_mul 4).log (by simp; positivity)
  have := hD.sub hL
  refine HasDerivAt.congr_deriv (f := Psi) this ?_
  · have h1' : (1 - x) ≠ 0 := by linarith
    have h2' : (1 + x) ≠ 0 := by linarith
    unfold Psi1
    simp only [id, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Pi.div_apply]
    field_simp
    ring

theorem Psi1_deriv (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : HasDerivAt Psi1 (Psi2 x) x := by
  have hN := (((hasDerivAt_id x).pow 2).const_sub 1).mul
    ((hasDerivAt_log1p x (by linarith)).sub (hasDerivAt_log1m x h1))
  have hD := hN.neg.div (((hasDerivAt_id x).pow 2).const_mul 2) (by simp; positivity)
  refine HasDerivAt.congr_deriv (f := Psi1) hD ?_
  · have h1' : (1 - x) ≠ 0 := by linarith
    have h2' : (1 + x) ≠ 0 := by linarith
    unfold Psi2
    simp only [id, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Pi.div_apply]
    field_simp
    ring

theorem Psi2_nonneg (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : 0 ≤ Psi2 x := by
  unfold Psi2
  apply div_nonneg _ (by positivity)
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith)
  have := Real.log_nonneg (show (1:ℝ) ≤ 1 + x by linarith)
  linarith

theorem Psi1_nonpos (x : ℝ) (h0 : 0 < x) (h1 : x < 1) : Psi1 x ≤ 0 := by
  unfold Psi1
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith)
  have := Real.log_nonneg (show (1:ℝ) ≤ 1 + x by linarith)
  have : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [neg_nonpos]; apply mul_nonneg this; linarith

theorem Psi_cont : ContinuousOn Psi (Set.Ioc 0 1) := by
  intro x hx
  obtain ⟨h0, h1⟩ := hx
  apply ContinuousAt.continuousWithinAt
  unfold Psi
  have hml : Continuous (fun y : ℝ => (1 - y) ^ 2 * Real.log (1 - y)) := by
    have : (fun y : ℝ => (1 - y) ^ 2 * Real.log (1 - y)) =
        fun y => (1 - y) * ((1 - y) * Real.log (1 - y)) := by ext y; ring
    rw [this]
    exact (continuous_const.sub continuous_id).mul
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))
  apply ContinuousAt.sub
  · apply ContinuousAt.div _ (by fun_prop) (by positivity)
    apply ContinuousAt.sub _ hml.continuousAt
    exact (by fun_prop : Continuous fun y : ℝ => (1 + y) ^ 2).continuousAt.mul
      ((continuous_const.add continuous_id).continuousAt.log (by simp; linarith))
  · exact ((continuous_const.mul continuous_id).continuousAt).log (by simp; positivity)

theorem Psi_convex : ConvexOn ℝ (Set.Ioc 0 1) Psi := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 1) Psi_cont (f' := Psi1) (f'' := Psi2)
  · intro x hx; rw [interior_Ioc] at hx ⊢
    exact (Psi_deriv x hx.1 hx.2).hasDerivWithinAt
  · intro x hx; rw [interior_Ioc] at hx ⊢
    exact (Psi1_deriv x hx.1 hx.2).hasDerivWithinAt
  · intro x hx; rw [interior_Ioc] at hx
    exact Psi2_nonneg x hx.1 hx.2

theorem Psi_anti : AntitoneOn Psi (Set.Ioc 0 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 0 1) Psi_cont (f' := Psi1)
  · intro x hx; rw [interior_Ioc] at hx ⊢
    exact (Psi_deriv x hx.1 hx.2).hasDerivWithinAt
  · intro x hx; rw [interior_Ioc] at hx
    exact Psi1_nonpos x hx.1 hx.2

theorem xlog2x_eq (y : ℝ) : xlog2x y = y * Real.log y / Real.log 2 := by
  unfold xlog2x
  split_ifs with h
  · simp [h]
  · rw [Real.logb]; ring

theorem fc_true (x : ℝ) (h0 : 0 < x) : formationCoefficient true x = (1 + x) ^ 2 / (4 * x) := by
  unfold formationCoefficient
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ x = s ^ 2 :=
    ⟨√x, Real.sqrt_pos.2 h0, (Real.sq_sqrt h0.le).symm⟩
  simp only [if_true]
  rw [Real.sqrt_sq hs.le]; field_simp; try ring

theorem fc_false (x : ℝ) (h0 : 0 < x) : formationCoefficient false x = (1 - x) ^ 2 / (4 * x) := by
  unfold formationCoefficient
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ x = s ^ 2 :=
    ⟨√x, Real.sqrt_pos.2 h0, (Real.sq_sqrt h0.le).symm⟩
  simp only [Bool.false_eq_true, if_false]
  rw [Real.sqrt_sq hs.le]; field_simp; try ring

theorem gfb_eq (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    gaussianFormationBits x = Psi x / Real.log 2 := by
  unfold gaussianFormationBits
  rw [xlog2x_eq, xlog2x_eq, fc_true x h0, fc_false x h0, ← sub_div]
  congr 1
  unfold Psi
  have h4 : (4 * x) ≠ 0 := by positivity
  have hp : Real.log ((1 + x) ^ 2 / (4 * x)) = 2 * Real.log (1 + x) - Real.log (4 * x) := by
    rw [Real.log_div (by positivity) h4, Real.log_pow]; norm_num
  rw [hp]
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; norm_num
    field_simp; ring
  · have hm : Real.log ((1 - x) ^ 2 / (4 * x)) = 2 * Real.log (1 - x) - Real.log (4 * x) := by
      rw [Real.log_div (by have : 0 < 1 - x := by linarith
                           positivity) h4, Real.log_pow]; norm_num
    rw [hm]
    field_simp
    ring

theorem ffp12 : ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) gaussianFormationBits ∧
    AntitoneOn gaussianFormationBits (Set.Ioc (0 : ℝ) 1) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have heq : Set.EqOn (fun x => (1 / Real.log 2) • Psi x) gaussianFormationBits (Set.Ioc 0 1) := by
    intro x hx; simp only [smul_eq_mul]; rw [gfb_eq x hx.1 hx.2]; ring
  constructor
  · exact (Psi_convex.smul (by positivity)).congr heq
  · intro a ha b hb hab
    rw [← heq ha, ← heq hb]
    simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (Psi_anti ha hb hab) (by positivity)


theorem sq_mem (r : ℝ) : Memℓp (squeezedCoefficients r) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2]
  let g : ℕ → (Fin 2 → ℕ) := fun m => ![m, m]
  have hg : Function.Injective g := by
    intro a b h; have := congrFun h 0; simpa [g] using this
  rw [← hg.summable_iff]
  · have ht : Real.tanh r ^ 2 < 1 := by
      have := Real.abs_tanh_lt_one r
      have h0 := abs_nonneg (Real.tanh r)
      rw [← sq_abs]; nlinarith
    have hs := (summable_geometric_of_lt_one (sq_nonneg (Real.tanh r)) ht).div_const
      (Real.cosh r ^ 2)
    refine hs.congr (fun m => ?_)
    simp only [Function.comp_apply, g, squeezedCoefficients, Matrix.cons_val_zero,
      Matrix.cons_val_one, if_true]
    simp only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two, sq_abs, div_pow]
    ring
  · intro x hx
    simp only [squeezedCoefficients]
    split_ifs with h
    · exfalso; apply hx; refine ⟨x 0, ?_⟩
      funext i; fin_cases i <;> simp [g, h]
    · simp

theorem sq_apply (r : ℝ) (i : Fin 2 → ℕ) : squeezedVector r i = squeezedCoefficients r i := by
  unfold squeezedVector; rw [dif_pos (sq_mem r)]

theorem red_sq (r : ℝ) : firstReduction (squeezedVector r) =
    fun m n => if m = n then (((Real.tanh r ^ m / Real.cosh r) ^ 2 : ℝ) : ℂ) else 0 := by
  ext m n
  unfold firstReduction
  simp only [sq_apply, squeezedCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [tsum_eq_single m]
  · by_cases h : m = n
    · subst h
      simp only [if_true]
      rw [show star (((Real.tanh r ^ m / Real.cosh r : ℝ)) : ℂ) =
        ((Real.tanh r ^ m / Real.cosh r : ℝ) : ℂ) from Complex.conj_ofReal _]
      push_cast; ring
    · simp [h, Ne.symm h]
  · intro k hk; simp [Ne.symm hk]

theorem geom_ent (l : ℝ) (h0 : 0 ≤ l) (h1 : l < 1) :
    (∑' m : ℕ, ENNReal.ofReal (-((1 - l) * l ^ m) * Real.log ((1 - l) * l ^ m))) =
      ENNReal.ofReal (-Real.log (1 - l) - l * Real.log l / (1 - l)) := by
  have hl1 : 0 < 1 - l := by linarith
  have key : ∀ m : ℕ, -((1 - l) * l ^ m) * Real.log ((1 - l) * l ^ m) =
      -((1 - l) * Real.log (1 - l)) * l ^ m + (-((1 - l) * Real.log l)) * ((m : ℝ) * l ^ m) := by
    intro m
    by_cases hm : l ^ m = 0
    · rw [hm]; simp
    · rw [Real.log_mul hl1.ne' hm, Real.log_pow]; ring
  have hs1 := (hasSum_geometric_of_lt_one h0 h1).mul_left (-((1 - l) * Real.log (1 - l)))
  have hs2 := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := l)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)).mul_left (-((1 - l) * Real.log l))
  have hs := hs1.add hs2
  have hnn : ∀ m : ℕ, 0 ≤ -((1 - l) * l ^ m) * Real.log ((1 - l) * l ^ m) := by
    intro m
    have hp0 : 0 ≤ (1 - l) * l ^ m := by positivity
    have hp1 : (1 - l) * l ^ m ≤ 1 := by
      have : l ^ m ≤ 1 := pow_le_one₀ h0 h1.le
      nlinarith
    have := Real.log_nonpos hp0 hp1
    nlinarith
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn]
  · congr 1
    rw [show (fun m : ℕ => -((1 - l) * l ^ m) * Real.log ((1 - l) * l ^ m)) = _ from funext key,
      hs.tsum_eq]
    field_simp
    ring
  · exact (show (fun m : ℕ => -((1 - l) * l ^ m) * Real.log ((1 - l) * l ^ m)) = _ from
      funext key) ▸ hs.summable

theorem ent_sq (r : ℝ) : pureEntanglement (squeezedVector r) =
    ENNReal.ofReal (xlog2x (Real.cosh r ^ 2) - xlog2x (Real.sinh r ^ 2)) := by
  unfold pureEntanglement
  rw [red_sq]
  have hc := Real.cosh_pos r
  have hcs := Real.cosh_sq r
  set l := Real.tanh r ^ 2 with hl
  have ht : l < 1 := by
    have := Real.abs_tanh_lt_one r
    have h0 := abs_nonneg (Real.tanh r)
    rw [hl, ← sq_abs]; nlinarith
  have h1l : 1 - l = 1 / Real.cosh r ^ 2 := by
    rw [hl, Real.tanh_eq_sinh_div_cosh]; field_simp; linarith
  have hp : ∀ m : ℕ, (Real.tanh r ^ m / Real.cosh r) ^ 2 = (1 - l) * l ^ m := by
    intro m
    rw [h1l, hl]; ring
  have hC : ∀ k : ℕ, ‖((((Real.tanh r ^ k / Real.cosh r) ^ 2 : ℝ)) : ℂ)‖ ≤ 1 := by
    intro k
    rw [Complex.norm_real, Real.norm_eq_abs, hp k, abs_of_nonneg (by have := sq_nonneg (Real.tanh r); positivity)]
    have : l ^ k ≤ 1 := pow_le_one₀ (sq_nonneg _) ht.le
    have : 0 ≤ l := sq_nonneg _
    nlinarith
  rw [sEB_diag (fun m => (Real.tanh r ^ m / Real.cosh r) ^ 2) 1 hC]
  simp only [hp]
  rw [geom_ent l (sq_nonneg _) ht, ← ENNReal.ofReal_div_of_pos (Real.log_pos (by norm_num)),
    xlog2x_eq, xlog2x_eq, ← sub_div]
  congr 2
  have hll : l = Real.sinh r ^ 2 / Real.cosh r ^ 2 := by
    rw [hl, Real.tanh_eq_sinh_div_cosh, div_pow]
  rw [h1l, hll]
  by_cases hs : Real.sinh r = 0
  · have : Real.cosh r ^ 2 = 1 := by rw [hcs, hs]; ring
    rw [hs, this]; simp
  · rw [Real.log_div (x := Real.sinh r ^ 2) (by positivity) (by positivity),
      Real.log_div (x := 1) (by positivity) (by positivity), Real.log_one]
    field_simp
    rw [hcs]; ring

end g62d_ns

namespace g62d_ns
theorem cosh_sinh_sq_squeezingAt (x : ℝ) (h0 : 0 < x) :
    Real.cosh (squeezingAt x) ^ 2 = formationCoefficient true x ∧
    Real.sinh (squeezingAt x) ^ 2 = formationCoefficient false x := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ x = s ^ 2 :=
    ⟨√x, Real.sqrt_pos.2 h0, (Real.sq_sqrt h0.le).symm⟩
  have hr : squeezingAt (s ^ 2) = -Real.log s := by
    unfold squeezingAt; rw [Real.log_pow]; push_cast; ring
  have e1 : Real.exp (squeezingAt (s ^ 2)) = s⁻¹ := by
    rw [hr, Real.exp_neg, Real.exp_log hs]
  have e2 : Real.exp (-squeezingAt (s ^ 2)) = s := by
    rw [hr, neg_neg, Real.exp_log hs]
  unfold formationCoefficient
  rw [Real.sqrt_sq hs.le, Real.cosh_eq, Real.sinh_eq, e1, e2]
  simp only [if_true, Bool.false_eq_true, if_false]
  constructor <;> (field_simp; ring)
end g62d_ns

end

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF pp.3–4, (17)–(18): convexity and decreasingness only on the specified
interval; identity with actual spectral entropy, including the vacuum endpoint. -/
theorem solution :
    ConvexOn ℝ (Set.Ioc (0 : ℝ) 1) gaussianFormationBits ∧
    AntitoneOn gaussianFormationBits (Set.Ioc (0 : ℝ) 1) ∧
    (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      pureEntanglement (squeezedVector (squeezingAt delta)) =
        ENNReal.ofReal (gaussianFormationBits delta)) := by
  refine ⟨g62d_ns.ffp12.1, g62d_ns.ffp12.2, ?_⟩
  intro delta h0 h1
  rw [g62d_ns.ent_sq, (g62d_ns.cosh_sinh_sq_squeezingAt delta h0).1,
    (g62d_ns.cosh_sinh_sq_squeezingAt delta h0).2]
  rfl


end
