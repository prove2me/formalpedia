-- Prove2me | solution 1 for SYZ.bigTheta_is_constant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T15:58:52.448906+00:00
-- url     : https://prove2.me/submissions/4a3b0d83-8c8e-4b1d-a691-eea53e2555ca

import Mathlib
import Definitions.Def_syz_flat_model

/-! 48a00b13 SYZ.bigTheta_is_constant.  Route: differentiate under the cube integral; the
derivative of `det` is a sum of row replacements by `∂_c θ^{a p}`; expand each in the row and pair
the closed, periodic, period-free form `∂_c θ` against the Piola cofactor field, which is
divergence-free because every other row is closed (symmetric × antisymmetric). -/

set_option autoImplicit false

namespace SYZL

open SYZ MeasureTheory Set Metric Function

lemma dom_expand {k : ℕ} (v : Dom k) : v = ∑ c, v c • basis c := by
  ext i
  simp [basis, Finset.sum_apply, Pi.single_apply]

lemma fderiv_expand {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (h : Dom k → V) (t v : Dom k) : fderiv ℝ h t v = ∑ c, v c • D h c t := by
  conv_lhs => rw [dom_expand v]
  simp [map_sum, map_smul, D]

/-! ## M2. the unit cube: transfer, compactness, volume, divergence-free lemma -/


lemma toLp_preimage_cube (n : ℕ) :
    (WithLp.toLp 2 : (Fin n → ℝ) → Dom n) ⁻¹' cube n = Icc 0 1 := by
  ext y; simp [cube, Set.mem_Icc, Pi.le_def, forall_and]

lemma integral_cube_eq (n : ℕ) (f : Dom n → ℝ) :
    ∫ x in cube n, f x = ∫ y in Icc (0 : Fin n → ℝ) 1, f (WithLp.toLp 2 y) := by
  rw [← toLp_preimage_cube]
  exact ((PiLp.volume_preserving_toLp (Fin n)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f (cube n)).symm

lemma cube_eq_image (n : ℕ) : cube n = (WithLp.toLp 2 : (Fin n → ℝ) → Dom n) '' Icc 0 1 := by
  rw [← toLp_preimage_cube, Set.image_preimage_eq]
  intro x; exact ⟨WithLp.ofLp x, rfl⟩

lemma isCompact_cube (n : ℕ) : IsCompact (cube n) := by
  rw [cube_eq_image]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 _)

lemma measurableSet_cube (n : ℕ) : MeasurableSet (cube n) :=
  (isCompact_cube n).isClosed.measurableSet

lemma volume_cube (n : ℕ) : volume (cube n) = 1 := by
  have := (PiLp.volume_preserving_toLp (Fin n)).measure_preimage
    (measurableSet_cube n).nullMeasurableSet
  rw [toLp_preimage_cube] at this
  rw [← this, Real.volume_Icc_pi]
  simp

lemma insertNth_one_eq {n : ℕ} (k : Fin (n + 1)) (x : Fin n → ℝ) :
    Fin.insertNth (α := fun _ => ℝ) k 1 x = Fin.insertNth (α := fun _ => ℝ) k 0 x + Pi.single k 1 := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨j, rfl⟩
  · simp
  · simp [Pi.single_apply, Fin.succAbove_ne]

/-- The integral of a partial derivative of a periodic `C¹` function over the unit cube is 0. -/
theorem integral_cube_D_eq_zero {n : ℕ} (W : Dom n → ℝ) (hW : ContDiff ℝ 1 W)
    (hper : ∀ a x, W (x + basis a) = W x) (k : Fin n) :
    ∫ x in cube n, D W k x = 0 := by
  cases n with
  | zero => exact k.elim0
  | succ n =>
  set e := EuclideanSpace.equiv (Fin (n + 1)) ℝ
  set W' : (Fin (n + 1) → ℝ) → ℝ := fun y => W (WithLp.toLp 2 y) with hW'
  have hW'd : ContDiff ℝ 1 W' := hW.comp (e.symm.contDiff)
  have hder : ∀ y, D W k (WithLp.toLp 2 y) = fderiv ℝ W' y (Pi.single k 1) := by
    intro y
    have h1 : HasFDerivAt W' ((fderiv ℝ W (WithLp.toLp 2 y)).comp (e.symm : _ →L[ℝ] _)) y :=
      ((hW.differentiable (by norm_num)) _).hasFDerivAt.comp y e.symm.hasFDerivAt
    rw [h1.fderiv]; rfl
  rw [integral_cube_eq]
  simp_rw [hder]
  have hsum : ∀ y, (∑ i, (if i = k then fderiv ℝ W' y else 0) (Pi.single i 1)) =
      fderiv ℝ W' y (Pi.single k 1) := by
    intro y
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' (0 : Fin (n + 1) → ℝ) 1
    zero_le_one (fun i => if i = k then W' else 0)
    (fun i y => if i = k then fderiv ℝ W' y else 0) ∅ countable_empty
    (fun i => by split_ifs <;> [exact hW'd.continuous.continuousOn; exact continuousOn_const])
    (fun y _ i => by
      split_ifs
      · exact ((hW'd.differentiable (by norm_num)) y).hasFDerivAt
      · exact hasFDerivAt_const _ _)
    (by
      simp_rw [hsum]
      exact ((hW'd.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn
        |>.integrableOn_compact isCompact_Icc)
  simp_rw [hsum] at hdiv
  rw [hdiv]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hik : i = k
  · subst hik
    simp only [if_true, Pi.one_apply, Pi.zero_apply]
    rw [sub_eq_zero]
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    simp only [hW', insertNth_one_eq, WithLp.toLp_add]
    exact hper i _
  · simp [hik]


/-! ## M3. differentiation under the integral; M4. κ as a multilinear map -/


instance (n : ℕ) : IsFiniteMeasure (volume.restrict (cube n)) :=
  isFiniteMeasure_restrict.2 (isCompact_cube n).measure_lt_top.ne

/-- differentiation under the integral over the cube, jointly `C¹` integrand -/
theorem hasFDerivAt_integral_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {n : ℕ} (G : E → Dom n → ℝ)
    (hG : ContDiff ℝ 1 (fun p : E × Dom n => G p.1 p.2)) (t : E) :
    HasFDerivAt (fun s => ∫ x in cube n, G s x)
      (∫ x in cube n, fderiv ℝ (fun s => G s x) t) t := by
  have hF'c : Continuous (fun p : E × Dom n => fderiv ℝ (fun s => G s p.2) p.1) := by
    have h1 : ContDiff ℝ 1 (Function.uncurry fun (p : E × Dom n) (s : E) => G s p.2) :=
      hG.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
    exact (ContDiff.fderiv (n := 0) h1 contDiff_fst (by norm_num)).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_cube n)).exists_bound_of_continuousOn
    hF'c.continuousOn
  have hGc : ∀ s, Continuous (G s) := fun s =>
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict (cube n))
    (bound := fun _ => C) (ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => (hGc s).aestronglyMeasurable)
    ((hGc t).continuousOn.integrableOn_compact (isCompact_cube n))
    (hF'c.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_cube n)).2 (Filter.Eventually.of_forall fun x hx s hs =>
      hC (s, x) ⟨ball_subset_closedBall hs, hx⟩))
    (integrable_const C)
    (Filter.Eventually.of_forall fun x s _ => ?_)
  have : ContDiff ℝ 1 (fun s => G s x) := hG.comp (contDiff_id.prodMk contDiff_const)
  exact ((this.differentiable (by norm_num)) s).hasFDerivAt

theorem D_integral_cube {m n : ℕ} (G : Dom m → Dom n → ℝ)
    (hG : ContDiff ℝ 1 (fun p : Dom m × Dom n => G p.1 p.2)) (c : Fin m) (t : Dom m) :
    D (fun s => ∫ x in cube n, G s x) c t = ∫ x in cube n, D (fun s => G s x) c t := by
  have hF'c : Continuous (fun x : Dom n => fderiv ℝ (fun s => G s x) t) := by
    have h1 : ContDiff ℝ 1 (Function.uncurry fun (x : Dom n) (s : Dom m) => G s x) :=
      hG.comp (contDiff_snd.prodMk contDiff_fst)
    exact (ContDiff.fderiv (n := 0) h1 (contDiff_const (c := t)) (by norm_num)).continuous
  unfold D
  rw [(hasFDerivAt_integral_cube G hG t).fderiv,
    ContinuousLinearMap.integral_apply (hF'c.continuousOn.integrableOn_compact (isCompact_cube n))]

lemma sum_sum_antisymm {n : ℕ} (g : Fin n → Fin n → ℝ) (h : ∀ j k, g j k = -g k j) :
    ∑ j, ∑ k, g j k = 0 := by
  have h1 : ∑ j, ∑ k, g j k = -∑ j, ∑ k, g j k :=
    calc ∑ j, ∑ k, g j k = ∑ k, ∑ j, g j k := Finset.sum_comm
      _ = ∑ k, ∑ j, -g k j := Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => h j k
      _ = -∑ j, ∑ k, g j k := by simp only [Finset.sum_neg_distrib]
  linarith


/-! ## M8. the cohomology pairing on the torus (translation trick) -/

lemma intOn_cube {n : ℕ} {f : Dom n → ℝ} (hf : Continuous f) : IntegrableOn f (cube n) :=
  hf.continuousOn.integrableOn_compact (isCompact_cube n)

/-- a parametric cube integral whose parameter-derivatives integrate to zero is constant -/
lemma const_of_D_integral {n : ℕ} (G : Dom n → Dom n → ℝ)
    (hG : ContDiff ℝ 1 (fun p : Dom n × Dom n => G p.1 p.2))
    (h : ∀ x c, ∫ y in cube n, D (fun s => G s y) c x = 0) (x x' : Dom n) :
    ∫ y in cube n, G x y = ∫ y in cube n, G x' y := by
  refine is_const_of_fderiv_eq_zero (f := fun x => ∫ y in cube n, G x y)
    (fun x => (hasFDerivAt_integral_cube G hG x).differentiableAt) (fun x => ?_) x x'
  ext1 v
  rw [fderiv_expand]
  simp [D_integral_cube G hG, h]

lemma D_comp_add_left {n : ℕ} (g : Dom n → ℝ) (x : Dom n) (c : Fin n) (y : Dom n) :
    D (fun s => g (x + s)) c y = D g c (x + y) := by
  unfold D; rw [fderiv_comp_add_left]

lemma D_comp_add_right {n : ℕ} (g : Dom n → ℝ) (y : Dom n) (c : Fin n) (x : Dom n) :
    D (fun s => g (s + y)) c x = D g c (x + y) := by
  unfold D; rw [fderiv_comp_add_right]

/-- translation invariance of the torus integral of a periodic function -/
theorem transl_inv {n : ℕ} (g : Dom n → ℝ) (hg : ContDiff ℝ 1 g)
    (hper : ∀ a x, g (x + basis a) = g x) (x : Dom n) :
    ∫ y in cube n, g (x + y) = ∫ y in cube n, g y := by
  have hG : ContDiff ℝ 1 (fun p : Dom n × Dom n => g (p.1 + p.2)) :=
    hg.comp (contDiff_fst.add contDiff_snd)
  have := const_of_D_integral (fun x y => g (x + y)) hG (fun x c => by
    simp only [D_comp_add_right]
    have := integral_cube_D_eq_zero (fun y => g (x + y)) (hg.comp (contDiff_const.add contDiff_id))
      (fun a y => by simp only [← add_assoc, hper]) c
    simpa [D_comp_add_left] using this) x 0
  simpa using this

/-- **Cohomology pairing.** For a closed periodic 1-form `θ` and a periodic divergence-free field
`J`, `∫ θ·J = Σᵢ (∫ θᵢ)(∫ Jᵢ)`. -/
theorem pairing {n : ℕ} (θ J : Dom n → Fin n → ℝ)
    (hθ : ∀ i, ContDiff ℝ 1 (fun x => θ x i)) (hJ : ∀ i, ContDiff ℝ 1 (fun x => J x i))
    (hθp : ∀ a x i, θ (x + basis a) i = θ x i) (hJp : ∀ a x i, J (x + basis a) i = J x i)
    (hcl : IsClosed1Form θ) (hdiv : ∀ x, ∑ i, D (fun y => J y i) i x = 0) :
    ∫ x in cube n, ∑ i, θ x i * J x i =
      ∑ i, (∫ x in cube n, θ x i) * (∫ x in cube n, J x i) := by
  set Ψ : Dom n → Dom n → ℝ := fun y x => ∑ i, θ (x + y) i * J x i with hΨ
  have hΨc : ContDiff ℝ 1 (fun p : Dom n × Dom n => Ψ p.1 p.2) :=
    ContDiff.sum fun i _ => ((hθ i).comp (contDiff_snd.add contDiff_fst)).mul
      ((hJ i).comp contDiff_snd)
  have hθd : ∀ i, Differentiable ℝ (fun x => θ x i) := fun i => (hθ i).differentiable (by norm_num)
  have hJd : ∀ i, Differentiable ℝ (fun x => J x i) := fun i => (hJ i).differentiable (by norm_num)
  have hWc : ∀ y c i, ContDiff ℝ 1 (fun z => θ (z + y) c * J z i) := fun y c i =>
    ((hθ c).comp (contDiff_id.add contDiff_const)).mul (hJ i)
  -- Step A: the parameter derivative integrates to zero
  have hA : ∀ y c, ∫ x in cube n, D (fun s => Ψ s x) c y = 0 := by
    intro y c
    have h1 : ∀ x, D (fun s => Ψ s x) c y = ∑ i, D (fun z => θ z i) c (x + y) * J x i := by
      intro x
      have hdθx : ∀ i, Differentiable ℝ (fun s => θ (x + s) i) := fun i =>
        (hθd i).comp ((differentiable_const x).add differentiable_id)
      unfold D
      simp only [hΨ]
      rw [fderiv_fun_sum (A := fun i s => θ (x + s) i * J x i)
        (fun i _ => ((hdθx i).mul_const (J x i)) y)]
      simp only [FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fderiv_mul_const ((hdθx i) y)]
      simp only [smul_apply, smul_eq_mul]
      have := D_comp_add_left (fun z => θ z i) x c y
      unfold D at this
      rw [this, mul_comm]
    have hprod : ∀ x i, D (fun z => θ (z + y) c * J z i) i x =
        D (fun z => θ z c) i (x + y) * J x i + θ (x + y) c * D (fun z => J z i) i x := by
      intro x i
      have hdθy : Differentiable ℝ (fun z => θ (z + y) c) :=
        (hθd c).comp (differentiable_id.add_const y)
      unfold D
      rw [fderiv_fun_mul (hdθy x) ((hJd i) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      have := D_comp_add_right (fun z => θ z c) y i x
      unfold D at this
      rw [this]; ring
    have hpt : ∀ x, D (fun s => Ψ s x) c y = ∑ i, D (fun z => θ (z + y) c * J z i) i x := by
      intro x
      rw [h1 x]
      simp only [hprod x, Finset.sum_add_distrib, ← Finset.mul_sum, hdiv x, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcl c i (x + y)]
    simp only [hpt]
    rw [integral_finsetSum (f := fun i x => D (fun z => θ (z + y) c * J z i) i x) _
      (fun i _ => intOn_cube
        (((hWc y c i).continuous_fderiv (by norm_num)).clm_apply continuous_const))]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine integral_cube_D_eq_zero _ (hWc y c i) (fun a z => ?_) i
    simp only [add_right_comm z (basis a) y, hθp, hJp]
  -- Step B: Ψ y integrates to the same value for every y
  have hB : ∀ y, ∫ x in cube n, Ψ y x = ∫ x in cube n, Ψ 0 x := fun y =>
    const_of_D_integral Ψ hΨc hA y 0
  have hΨcont : Continuous (fun p : Dom n × Dom n => Ψ p.1 p.2) := hΨc.continuous
  -- Step C: Fubini
  have hint : Integrable (Function.uncurry Ψ)
      ((volume.restrict (cube n)).prod (volume.restrict (cube n))) := by
    rw [Measure.prod_restrict]
    exact hΨcont.continuousOn.integrableOn_compact ((isCompact_cube n).prod (isCompact_cube n))
  have hfub := integral_integral_swap hint
  have hL : ∫ y in cube n, ∫ x in cube n, Ψ y x = ∫ x in cube n, Ψ 0 x := by
    simp only [hB, setIntegral_const, measureReal_def, volume_cube]
    simp
  have hR : ∫ x in cube n, ∫ y in cube n, Ψ y x =
      ∑ i, (∫ x in cube n, θ x i) * (∫ x in cube n, J x i) := by
    have hin : ∀ x, ∫ y in cube n, Ψ y x = ∑ i, (∫ z in cube n, θ z i) * J x i := by
      intro x
      simp only [hΨ]
      rw [integral_finsetSum (f := fun i y => θ (x + y) i * J x i) _ (fun i _ => intOn_cube
        ((((hθ i).continuous.comp (continuous_const.add continuous_id))).mul continuous_const))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      congr 1
      have := transl_inv (fun z => θ z i) (hθ i) (fun a z => hθp a z i) x
      simpa [add_comm] using this
    simp only [hin]
    rw [integral_finsetSum (f := fun i x => (∫ z in cube n, θ z i) * J x i) _
      (fun i _ => intOn_cube (continuous_const.mul (hJ i).continuous))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  rw [← hR, ← hfub, hL]
  simp [hΨ]


section Glue

variable {n m : ℕ}

/-- `x`-direction `j` and `t`-direction `a` in `Dom m × Dom n` -/
noncomputable def vX (m : ℕ) {n : ℕ} (j : Fin n) : Dom m × Dom n := (0, basis j)
noncomputable def vT {m : ℕ} (n : ℕ) (a : Fin m) : Dom m × Dom n := (basis a, 0)

lemma D_right {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : Dom m × Dom n → V)
    (t : Dom m) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (j : Fin n) :
    D (fun y => h (t, y)) j x = fderiv ℝ h (t, x) (vX m j) := by
  have H : HasFDerivAt (fun y => h (t, y))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inr ℝ (Dom m) (Dom n))) x :=
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  unfold D
  rw [H.fderiv]
  rfl

lemma D_left {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : Dom m × Dom n → V)
    (t : Dom m) (x : Dom n) (hd : DifferentiableAt ℝ h (t, x)) (a : Fin m) :
    D (fun s => h (s, x)) a t = fderiv ℝ h (t, x) (vT n a) := by
  have H : HasFDerivAt (fun s => h (s, x))
      ((fderiv ℝ h (t, x)).comp (ContinuousLinearMap.inl ℝ (Dom m) (Dom n))) t :=
    hd.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x)
  unfold D
  rw [H.fderiv]
  rfl

/-- the family as a map on `Dom m × Dom n` -/
noncomputable def Phi (S : SYZFamily n m) : Dom m × Dom n → Amb n := fun p => S.F p.1 p.2

lemma Phi_smooth (S : SYZFamily n m) (k : ℕ) : ContDiff ℝ k (Phi S) :=
  S.smooth.of_le (by exact_mod_cast le_top)

lemma Phi_diff (S : SYZFamily n m) : Differentiable ℝ (Phi S) :=
  (Phi_smooth S 1).differentiable (by norm_num)

lemma cols_smooth (S : SYZFamily n m) (k : ℕ) (u : Dom m × Dom n) :
    ContDiff ℝ k (fun p => fderiv ℝ (Phi S) p u) :=
  ((Phi_smooth S (k + 1)).fderiv_right (m := k) (by norm_cast)).clm_apply contDiff_const

lemma DF_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) (j : Fin n) :
    D (S.F t) j x = fderiv ℝ (Phi S) (t, x) (vX m j) :=
  D_right (Phi S) t x (Phi_diff S _) j

lemma DFt_eq (S : SYZFamily n m) (t : Dom m) (x : Dom n) (a : Fin m) :
    D (fun s => S.F s x) a t = fderiv ℝ (Phi S) (t, x) (vT n a) :=
  D_left (Phi S) t x (Phi_diff S _) a

lemma thetaM_eq (S : SYZFamily n m) (a : Fin m) (t : Dom m) (x : Dom n) (i : Fin n) :
    thetaM S.F a t x i =
      kForm (fderiv ℝ (Phi S) (t, x) (vT n a)) (fderiv ℝ (Phi S) (t, x) (vX m i)) := by
  unfold thetaM; rw [DF_eq, DFt_eq]

lemma kForm_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (k : ℕ)
    (f g : P → Amb n) (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (fun p => kForm (f p) (g p)) :=
  Complex.imCLM.contDiff.comp (hf.inner ℂ hg)

lemma theta_smooth (S : SYZFamily n m) (k : ℕ) (a : Fin m) (i : Fin n) :
    ContDiff ℝ k (fun p : Dom m × Dom n => thetaM S.F a p.1 p.2 i) := by
  simp only [thetaM_eq]
  exact kForm_smooth k _ _ (cols_smooth S k _) (cols_smooth S k _)

/-- directional derivative of a directional derivative -/
lemma fderiv_fderiv_apply {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (h : P → ℝ) (hh : ContDiff ℝ 2 h) (p v w : P) :
    fderiv ℝ (fun q => fderiv ℝ h q w) p v = fderiv ℝ (fderiv ℝ h) p v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ h) p :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) p
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- the variation `∂_a θ^b` as a function of `x` -/
noncomputable def varT (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i : Fin n) (y : Dom n) : ℝ :=
  D (fun s => thetaM S.F b s y i) a t

lemma varT_eq (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i : Fin n) (y : Dom n) :
    varT S a b t i y =
      fderiv ℝ (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i) (t, y) (vT n a) :=
  D_left (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i) t y
    (((theta_smooth S 1 b i).differentiable (by norm_num)) _) a

lemma varT_smooth (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i : Fin n) :
    ContDiff ℝ 1 (varT S a b t i) := by
  have h2 := theta_smooth S 2 b i
  have h1 : ContDiff ℝ 1 (fun p : Dom m × Dom n =>
      fderiv ℝ (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i) p (vT n a)) :=
    (h2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have : varT S a b t i = fun y => fderiv ℝ (fun p : Dom m × Dom n => thetaM S.F b p.1 p.2 i)
      (t, y) (vT n a) := funext fun y => varT_eq S a b t i y
  rw [this]
  exact h1.comp ((contDiff_const (c := t)).prodMk contDiff_id)

/-- `∂_a θ^b` is closed in `x` -/
theorem varT_closed (S : SYZFamily n m) (a b : Fin m) (t : Dom m) (i j : Fin n) (x : Dom n) :
    D (varT S a b t i) j x = D (varT S a b t j) i x := by
  set Θ : Fin n → Dom m × Dom n → ℝ := fun k p => thetaM S.F b p.1 p.2 k with hΘ
  have hs : ∀ k, ContDiff ℝ 2 (Θ k) := fun k => theta_smooth S 2 b k
  -- closedness in `x` of `θ^b`, as an identity of functions of `p`
  have hcl : ∀ k l, (fun p => fderiv ℝ (Θ k) p (vX m l)) = fun p => fderiv ℝ (Θ l) p (vX m k) := by
    intro k l
    funext p
    have e1 := D_right (Θ k) p.1 p.2 (((hs k).differentiable (by norm_num)) _) l
    have e2 := D_right (Θ l) p.1 p.2 (((hs l).differentiable (by norm_num)) _) k
    have hh := (S.harmonic p.1 b).1 l k p.2
    simp only [hΘ] at e1 e2
    rw [← e1, ← e2]
    exact hh
  have key : ∀ k l, D (varT S a b t k) l x =
      fderiv ℝ (fun p => fderiv ℝ (Θ k) p (vX m l)) (t, x) (vT n a) := by
    intro k l
    have hfun : varT S a b t k = fun y => fderiv ℝ (Θ k) (t, y) (vT n a) :=
      funext fun y => varT_eq S a b t k y
    have hg : ContDiff ℝ 1 (fun p => fderiv ℝ (Θ k) p (vT n a)) :=
      ((hs k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    rw [hfun, D_right (fun p => fderiv ℝ (Θ k) p (vT n a)) t x
      ((hg.differentiable (by norm_num)) _) l]
    rw [fderiv_fderiv_apply _ (hs k), fderiv_fderiv_apply _ (hs k)]
    exact (hs k).contDiffAt.isSymmSndFDerivAt (by simp) _ _
  rw [key, key, hcl]

/-- the `k`-th coordinate functional on `Dom n` -/
noncomputable def pr (k : Fin n) : Dom n →L[ℝ] ℝ := EuclideanSpace.proj k

@[simp] lemma pr_apply (k : Fin n) (w : Dom n) : pr k w = w k := rfl


/-- the derivative of the family is periodic in `x` -/
lemma fderiv_Phi_periodic (S : SYZFamily n m) (t : Dom m) (x : Dom n) (a : Fin n) :
    fderiv ℝ (Phi S) (t, x + basis a) = fderiv ℝ (Phi S) (t, x) := by
  have h1 : (fun q : Dom m × Dom n => Phi S (q + (0, basis a))) = fun q => Phi S q + S.lam a := by
    funext q; simp only [Phi, Prod.fst_add, Prod.snd_add, add_zero]; exact S.periodic q.1 a q.2
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := Phi S) (x := (t, x)) ((0 : Dom m), basis a)
  rw [h1, fderiv_add_const] at h2
  have h3 : (t, x) + ((0 : Dom m), basis a) = (t, x + basis a) := by simp
  rw [h3] at h2
  exact h2.symm


end Glue

section Det

variable {n m : ℕ}

/-- the determinant as a continuous multilinear map in the rows -/
noncomputable def detML (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ where
  toMultilinearMap := (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap
  cont := by
    show Continuous fun v : Matrix (Fin n) (Fin n) ℝ => Matrix.det v
    exact continuous_id.matrix_det

lemma detML_apply (v : Fin n → Fin n → ℝ) : detML n v = Matrix.det (Matrix.of v) := rfl

lemma detML_swap2 (v : Fin n → Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) (x y : Fin n → ℝ) :
    detML n (update (update v i x) j y) = -detML n (update (update v i y) j x) := by
  have hperm : ∀ u : Fin n → Fin n → ℝ, detML n (u ∘ Equiv.swap i j) = -detML n u := fun u =>
    (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).map_swap u hij
  rw [← hperm]
  congr 1
  ext1 k
  simp only [Function.comp_apply]
  by_cases hki : k = i
  · subst hki; simp [Equiv.swap_apply_left, hij]
  · by_cases hkj : k = j
    · subst hkj; simp [Equiv.swap_apply_right, hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

lemma detML_expand (v : Fin n → Fin n → ℝ) (k : Fin n) (w : Fin n → ℝ) :
    detML n (update v k w) = ∑ r, w r * detML n (update v k (Pi.single r 1)) := by
  have hw : w = ∑ r, w r • (Pi.single r (1 : ℝ) : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  calc detML n (update v k w) = (detML n).toMultilinearMap.toLinearMap v k w := rfl
    _ = (detML n).toMultilinearMap.toLinearMap v k
          (∑ r, w r • (Pi.single r (1 : ℝ) : Fin n → ℝ)) := by rw [← hw]
    _ = ∑ r, w r * detML n (update v k (Pi.single r 1)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      rfl

/-- derivative of `det` of a row-valued map -/
lemma D_detML {k : ℕ} (R : Dom k → Fin n → Fin n → ℝ) (x : Dom k)
    (hR : ∀ r q, DifferentiableAt ℝ (fun y => R y r q) x) (c : Fin k) :
    D (fun y => detML n (R y)) c x =
      ∑ r, detML n (update (R x) r (fun q => D (fun y => R y r q) c x)) := by
  have hrow : ∀ r, HasFDerivAt (fun y => R y r)
      (ContinuousLinearMap.pi fun q => fderiv ℝ (fun y => R y r q) x) x := by
    intro r
    refine hasFDerivAt_pi.2 fun q => ?_
    simpa using (hR r q).hasFDerivAt
  have hRd : HasFDerivAt R (ContinuousLinearMap.pi fun r =>
      ContinuousLinearMap.pi fun q => fderiv ℝ (fun y => R y r q) x) x := by
    refine hasFDerivAt_pi.2 fun r => ?_
    simpa using hrow r
  have H : HasFDerivAt (fun y => detML n (R y)) _ x := ((detML n).hasFDerivAt (R x)).comp x hRd
  unfold D
  rw [H.fderiv]
  simp [ContinuousMultilinearMap.linearDeriv_apply]

/-- the rows `θ^{a p}` of the Θ matrix -/
noncomputable def rowsT (S : SYZFamily n m) (a : Fin n → Fin m) (p : Dom m × Dom n) :
    Fin n → Fin n → ℝ := fun k q => thetaM S.F (a k) p.1 p.2 q

lemma rowsT_smooth (S : SYZFamily n m) (a : Fin n → Fin m) (k : ℕ) :
    ContDiff ℝ k (rowsT S a) := by
  unfold rowsT
  exact contDiff_pi.2 fun r => contDiff_pi.2 fun q => theta_smooth S k (a r) q

lemma theta_s_diff (S : SYZFamily n m) (b : Fin m) (x : Dom n) (i : Fin n) :
    Differentiable ℝ (fun s => thetaM S.F b s x i) :=
  ((theta_smooth S 1 b i).comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable
    (by norm_num)

lemma theta_per (S : SYZFamily n m) (b : Fin m) (s : Dom m) (x : Dom n) (j i : Fin n) :
    thetaM S.F b s (x + basis j) i = thetaM S.F b s x i := by
  rw [thetaM_eq, thetaM_eq, fderiv_Phi_periodic]

lemma rowsT_per (S : SYZFamily n m) (a : Fin n → Fin m) (t : Dom m) (x : Dom n) (j : Fin n) :
    rowsT S a (t, x + basis j) = rowsT S a (t, x) := by
  funext k q; exact theta_per S (a k) t x j q

/-- the Piola cofactor field of row `p` -/
noncomputable def Jf (S : SYZFamily n m) (a : Fin n → Fin m) (t : Dom m) (p q : Fin n)
    (y : Dom n) : ℝ := detML n (update (rowsT S a (t, y)) p (Pi.single q 1))

lemma updrow_smooth (S : SYZFamily n m) (a : Fin n → Fin m) (t : Dom m) (p : Fin n)
    (e : Fin n → ℝ) : ContDiff ℝ 1 (fun y => update (rowsT S a (t, y)) p e) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = p
  · subst hk; simp only [update_self]; exact contDiff_const
  · simp only [update_of_ne hk]
    exact (rowsT_smooth S a 1).comp ((contDiff_const (c := t)).prodMk contDiff_id)
      |> fun h => contDiff_pi.1 h k

lemma Jf_smooth (S : SYZFamily n m) (a : Fin n → Fin m) (t : Dom m) (p q : Fin n) :
    ContDiff ℝ 1 (Jf S a t p q) :=
  (detML n).contDiff.comp (updrow_smooth S a t p _)

/-- **Piola identity**: the cofactor field is divergence free -/
theorem piola (S : SYZFamily n m) (a : Fin n → Fin m) (t : Dom m) (p : Fin n) (x : Dom n) :
    ∑ q, D (fun y => Jf S a t p q y) q x = 0 := by
  set R := rowsT S a (t, x) with hRdef
  set dθ : Fin n → Fin n → Fin n → ℝ := fun k q r => D (fun y => thetaM S.F (a k) t y r) q x
    with hdθ
  have step : ∀ q, D (fun y => Jf S a t p q y) q x = ∑ k, if k = p then 0 else
      ∑ r, dθ k q r * detML n (update (update R p (Pi.single q 1)) k (Pi.single r 1)) := by
    intro q
    unfold Jf
    rw [D_detML (fun y => update (rowsT S a (t, y)) p (Pi.single q 1)) x ?_ q]
    · refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k = p
      · subst hk
        simp only [if_true]
        have : (fun r => D (fun y => update (rowsT S a (t, y)) k
            (Pi.single q (1 : ℝ)) k r) q x) = 0 := by
          funext r; simp [D]
        rw [this]
        exact (detML n).map_coord_zero k (by simp)
      · rw [if_neg hk]
        have : (fun r => D (fun y => update (rowsT S a (t, y)) p
            (Pi.single q (1 : ℝ)) k r) q x) = dθ k q := by
          funext r; simp [update_of_ne hk, rowsT, hdθ]
        rw [this, detML_expand]
    · intro k r
      by_cases hk : k = p
      · subst hk; simp
      · simp only [update_of_ne hk]
        have h := (rowsT_smooth S a 1).comp ((contDiff_const (c := t)).prodMk contDiff_id)
        exact ((contDiff_pi.1 (contDiff_pi.1 h k) r).differentiable (by norm_num)) x
  simp only [step]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = p
  · simp [hk]
  · simp only [if_neg hk]
    refine sum_sum_antisymm _ fun q r => ?_
    have hsym : dθ k q r = dθ k r q := (S.harmonic t (a k)).1 q r x
    rw [hsym, detML_swap2 R (Ne.symm hk)]
    ring

/-- the `t`-derivative of the integrand -/
lemma D_integrand (S : SYZFamily n m) (a : Fin n → Fin m) (c : Fin m) (t : Dom m) (x : Dom n) :
    D (fun s => detML n (rowsT S a (s, x))) c t =
      ∑ p, ∑ q, varT S c (a p) t q x * Jf S a t p q x := by
  rw [D_detML (fun s => rowsT S a (s, x)) t (fun r q => theta_s_diff S (a r) x q t) c]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [detML_expand]
  rfl

theorem main (S : SYZFamily n m) (a : Fin n → Fin m) (c : Fin m) (t : Dom m) :
    D (fun s => bigTheta S.F a s) c t = 0 := by
  have hG : ContDiff ℝ 1 (fun p : Dom m × Dom n => detML n (rowsT S a (p.1, p.2))) :=
    (detML n).contDiff.comp (rowsT_smooth S a 1)
  have e1 : (fun s => bigTheta S.F a s) = fun s => ∫ x in cube n, detML n (rowsT S a (s, x)) := rfl
  rw [e1, D_integral_cube (fun s x => detML n (rowsT S a (s, x))) hG c t]
  simp only [D_integrand]
  rw [integral_finsetSum (f := fun p x => ∑ q, varT S c (a p) t q x * Jf S a t p q x) _
    (fun p _ => intOn_cube (continuous_finsetSum _ fun q _ =>
    (varT_smooth S c (a p) t q).continuous.mul (Jf_smooth S a t p q).continuous))]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hpair := pairing (fun x q => varT S c (a p) t q x) (fun x q => Jf S a t p q x)
    (fun q => varT_smooth S c (a p) t q) (fun q => Jf_smooth S a t p q)
    (fun j x q => by
      show varT S c (a p) t q (x + basis j) = varT S c (a p) t q x
      unfold varT
      simp only [theta_per])
    (fun j x q => by
      show Jf S a t p q (x + basis j) = Jf S a t p q x
      unfold Jf; rw [rowsT_per])
    (fun i j x => (varT_closed S c (a p) t j i x))
    (fun x => piola S a t p x)
  rw [hpair]
  refine Finset.sum_eq_zero fun q _ => ?_
  have hθ0 : ∫ x in cube n, varT S c (a p) t q x = 0 := by
    have := D_integral_cube (fun s x => thetaM S.F (a p) s x q) (theta_smooth S 1 (a p) q) c t
    rw [← S.periodConst (a p) q c t]
    exact this.symm
  simp [hθ0]

end Det

end SYZL

open SYZ in
theorem solution {n m : ℕ} (S : SYZFamily n m)
    (a : Fin n → Fin m) (c : Fin m) (t : Dom m) :
    D (fun s => bigTheta S.F a s) c t = 0 := by
  exact SYZL.main S a c t
