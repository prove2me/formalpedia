-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P24.haarTwirl_preservesOptimum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T22:43:22.971405+00:00
-- url     : https://prove2.me/submissions/8f60926e-0d22-4bdd-bee1-551ec498444d

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P24
noncomputable section

open MeasureTheory TopologicalSpace

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Next46.P24

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.combContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.pairContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P24.wireContinuousENorm


instance g64_scM (d : ℕ) : SecondCountableTopology (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))
instance g64_sc (d : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology (Matrix.specialUnitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ))
example (d : ℕ) : OpensMeasurableSpace (Matrix.specialUnitaryGroup (Fin d) ℂ × Matrix.specialUnitaryGroup (Fin d) ℂ) := by
  infer_instance
example (d : ℕ) : MeasurableMul (Matrix.specialUnitaryGroup (Fin d) ℂ × Matrix.specialUnitaryGroup (Fin d) ℂ) := by
  infer_instance
abbrev g64G (d : ℕ) := Matrix.specialUnitaryGroup (Fin d) ℂ

instance g64_prob (d : ℕ) : IsProbabilityMeasure (haar d) := ⟨Measure.haarMeasure_self⟩
instance g64_haar (d : ℕ) : (haar d).IsHaarMeasure := by unfold haar; infer_instance

theorem g64_int_comb {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (m : Measure α) [IsFiniteMeasure m] {d : ℕ} (F : α → CombMatrix d)
    (hF : ∀ x y, Continuous (fun a => F a x y)) : Integrable F m := by
  have hc : Continuous F := continuous_pi (fun x => continuous_pi (fun y => hF x y))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem g64_ent_comb {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (m : Measure α) [IsFiniteMeasure m] {d : ℕ} (F : α → CombMatrix d)
    (hF : ∀ x y, Continuous (fun a => F a x y)) (x y : InversionWires d) :
    (∫ a, F a ∂m) x y = ∫ a, F a x y ∂m := by
  have h1 : ∀ x, Integrable (fun a => F a x) m := fun x =>
    (continuous_pi (fun y => hF x y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : ∀ y, Integrable (fun a => F a x y) m := fun y =>
    (hF x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (congrFun (eval_integral h1 x) y).trans (eval_integral h2 y)

open scoped Kronecker

theorem g64_coe_cont {d : ℕ} (i j : Fin d) : Continuous (fun U : g64G d => U.val i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem g64_cov_kron {d : ℕ} (U W : g64G d) :
    covarianceMatrix U W = U.val ⊗ₖ (W.val ⊗ₖ (U.val ⊗ₖ W.val)) := by
  ext x y
  simp only [covarianceMatrix, Matrix.kronecker, Matrix.kroneckerMap_apply]
  ring

theorem g64_cov_mul {d : ℕ} (U W U' W' : g64G d) :
    covarianceMatrix (U * U') (W * W') = covarianceMatrix U W * covarianceMatrix U' W' := by
  simp only [g64_cov_kron, Submonoid.coe_mul, Matrix.mul_kronecker_mul]

theorem g64_unit {d : ℕ} (U : g64G d) : U.val * U.valᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp U.2.1

theorem g64_unit' {d : ℕ} (U : g64G d) : U.valᴴ * U.val = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp U.2.1

theorem g64_cov_unit {d : ℕ} (U W : g64G d) :
    covarianceMatrix U W * (covarianceMatrix U W)ᴴ = 1 := by
  simp only [g64_cov_kron, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, g64_unit,
    Matrix.one_kronecker_one]

theorem g64_cov_unit' {d : ℕ} (U W : g64G d) :
    (covarianceMatrix U W)ᴴ * covarianceMatrix U W = 1 := by
  simp only [g64_cov_kron, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, g64_unit',
    Matrix.one_kronecker_one]

theorem g64_cov_cont {d : ℕ} (x y : InversionWires d) :
    Continuous (fun z : g64G d × g64G d => covarianceMatrix z.1 z.2 x y) := by
  simp only [covarianceMatrix]
  exact (((g64_coe_cont _ _).comp continuous_fst).mul ((g64_coe_cont _ _).comp continuous_snd)).mul
    ((g64_coe_cont _ _).comp continuous_fst) |>.mul ((g64_coe_cont _ _).comp continuous_snd)

theorem g64_A_cont {β : Type*} [TopologicalSpace β] {n : Type} [Fintype n] (A : β → Matrix n n ℂ)
    (hA : ∀ x a, Continuous (fun U => A U x a)) (M : Matrix n n ℂ) (x y : n) :
    Continuous (fun U : β => (A U * M * (A U)ᴴ) x y) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  exact continuous_finsetSum _ (fun b _ => (continuous_finsetSum _ (fun a _ =>
    (hA x a).mul continuous_const)).mul (Complex.continuous_conj.comp (hA y b)))

theorem g64_tk_cont {d : ℕ} (C : CombMatrix d) (x y : InversionWires d) :
    Continuous (fun z => twirlKernel C z x y) :=
  g64_A_cont (fun z : g64G d × g64G d => covarianceMatrix z.1 z.2) g64_cov_cont C x y

theorem g64_tk_mul {d : ℕ} (C : CombMatrix d) (z0 z : g64G d × g64G d) :
    covarianceMatrix z0.1 z0.2 * twirlKernel C z * (covarianceMatrix z0.1 z0.2)ᴴ =
      twirlKernel C (z0 * z) := by
  simp only [twirlKernel, Prod.fst_mul, Prod.snd_mul, g64_cov_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]

theorem g64_twirl_inv {d : ℕ} (C : CombMatrix d) (U W : g64G d) :
    covarianceMatrix U W * inversionTwirl C * (covarianceMatrix U W)ᴴ = inversionTwirl C := by
  let L : CombMatrix d →L[ℂ] CombMatrix d :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => covarianceMatrix U W * M * (covarianceMatrix U W)ᴴ
        map_add' := fun M N => by simp [Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c M => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hint : Integrable (twirlKernel C) ((haar d).prod (haar d)) :=
    g64_int_comb _ _ (fun x y => g64_tk_cont C x y)
  have h1 : ∫ z, L (twirlKernel C z) ∂((haar d).prod (haar d)) =
      L (∫ z, twirlKernel C z ∂((haar d).prod (haar d))) := L.integral_comp_comm hint
  have h2 : ∀ z, L (twirlKernel C z) = twirlKernel C ((U, W) * z) := fun z => g64_tk_mul C (U, W) z
  have h3 : ∫ z, L (twirlKernel C z) ∂((haar d).prod (haar d)) =
      ∫ z, twirlKernel C ((U, W) * z) ∂((haar d).prod (haar d)) := congrArg _ (funext h2)
  rw [integral_mul_left_eq_self (fun z => twirlKernel C z) (U, W)] at h3
  exact (h1.symm.trans h3 : _)

theorem g64_covariant {d : ℕ} (C : CombMatrix d) : InversionCovariant (inversionTwirl C) := by
  intro U W
  conv_lhs => rw [← g64_twirl_inv C U W]
  rw [Matrix.mul_assoc, g64_cov_unit', Matrix.mul_one]

theorem g64_psd_of {α : Type*} [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (m : Measure α) [IsFiniteMeasure m]
    {n : Type} [Fintype n] (F : α → Matrix n n ℂ)
    (hc : ∀ x y, Continuous (fun U => F U x y))
    (hpsd : ∀ U, (F U).PosSemidef) : (Matrix.of fun x y => ∫ U, F U x y ∂m).PosSemidef := by
  have hI : ∀ x y, Integrable (fun U => F U x y) m :=
    fun x y => (hc x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext x y
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, RCLike.star_def, ← integral_conj]
    congr 1; funext U
    have := congrFun (congrFun (hpsd U).1.eq x) y
    rw [Matrix.conjTranspose_apply, RCLike.star_def] at this
    exact this
  · have hJ : ∀ a b, Integrable (fun U => star v a * (F U a b * v b)) m :=
      fun a b => ((hI a b).mul_const _).const_mul _
    have e : star v ⬝ᵥ (Matrix.of fun x y => ∫ U, F U x y ∂m) *ᵥ v = ∫ U, star v ⬝ᵥ (F U) *ᵥ v ∂m := by
      calc star v ⬝ᵥ (Matrix.of fun x y => ∫ U, F U x y ∂m) *ᵥ v
          = ∑ a, ∑ b, star v a * ((∫ U, F U a b ∂m) * v b) := by
            simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
        _ = ∑ a, ∑ b, ∫ U, star v a * (F U a b * v b) ∂m := by
            refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
            rw [integral_const_mul, integral_mul_const]
        _ = ∫ U, ∑ a, ∑ b, star v a * (F U a b * v b) ∂m := by
            rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hJ a b))]
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [integral_finsetSum _ (fun b _ => hJ a b)]
        _ = _ := by
            congr 1; funext U
            simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [e]
    have hq : (fun U => star v ⬝ᵥ (F U) *ᵥ v) = fun U => (((star v ⬝ᵥ (F U) *ᵥ v).re : ℝ) : ℂ) := by
      funext U
      have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hpsd U)).2 v
      exact Complex.ext (by simp) (by simp [(Complex.nonneg_iff.mp this).2])
    rw [hq, integral_complex_ofReal]
    refine Complex.zero_le_real.mpr (integral_nonneg (fun U => ?_))
    exact (Complex.nonneg_iff.mp ((Matrix.posSemidef_iff_dotProduct_mulVec.mp (hpsd U)).2 v)).1

theorem g64_twirl_eq {d : ℕ} (C : CombMatrix d) :
    inversionTwirl C = Matrix.of fun x y => ∫ z, twirlKernel C z x y ∂((haar d).prod (haar d)) := by
  ext x y
  exact g64_ent_comb _ _ (fun x y => g64_tk_cont C x y) x y

theorem g64_tk_psd {d : ℕ} (C : CombMatrix d) (hC : C.PosSemidef) (z : g64G d × g64G d) :
    (twirlKernel C z).PosSemidef := by
  unfold twirlKernel
  exact hC.mul_mul_conjTranspose_same _

theorem g64_tl_conj {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (A : Matrix α α ℂ) (hA : Aᴴ * A = 1)
    (R : Matrix β β ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft ((A ⊗ₖ R) * M * (A ⊗ₖ R)ᴴ) = R * traceLeft M * Rᴴ := by
  classical
  have hA' : ∀ x y, ∑ a, A a x * star (A a y) = if x = y then 1 else 0 := by
    intro x y
    have := congrFun (congrFun hA y) x
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.conjTranspose_apply] at this
    rw [eq_comm] at this
    by_cases h : x = y
    · subst h; rw [if_pos rfl] at this ⊢; rw [this]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    · rw [if_neg (Ne.symm h)] at this; rw [if_neg h, this]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  ext b b'
  have lhs : traceLeft ((A ⊗ₖ R) * M * (A ⊗ₖ R)ᴴ) b b' =
      ∑ y1, ∑ y2, ∑ x1, ∑ x2, (∑ a, A a x1 * star (A a y1)) *
        (R b x2 * M (x1, x2) (y1, y2) * star (R b' y2)) := by
    simp only [traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    simp only [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv
      { toFun := fun l => (l.2.1, l.2.2.1, l.2.2.2.1, l.2.2.2.2, l.1)
        invFun := fun r => (r.2.2.2.2, r.1, r.2.1, r.2.2.1, r.2.2.2.1)
        left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
    simp only [Equiv.coe_fn_mk, star_mul']; ring
  rw [lhs]
  simp only [hA']
  simp only [traceLeft, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y2 _ => ?_)
  conv_lhs => enter [2, y1]; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]

theorem g64_S_cont {d : ℕ} (x a : Pair d) :
    Continuous (fun z : g64G d × g64G d => (z.1.val ⊗ₖ z.2.val) x a) := by
  simp only [Matrix.kroneckerMap_apply]
  exact ((g64_coe_cont _ _).comp continuous_fst).mul ((g64_coe_cont _ _).comp continuous_snd)

theorem g64_comb {d : ℕ} (C : CombMatrix d) (hC : IsInversionComb C) :
    IsInversionComb (inversionTwirl C) := by
  obtain ⟨hpsd, B, hB, htl, htlB⟩ := hC
  let F : g64G d × g64G d → Matrix (Pair d) (Pair d) ℂ :=
    fun z => (z.1.val ⊗ₖ z.2.val) * B * (z.1.val ⊗ₖ z.2.val)ᴴ
  have hFc : ∀ p q, Continuous fun z => F z p q :=
    g64_A_cont (fun z : g64G d × g64G d => z.1.val ⊗ₖ z.2.val) g64_S_cont B
  have hFI : ∀ p q, Integrable (fun z => F z p q) ((haar d).prod (haar d)) := fun p q =>
    (hFc p q).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKI : ∀ x y, Integrable (fun z => twirlKernel C z x y) ((haar d).prod (haar d)) := fun x y =>
    (g64_tk_cont C x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨?_, Matrix.of fun p q => ∫ z, F z p q ∂((haar d).prod (haar d)),
    g64_psd_of _ F hFc (fun z => hB.mul_mul_conjTranspose_same _), ?_, ?_⟩
  · rw [g64_twirl_eq]; exact g64_psd_of _ _ (g64_tk_cont C) (g64_tk_psd C hpsd)
  · have hK : ∀ z, traceLeft (twirlKernel C z) = Matrix.kronecker 1 (F z) := by
      intro z
      unfold twirlKernel
      rw [g64_cov_kron, g64_tl_conj _ (g64_unit' z.1), htl]
      show (_ ⊗ₖ _) * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ B) * (_ ⊗ₖ _)ᴴ = (1 ⊗ₖ _)
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, g64_unit]
    ext ⟨c, p⟩ ⟨c', q⟩
    rw [g64_twirl_eq]
    simp only [traceLeft, Matrix.of_apply]
    rw [← integral_finsetSum _ (fun a _ => hKI _ _)]
    have h2 : ∀ z, ∑ a, twirlKernel C z (a, (c, p)) (a, (c', q)) =
        (1 : Matrix (Fin d) (Fin d) ℂ) c c' * F z p q := by
      intro z
      have := congrFun (congrFun (hK z) (c, p)) (c', q)
      simpa [traceLeft, Matrix.kronecker] using this
    simp only [h2]
    rw [integral_const_mul]
    rfl
  · ext p q
    simp only [traceLeft, Matrix.of_apply]
    rw [← integral_finsetSum _ (fun a _ => hFI _ _)]
    have h2 : ∀ z : g64G d × g64G d, ∑ a, F z (a, p) (a, q) = (1 : Matrix (Fin d) (Fin d) ℂ) p q := by
      intro z
      have := congrFun (congrFun (g64_tl_conj z.1.val (g64_unit' z.1) z.2.val B) p) q
      rw [htlB, Matrix.mul_one, g64_unit] at this
      simpa [traceLeft] using this
    simp only [h2]
    rw [integral_const]
    simp

instance g64_rinv (d : ℕ) : (haar d).IsMulRightInvariant := ⟨fun g => by
  have : IsProbabilityMeasure (Measure.map (· * g) (haar d)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _⟩

def g64_tr {d : ℕ} (W : g64G d) : g64G d :=
  ⟨W.valᵀ, by
    rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨?_, by rw [Matrix.det_transpose]; exact (Matrix.mem_specialUnitaryGroup_iff.mp W.2).2⟩
    rw [Matrix.mem_unitaryGroup_iff]
    have h := g64_unit' W
    have : W.valᵀ * star W.valᵀ = (W.valᴴ * W.val)ᵀ := by
      rw [Matrix.transpose_mul]; rfl
    rw [this, h, Matrix.transpose_one]⟩

theorem g64_fid_dot {d : ℕ} (M : CombMatrix d) (V : g64G d) :
    inversionFidelity M V =
      (star (inverseChoiTarget V) ⬝ᵥ (M *ᵥ inverseChoiTarget V)).re / (d : ℝ) ^ 2 := by
  unfold inversionFidelity
  congr 2
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def, mul_assoc]

theorem g64_target {d : ℕ} (C : CombMatrix d) (z : g64G d × g64G d) (V : g64G d) :
    (covarianceMatrix z.1 z.2)ᴴ *ᵥ inverseChoiTarget V =
      inverseChoiTarget (g64_tr z.2 * V * z.1) := by
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, covarianceMatrix, inverseChoiTarget,
    Submonoid.coe_mul, g64_tr, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul,
    RCLike.star_def, Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul, Finset.mul_sum]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (M := ℂ)
    { toFun := fun l : InversionWires d => ((l.2.2.1, l.2.1, l.1, l.2.2.2) : InversionWires d)
      invFun := fun r : InversionWires d => ((r.2.2.1, r.2.1, r.1, r.2.2.2) : InversionWires d)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]; ring


theorem g64_fid_tk {d : ℕ} (C : CombMatrix d) (z : g64G d × g64G d) (V : g64G d) :
    inversionFidelity (twirlKernel C z) V = inversionFidelity C (g64_tr z.2 * V * z.1) := by
  rw [g64_fid_dot, g64_fid_dot, ← g64_target C z V]
  have e : star (inverseChoiTarget V) ⬝ᵥ (twirlKernel C z *ᵥ inverseChoiTarget V) =
      star ((covarianceMatrix z.1 z.2)ᴴ *ᵥ inverseChoiTarget V) ⬝ᵥ
        (C *ᵥ ((covarianceMatrix z.1 z.2)ᴴ *ᵥ inverseChoiTarget V)) := by
    unfold twirlKernel
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose]
  rw [e]

theorem g64_fid_cont {d : ℕ} (C : CombMatrix d) : Continuous (fun V : g64G d => inversionFidelity C V) := by
  have hT : ∀ x, Continuous fun V : g64G d => inverseChoiTarget V x := fun x => by
    unfold inverseChoiTarget
    exact (Complex.continuous_conj.comp (g64_coe_cont _ _)).mul (Complex.continuous_conj.comp (g64_coe_cont _ _))
  unfold inversionFidelity
  refine (Complex.continuous_re.comp ?_).div_const _
  exact continuous_finsetSum _ (fun x _ => continuous_finsetSum _ (fun y _ =>
    ((Complex.continuous_conj.comp (hT x)).mul continuous_const).mul (hT y)))

theorem g64_tr_cont {d : ℕ} : Continuous (fun W : g64G d => g64_tr W) :=
  Continuous.subtype_mk continuous_subtype_val.matrix_transpose _

theorem g64_fid_twirl {d : ℕ} (C : CombMatrix d) (V : g64G d) :
    inversionFidelity (inversionTwirl C) V =
      ∫ z, inversionFidelity (twirlKernel C z) V ∂((haar d).prod (haar d)) := by
  have hKI : ∀ x y, Integrable (fun z => twirlKernel C z x y) ((haar d).prod (haar d)) := fun x y =>
    (g64_tk_cont C x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJ : ∀ x y, Integrable (fun z => conj (inverseChoiTarget V x) * twirlKernel C z x y *
      inverseChoiTarget V y) ((haar d).prod (haar d)) := fun x y => ((hKI x y).const_mul _).mul_const _
  rw [g64_twirl_eq]
  unfold inversionFidelity
  simp only [Matrix.of_apply]
  have e : ∑ x, ∑ y, conj (inverseChoiTarget V x) * (∫ z, twirlKernel C z x y ∂((haar d).prod (haar d))) *
      inverseChoiTarget V y = ∫ z, ∑ x, ∑ y, conj (inverseChoiTarget V x) * twirlKernel C z x y *
      inverseChoiTarget V y ∂((haar d).prod (haar d)) := by
    rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hJ x y))]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [integral_finsetSum _ (fun y _ => hJ x y)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [integral_mul_const, integral_const_mul]
  rw [e, integral_div]
  congr 1
  have hI : Integrable (fun z => ∑ x, ∑ y, conj (inverseChoiTarget V x) * twirlKernel C z x y *
      inverseChoiTarget V y) ((haar d).prod (haar d)) :=
    integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hJ x y))
  exact (integral_re hI).symm

theorem g64_avg_inv {d : ℕ} (C : CombMatrix d) (z : g64G d × g64G d) :
    ∫ V, inversionFidelity C (g64_tr z.2 * V * z.1) ∂haar d = inversionAverage C := by
  have h1 := integral_mul_right_eq_self (μ := haar d) (fun V => inversionFidelity C (g64_tr z.2 * V)) z.1
  simp only [← mul_assoc] at h1
  rw [h1, integral_mul_left_eq_self (fun V => inversionFidelity C V) (g64_tr z.2)]
  rfl

theorem g64_avg {d : ℕ} (C : CombMatrix d) : inversionAverage (inversionTwirl C) = inversionAverage C := by
  have hc : Continuous (Function.uncurry fun (V : g64G d) (z : g64G d × g64G d) =>
      inversionFidelity C (g64_tr z.2 * V * z.1)) := by
    refine (g64_fid_cont C).comp ?_
    exact ((g64_tr_cont.comp (continuous_snd.comp continuous_snd)).mul continuous_fst).mul
      (continuous_fst.comp continuous_snd)
  have hI := hc.integrable_of_hasCompactSupport (μ := (haar d).prod ((haar d).prod (haar d)))
    (HasCompactSupport.of_compactSpace _)
  unfold inversionAverage
  simp only [g64_fid_twirl, g64_fid_tk]
  rw [integral_integral_swap hI]
  simp only [g64_avg_inv]
  rw [integral_const]
  simp [inversionAverage]

/-- PDF p.3, Lemma 1 and its averaging proof. Printed quantified V is changed to U,
as required by the displayed action and the proof. Integrability is a conclusion. -/
theorem solution (d : ℕ) (hd : 2 ≤ d)
    (C : CombMatrix d) (hC : IsInversionComb C) :
    Integrable (twirlKernel C) ((haar d).prod (haar d)) ∧
    Integrable (inversionFidelity C) (haar d) ∧
    IsInversionComb (inversionTwirl C) ∧ InversionCovariant (inversionTwirl C) ∧
    inversionAverage (inversionTwirl C) = inversionAverage C ∧
    (Optimal C → Optimal (inversionTwirl C)) := by
  have hav := g64_avg C
  refine ⟨g64_int_comb _ _ (fun x y => g64_tk_cont C x y),
    (g64_fid_cont C).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),
    g64_comb C hC, g64_covariant C, hav, fun hO => ⟨g64_comb C hC, fun D hD => ?_⟩⟩
  rw [hav]; exact hO.2 D hD


end

