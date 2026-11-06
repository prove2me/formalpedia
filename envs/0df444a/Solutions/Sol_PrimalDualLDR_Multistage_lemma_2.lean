-- Prove2me | solution 1 for PrimalDualLDR.Multistage.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:21:16.24699+00:00
-- url     : https://prove2.me/submissions/a2fa6cdb-6ce9-415e-b5d1-de2f9b50a35f

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PDLDRCommon

open PrimalDualLDR.Multistage PrimalDualLDR.Multistage.Setting

variable (σ : Setting)

theorem ae_mem_Xi (hσ : σ.Standing) : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi := by
  rw [ae_iff]; exact hσ.2.1.2.1

/-- A continuous function that is a.s. nonnegative is nonnegative on `Ξ`. -/
theorem nonneg_on_Xi_of_ae (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ} (hf : Continuous f)
    (hae : ∀ᵐ ξ ∂σ.P, 0 ≤ f ξ) : ∀ ξ ∈ σ.Xi, 0 ≤ f ξ := by
  obtain ⟨-, ⟨-, -, hball⟩, -⟩ := hσ
  intro ξ₀ hξ₀
  by_contra hneg
  push Not at hneg
  have hopen : IsOpen {ξ : Fin σ.k → ℝ | f ξ < 0} := isOpen_lt hf continuous_const
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen ξ₀ hneg
  have hpos := hball ξ₀ hξ₀ ε hε
  have hnull : σ.P {ξ | ¬ 0 ≤ f ξ} = 0 := ae_iff.mp hae
  have : σ.P (Metric.ball ξ₀ ε) = 0 := by
    apply measure_mono_null _ hnull
    intro ξ hξ
    exact not_le.mpr (hsub hξ)
  exact (ne_of_gt hpos) this

theorem k_pos (hσ : σ.Standing) : 0 < σ.k := by
  obtain ⟨⟨hT, hk1⟩, -⟩ := hσ
  have : σ.kk ⟨0, hT⟩ ≤ σ.k := by
    unfold Setting.k ksum
    exact Finset.single_le_sum (f := σ.kk) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  omega

/-- On `Ξ`, the first coordinate equals `1`. -/
theorem Xi_first (hσ : σ.Standing) (ξ : Fin σ.k → ℝ) (hξ : ξ ∈ σ.Xi) :
    ξ ⟨0, k_pos σ hσ⟩ = 1 := by
  have hl := hσ.2.2.2.2.1
  have hrows := hσ.2.2.2.2.2.1
  have he : ∀ v : Fin σ.k → ℝ, PrimalDualLDR.FixedRecourse.e1 σ.k ⬝ᵥ v = v ⟨0, k_pos σ hσ⟩ := by
    intro v
    simp only [PrimalDualLDR.FixedRecourse.e1, dotProduct, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single ⟨0, k_pos σ hσ⟩]
    · intro b hb hne
      simp only [Finset.mem_filter] at hb
      exact absurd (Fin.ext hb.2) hne
    · intro h; simp at h
  have h0 := hξ ⟨0, by omega⟩
  have h1 := hξ ⟨1, by omega⟩
  obtain ⟨hW0, hh0⟩ := (hrows ⟨0, by omega⟩).1 rfl
  obtain ⟨hW1, hh1⟩ := (hrows ⟨1, by omega⟩).2.1 rfl
  simp only [Matrix.mulVec] at h0 h1
  rw [hW0, he, hh0] at h0
  rw [hW1, neg_dotProduct, he, hh1] at h1
  linarith

theorem Xi_bound (hσ : σ.Standing) : ∃ R : ℝ, 0 ≤ R ∧ ∀ ξ ∈ σ.Xi, ∀ j, |ξ j| ≤ R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin σ.k → ℝ)).mp hσ.2.2.2.1
  refine ⟨max R 0, le_max_right _ _, fun ξ hξ j => ?_⟩
  have := hR hξ
  rw [Metric.mem_closedBall, dist_zero_right] at this
  have := (norm_le_pi_norm ξ j).trans this
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem ae_bound (hσ : σ.Standing) : ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ ξ ∂σ.P, ∀ j, |ξ j| ≤ R := by
  obtain ⟨R, hR0, hR⟩ := Xi_bound σ hσ
  exact ⟨R, hR0, (ae_mem_Xi σ hσ).mono fun ξ hξ => hR ξ hξ⟩

theorem integrable_coord_mul_coord (hσ : σ.Standing) (i j : Fin σ.k) :
    Integrable (fun ξ : Fin σ.k → ℝ => ξ i * ξ j) σ.P := by
  obtain ⟨R, hR0, hR⟩ := ae_bound σ hσ
  refine Integrable.of_bound (((continuous_apply i).mul (continuous_apply j)).aestronglyMeasurable) (R * R) ?_
  filter_upwards [hR] with ξ hξ
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hξ i) (hξ j) (abs_nonneg _) hR0

theorem integrable_coord (hσ : σ.Standing) (j : Fin σ.k) :
    Integrable (fun ξ : Fin σ.k → ℝ => ξ j) σ.P := by
  obtain ⟨R, hR0, hR⟩ := ae_bound σ hσ
  refine Integrable.of_bound ((continuous_apply j).aestronglyMeasurable) R ?_
  filter_upwards [hR] with ξ hξ
  rw [Real.norm_eq_abs]; exact hξ j

theorem integrable_id (hσ : σ.Standing) : Integrable (fun ξ : Fin σ.k → ℝ => ξ) σ.P :=
  Integrable.of_eval (fun j => integrable_coord σ hσ j)

/-- `f ∈ L²` times a coordinate is integrable. -/
theorem integrable_mul_coord (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ} (hf : MemLp f 2 σ.P)
    (j : Fin σ.k) : Integrable (fun ξ => f ξ * ξ j) σ.P := by
  obtain ⟨R, hR0, hR⟩ := ae_bound σ hσ
  have hfi : Integrable f σ.P := hf.integrable one_le_two
  refine hfi.mul_bdd (c := R) ((continuous_apply j).aestronglyMeasurable) ?_
  filter_upwards [hR] with ξ hξ
  rw [Real.norm_eq_abs]; exact hξ j

theorem M_transpose : σ.Mᵀ = σ.M := by
  ext i j; simp [Setting.M, mul_comm]

theorem quad_M (hσ : σ.Standing) (v : Fin σ.k → ℝ) :
    v ⬝ᵥ σ.M.mulVec v = ∫ ξ, (v ⬝ᵥ ξ) ^ 2 ∂σ.P := by
  have : ∀ ξ : Fin σ.k → ℝ, (v ⬝ᵥ ξ) ^ 2 = ∑ i, ∑ j, v i * v j * (ξ i * ξ j) := by
    intro ξ
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [this]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integrable_coord_mul_coord σ hσ i j).const_mul _))]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable_coord_mul_coord σ hσ i j).const_mul _)]
  apply Finset.sum_congr rfl; intro j _
  rw [integral_const_mul]; simp only [Setting.M]; ring

theorem M_posDef (hσ : σ.Standing) (v : Fin σ.k → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ σ.M.mulVec v := by
  rw [quad_M σ hσ]
  have hint : Integrable (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) σ.P := by
    have : (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) =
        fun ξ => ∑ i, ∑ j, v i * v j * (ξ i * ξ j) := by
      funext ξ
      simp only [dotProduct, sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
    rw [this]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (integrable_coord_mul_coord σ hσ i j).const_mul _))
  rcases (integral_nonneg (fun ξ => sq_nonneg (v ⬝ᵥ ξ)) : 0 ≤ ∫ ξ, (v ⬝ᵥ ξ) ^ 2 ∂σ.P).lt_or_eq
    with h | h
  · exact h
  exfalso
  have hae : (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) =ᵐ[σ.P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ξ => sq_nonneg _) hint).mp h.symm
  have hcont : Continuous fun ξ : Fin σ.k → ℝ => -(v ⬝ᵥ ξ) ^ 2 := by
    simp only [dotProduct]; fun_prop
  have hXi := nonneg_on_Xi_of_ae σ hσ hcont (hae.mono fun ξ hξ => by simp at hξ; simp [hξ])
  have hzero : ∀ ξ ∈ σ.Xi, v ⬝ᵥ ξ = 0 := by
    intro ξ hξ
    have := hXi ξ hξ
    have h2 := sq_nonneg (v ⬝ᵥ ξ)
    nlinarith
  have hspan : Submodule.span ℝ σ.Xi ≤ LinearMap.ker (dotProductBilin ℝ ℝ v) := by
    rw [Submodule.span_le]
    intro ξ hξ
    simp [hzero ξ hξ]
  rw [hσ.2.2.2.2.2.2] at hspan
  apply hv
  funext i
  have := hspan (Submodule.mem_top (x := Pi.single i 1))
  simpa using this

theorem Pt_mul_transpose (t : Fin σ.T) : σ.Pt t * (σ.Pt t)ᵀ = 1 := by
  ext i j
  simp only [Setting.Pt, Pmat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  by_cases h : i = j
  · subst h; simp
  · simp only [h, if_false]
    rw [if_neg]
    intro h'
    exact h (Fin.castLE_injective _ h').symm

theorem G_posDef (hσ : σ.Standing) (t : Fin σ.T) (v : Fin (σ.kb t) → ℝ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (σ.Pt t * σ.M * (σ.Pt t)ᵀ).mulVec v := by
  have hw : (σ.Pt t)ᵀ.mulVec v ≠ 0 := by
    intro h
    apply hv
    have := congrArg (σ.Pt t).mulVec h
    rwa [Matrix.mulVec_mulVec, Pt_mul_transpose, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  have := M_posDef σ hσ _ hw
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  exact this

theorem G_isUnit (hσ : σ.Standing) (t : Fin σ.T) :
    IsUnit (σ.Pt t * σ.M * (σ.Pt t)ᵀ).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := G_posDef σ hσ t v hv
  rw [hGv, dotProduct_zero] at this
  exact lt_irrefl _ this

end PDLDRCommon


namespace PDLDRCommon

open PrimalDualLDR.Multistage PrimalDualLDR.Multistage.Setting

variable (σ : Setting)

theorem F_le (t : Fin σ.T) : σ.F t ≤ MeasurableSpace.pi :=
  (measurable_trunc σ.kk t).comap_le

theorem sm_comp_tr (t : Fin σ.T) {g : (Fin (σ.kb t) → ℝ) → ℝ} (hg : Measurable g) :
    StronglyMeasurable[σ.F t] (fun ξ => g (σ.tr t ξ)) :=
  (hg.comp (comap_measurable (σ.tr t))).stronglyMeasurable

/-- Pull-out: `∫ f u = ∫ f 𝔼[u | m]` for `m`-measurable `f`. -/
theorem integral_mul_condExp {m : MeasurableSpace (Fin σ.k → ℝ)}
    (hm : m ≤ MeasurableSpace.pi)
    {f u : (Fin σ.k → ℝ) → ℝ} (hf : StronglyMeasurable[m] f)
    (hfu : Integrable (f * u) σ.P) (hu : Integrable u σ.P) :
    ∫ ξ, f ξ * u ξ ∂σ.P = ∫ ξ, f ξ * (σ.P[u | m]) ξ ∂σ.P := by
  have h1 := integral_condExp (μ := σ.P) (f := f * u) hm
  rw [show (fun ξ => f ξ * u ξ) = f * u from rfl, ← h1]
  exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hf hfu hu)

/-- `∫ 𝔼[v | m] w = ∫ v w` for `m`-measurable `w`. -/
theorem integral_condExp_mul {m : MeasurableSpace (Fin σ.k → ℝ)}
    (hm : m ≤ MeasurableSpace.pi)
    {v w : (Fin σ.k → ℝ) → ℝ} (hw : StronglyMeasurable[m] w)
    (hvw : Integrable (v * w) σ.P) (hv : Integrable v σ.P) :
    ∫ ξ, (σ.P[v | m]) ξ * w ξ ∂σ.P = ∫ ξ, v ξ * w ξ ∂σ.P := by
  have h1 := integral_condExp (μ := σ.P) (f := v * w) hm
  rw [show (fun ξ => v ξ * w ξ) = v * w from rfl, ← h1]
  exact (integral_congr_ae (condExp_mul_of_stronglyMeasurable_right hw hvw hv)).symm

theorem condExp_coord (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T) (j : Fin σ.k) :
    σ.P[fun ξ : Fin σ.k → ℝ => ξ j | σ.F t] =ᵐ[σ.P]
      fun ξ => (σ.Mt t * σ.Pt t).mulVec ξ j := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin σ.k => ℝ) j).comp_condExp_comm
    (μ := σ.P) (m := σ.F t) (integrable_id σ hσ)
  refine h.symm.trans ?_
  filter_upwards [hM t] with ξ hξ
  simp [hξ]

theorem mulVec_MtPt (t : Fin σ.T) (ξ : Fin σ.k → ℝ) (j : Fin σ.k) :
    (σ.Mt t * σ.Pt t).mulVec ξ j = (σ.Mt t).mulVec (σ.tr t ξ) j := by
  rw [← Matrix.mulVec_mulVec, Setting.Pt, Pmat_mulVec]

/-- The key conditional-mean identity: for `F_t`-measurable `f`, `∫ f ξ_j = ∫ f (M_t P_t ξ)_j`. -/
theorem integral_mul_coord_eq (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T)
    {f : (Fin σ.k → ℝ) → ℝ} (hf : StronglyMeasurable[σ.F t] f) (hf2 : MemLp f 2 σ.P)
    (j : Fin σ.k) :
    ∫ ξ, f ξ * ξ j ∂σ.P = ∫ ξ, f ξ * (σ.Mt t * σ.Pt t).mulVec ξ j ∂σ.P := by
  rw [integral_mul_condExp σ (F_le σ t) hf (integrable_mul_coord σ hσ hf2 j)
    (integrable_coord σ hσ j)]
  apply integral_congr_ae
  filter_upwards [condExp_coord σ hσ hM t j] with ξ hξ
  simp only [hξ]

theorem integral_mul_MtPt (hσ : σ.Standing) (t : Fin σ.T) {f : (Fin σ.k → ℝ) → ℝ}
    (hf2 : MemLp f 2 σ.P) (j : Fin σ.k) :
    ∫ ξ, f ξ * (σ.Mt t * σ.Pt t).mulVec ξ j ∂σ.P =
      ∑ b, (σ.Mt t * σ.Pt t) j b * ∫ ξ, f ξ * ξ b ∂σ.P := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [integral_finsetSum _ fun b _ => (integrable_mul_coord σ hσ hf2 b).const_mul ((σ.Mt t * σ.Pt t) j b)
    |>.congr (Filter.Eventually.of_forall fun ξ => by ring)]
  apply Finset.sum_congr rfl; intro b _
  rw [← integral_const_mul]; congr 1; funext ξ; ring

/-- For a stage-`t` rule, `𝔼(x ξᵀ) = 𝔼(x ξᵀ) (M_t P_t)ᵀ`. -/
theorem moment_eq_mul (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T) {d : ℕ}
    (x : (Fin (σ.kb t) → ℝ) → (Fin d → ℝ)) (hx : σ.IsL2RuleAt t x) :
    σ.moment t x = σ.moment t x * (σ.Mt t * σ.Pt t)ᵀ := by
  ext a j
  have hfa : MemLp (fun ξ => x (σ.tr t ξ) a) 2 σ.P := hx.2.eval a
  have hsm : StronglyMeasurable[σ.F t] (fun ξ => x (σ.tr t ξ) a) :=
    sm_comp_tr σ t ((measurable_pi_apply a).comp hx.1)
  have e : (σ.moment t x * (σ.Mt t * σ.Pt t)ᵀ) a j =
      ∑ b, (∫ ξ, x (σ.tr t ξ) a * ξ b ∂σ.P) * (σ.Mt t * σ.Pt t) j b := by
    rw [Matrix.mul_apply]; rfl
  rw [e]
  show ∫ ξ, x (σ.tr t ξ) a * ξ j ∂σ.P = _
  rw [integral_mul_coord_eq σ hσ hM t hsm hfa j, integral_mul_MtPt σ hσ t hfa j]
  apply Finset.sum_congr rfl; intro b _; ring

theorem memLp_tr (hσ : σ.Standing) (t : Fin σ.T) :
    MemLp (fun ξ => σ.tr t ξ) 2 σ.P := by
  obtain ⟨R, hR0, hR⟩ := ae_bound σ hσ
  apply MemLp.of_eval
  intro i
  refine MemLp.of_bound ((continuous_apply _).aestronglyMeasurable) R ?_
  filter_upwards [hR] with ξ hξ
  rw [Real.norm_eq_abs]; exact hξ _

theorem isL2_id (hσ : σ.Standing) (t : Fin σ.T) :
    σ.IsL2RuleAt t (fun z : Fin (σ.kb t) → ℝ => z) :=
  ⟨measurable_id, memLp_tr σ hσ t⟩

theorem moment_id (t : Fin σ.T) : σ.moment t (fun z : Fin (σ.kb t) → ℝ => z) = σ.Pt t * σ.M := by
  ext i j
  simp only [Setting.moment, Matrix.mul_apply, Setting.Pt, Pmat, Matrix.of_apply, ite_mul,
    one_mul, zero_mul, Setting.M]
  rw [Finset.sum_ite_eq']; simp; rfl

/-- `P_t M = P_t M P_tᵀ M_tᵀ`. -/
theorem PM_eq (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T) :
    σ.Pt t * σ.M = σ.Pt t * σ.M * (σ.Pt t)ᵀ * (σ.Mt t)ᵀ := by
  have := moment_eq_mul σ hσ hM t _ (isL2_id σ hσ t)
  rw [moment_id] at this
  conv_lhs => rw [this]
  rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

/-- Lemma 2, general dimension. -/
theorem lemma2_gen (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T) {d : ℕ}
    (x : (Fin (σ.kb t) → ℝ) → (Fin d → ℝ)) (hx : σ.IsL2RuleAt t x) :
    ∃! X : Matrix (Fin d) (Fin (σ.kb t)) ℝ, X * σ.Pt t * σ.M = σ.moment t x := by
  set G := σ.Pt t * σ.M * (σ.Pt t)ᵀ with hG
  have hGu : IsUnit G.det := G_isUnit σ hσ t
  refine ⟨σ.moment t x * (σ.Pt t)ᵀ * G⁻¹, ?_, ?_⟩
  · show σ.moment t x * (σ.Pt t)ᵀ * G⁻¹ * σ.Pt t * σ.M = σ.moment t x
    rw [Matrix.mul_assoc _ (σ.Pt t), PM_eq σ hσ hM t, ← hG,
      ← Matrix.mul_assoc (σ.moment t x * (σ.Pt t)ᵀ * G⁻¹) G,
      Matrix.mul_assoc (σ.moment t x * (σ.Pt t)ᵀ) G⁻¹ G, Matrix.nonsing_inv_mul _ hGu,
      Matrix.mul_one, Matrix.mul_assoc, ← Matrix.transpose_mul]
    exact (moment_eq_mul σ hσ hM t x hx).symm
  · intro Y hY
    have h1 : Y * G = σ.moment t x * (σ.Pt t)ᵀ := by
      rw [← hY, hG]; simp only [Matrix.mul_assoc]
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]

end PDLDRCommon


theorem solution (σ : PrimalDualLDR.Multistage.Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean)
    (t : Fin σ.T) :
    (∀ x : (Fin (σ.kb t) → ℝ) → (Fin (σ.n t) → ℝ), σ.IsL2RuleAt t x →
      ∃! X : Matrix (Fin (σ.n t)) (Fin (σ.kb t)) ℝ, X * σ.Pt t * σ.M = σ.moment t x) ∧
    (∀ s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ), σ.IsL2RuleAt t s →
      ∃! S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ, S * σ.Pt t * σ.M = σ.moment t s) :=
  ⟨fun x hx => PDLDRCommon.lemma2_gen σ hσ hM t x hx,
    fun s hs => PDLDRCommon.lemma2_gen σ hσ hM t s hs⟩
