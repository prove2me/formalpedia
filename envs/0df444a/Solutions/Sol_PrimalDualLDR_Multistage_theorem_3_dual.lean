-- Prove2me | solution 1 for PrimalDualLDR.Multistage.theorem_3_dual
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:34:35.81798+00:00
-- url     : https://prove2.me/submissions/13cdc101-3206-4328-ab08-a80db25c6d5a

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

theorem mul_Pt_transpose_apply (t : Fin σ.T) {a : Type*} (Z : Matrix a (Fin σ.k) ℝ) (i : a)
    (j : Fin (σ.kb t)) :
    (Z * (σ.Pt t)ᵀ) i j = Z i (Fin.castLE (kbar_le_ksum σ.kk t) j) := by
  simp only [Setting.Pt, Pmat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']; simp

theorem tr_apply (t : Fin σ.T) (ξ : Fin σ.k → ℝ) (j : Fin (σ.kb t)) :
    σ.tr t ξ j = ξ (Fin.castLE (kbar_le_ksum σ.kk t) j) := rfl

/-- (4.7) ⇔ the equality constraint of (4.6): pure algebra. -/
theorem eq47_iff_eq46 (hσ : σ.Standing) (t : Fin σ.T) (X : σ.XFam)
    (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ) :
    (∑ r, σ.A t r * X r * σ.Pt r * σ.M * (σ.Pt t)ᵀ + S * σ.Pt t * σ.M * (σ.Pt t)ᵀ =
        σ.B t * σ.Pt t * σ.M * (σ.Pt t)ᵀ) ↔
      ∑ r, σ.A t r * X r * σ.Pt r * σ.N t * σ.Pt t + S * σ.Pt t = σ.B t * σ.Pt t := by
  set P := σ.Pt t with hP
  set G := P * σ.M * Pᵀ with hG
  have hGu : IsUnit G.det := G_isUnit σ hσ t
  have hPP : P * Pᵀ = 1 := Pt_mul_transpose σ t
  set L := ∑ r, σ.A t r * X r * σ.Pt r with hL
  have e1 : ∑ r, σ.A t r * X r * σ.Pt r * σ.M * Pᵀ = L * σ.M * Pᵀ := by
    rw [hL, Matrix.sum_mul, Matrix.sum_mul]
  have e2 : ∑ r, σ.A t r * X r * σ.Pt r * σ.N t * P = L * σ.N t * P := by
    rw [hL, Matrix.sum_mul, Matrix.sum_mul]
  have hN : σ.N t = σ.M * Pᵀ * G⁻¹ := rfl
  rw [e1, e2, hN]
  constructor
  · intro h
    have h' := congrArg (fun Z => Z * G⁻¹ * P) h
    simp only [Matrix.add_mul] at h'
    have a1 : S * P * σ.M * Pᵀ * G⁻¹ * P = S * P := by
      rw [show S * P * σ.M * Pᵀ = S * G by simp only [hG, Matrix.mul_assoc],
        Matrix.mul_assoc S G, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]
    have a2 : σ.B t * P * σ.M * Pᵀ * G⁻¹ * P = σ.B t * P := by
      rw [show σ.B t * P * σ.M * Pᵀ = σ.B t * G by simp only [hG, Matrix.mul_assoc],
        Matrix.mul_assoc (σ.B t) G, Matrix.mul_nonsing_inv _ hGu, Matrix.mul_one]
    rw [a1, a2] at h'
    rw [← h']
    simp only [Matrix.mul_assoc]
  · intro h
    have h' := congrArg (fun Z => Z * Pᵀ * G) h
    simp only [Matrix.add_mul] at h'
    have a1 : L * (σ.M * Pᵀ * G⁻¹) * P * Pᵀ * G = L * σ.M * Pᵀ := by
      rw [Matrix.mul_assoc _ P, hPP, Matrix.mul_one, Matrix.mul_assoc,
        Matrix.mul_assoc (σ.M * Pᵀ), Matrix.nonsing_inv_mul _ hGu, Matrix.mul_one,
        Matrix.mul_assoc]
    have a2 : S * P * Pᵀ * G = S * P * σ.M * Pᵀ := by
      rw [Matrix.mul_assoc S P, hPP, Matrix.mul_one, hG]; simp only [Matrix.mul_assoc]
    have a3 : σ.B t * P * Pᵀ * G = σ.B t * P * σ.M * Pᵀ := by
      rw [Matrix.mul_assoc (σ.B t) P, hPP, Matrix.mul_one, hG]; simp only [Matrix.mul_assoc]
    rw [a1, a2, a3] at h'
    exact h'

/-- The integral defining the `t`-th equality constraint of `𝓜𝒮𝒫^l`, in terms of the moments. -/
theorem eqMSPl_integral (hσ : σ.Standing) (t : Fin σ.T) (x : σ.XRules)
    (s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ)) (X : σ.XFam)
    (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ)
    (hx : ∀ r, σ.IsL2RuleAt r (x r)) (hs : σ.IsL2RuleAt t s)
    (hX : ∀ r, X r * σ.Pt r * σ.M = σ.moment r (x r)) (hS : S * σ.Pt t * σ.M = σ.moment t s)
    (i : Fin (σ.m t)) (j : Fin (σ.kb t)) :
    ∫ ξ, ((∑ r, (σ.A t r).mulVec (x r (σ.tr r ξ))) + s (σ.tr t ξ) -
      (σ.B t * σ.Pt t).mulVec ξ) i * σ.tr t ξ j ∂σ.P =
    (∑ r, σ.A t r * X r * σ.Pt r * σ.M * (σ.Pt t)ᵀ + S * σ.Pt t * σ.M * (σ.Pt t)ᵀ -
        σ.B t * σ.Pt t * σ.M * (σ.Pt t)ᵀ) i j := by
  set c := Fin.castLE (kbar_le_ksum σ.kk t) j
  have hpt : ∀ ξ : Fin σ.k → ℝ,
      ((∑ r, (σ.A t r).mulVec (x r (σ.tr r ξ))) + s (σ.tr t ξ) -
        (σ.B t * σ.Pt t).mulVec ξ) i * σ.tr t ξ j =
      (∑ r, ∑ a, σ.A t r i a * (x r (σ.tr r ξ) a * ξ c)) + s (σ.tr t ξ) i * ξ c -
        ∑ b, (σ.B t * σ.Pt t) i b * (ξ b * ξ c) := by
    intro ξ
    rw [tr_apply]
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Matrix.mulVec, dotProduct,
      sub_mul, add_mul, Finset.sum_mul]
    congr 1; congr 1
    · apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro a _; ring
    · apply Finset.sum_congr rfl; intro b _; ring
  simp_rw [hpt]
  have ix : ∀ r a, Integrable (fun ξ => x r (σ.tr r ξ) a * ξ c) σ.P :=
    fun r a => integrable_mul_coord σ hσ ((hx r).2.eval a) c
  have is : Integrable (fun ξ => s (σ.tr t ξ) i * ξ c) σ.P :=
    integrable_mul_coord σ hσ (hs.2.eval i) c
  have ib : ∀ b, Integrable (fun ξ : Fin σ.k → ℝ => ξ b * ξ c) σ.P :=
    fun b => integrable_coord_mul_coord σ hσ b c
  rw [integral_sub, integral_add, integral_finsetSum, integral_finsetSum]
  rotate_left
  · exact fun b _ => (ib b).const_mul _
  · exact fun r _ => integrable_finsetSum _ fun a _ => (ix r a).const_mul _
  · exact integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun a _ => (ix r a).const_mul _
  · exact is
  · exact (integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun a _ =>
      (ix r a).const_mul _).add is
  · exact integrable_finsetSum _ fun b _ => (ib b).const_mul _
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply]
  simp_rw [mul_Pt_transpose_apply σ t]
  congr 1; congr 1
  · apply Finset.sum_congr rfl; intro r _
    rw [integral_finsetSum _ fun a _ => (ix r a).const_mul _]
    rw [Matrix.mul_assoc (σ.A t r * X r), Matrix.mul_assoc (σ.A t r), ← Matrix.mul_assoc (X r),
      hX r]
    simp only [Matrix.mul_apply, integral_const_mul, Setting.moment]; rfl
  · rw [hS]; rfl
  · simp only [integral_const_mul, Matrix.mul_apply, Setting.M]; rfl

theorem sec_4_eq_4_7_proof (σ : Setting) (hσ : σ.Standing) (t : Fin σ.T) :
    (∀ (x : σ.XRules) (s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ)) (X : σ.XFam)
        (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ),
        (∀ r, σ.IsL2RuleAt r (x r)) → σ.IsL2RuleAt t s →
        (∀ r, X r * σ.Pt r * σ.M = σ.moment r (x r)) → S * σ.Pt t * σ.M = σ.moment t s →
        (σ.eqMSPl t x s ↔
          ∑ r, σ.A t r * X r * σ.Pt r * σ.M * (σ.Pt t)ᵀ + S * σ.Pt t * σ.M * (σ.Pt t)ᵀ =
            σ.B t * σ.Pt t * σ.M * (σ.Pt t)ᵀ)) ∧
    (∀ (X : σ.XFam) (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ),
        (∑ r, σ.A t r * X r * σ.Pt r * σ.M * (σ.Pt t)ᵀ + S * σ.Pt t * σ.M * (σ.Pt t)ᵀ =
            σ.B t * σ.Pt t * σ.M * (σ.Pt t)ᵀ) ↔
          ∑ r, σ.A t r * X r * σ.Pt r * σ.N t * σ.Pt t + S * σ.Pt t = σ.B t * σ.Pt t) := by
  refine ⟨fun x s X S hx hs hX hS => ?_, fun X S => eq47_iff_eq46 σ hσ t X S⟩
  unfold Setting.eqMSPl
  simp_rw [eqMSPl_integral σ hσ t x s X S hx hs hX hS]
  rw [← sub_eq_zero]
  constructor
  · intro h; ext i j; exact h i j
  · intro h i j; rw [h]; rfl

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

theorem PM_eq' (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T) {d : ℕ}
    (S : Matrix (Fin d) (Fin (σ.kb t)) ℝ) :
    S * σ.Pt t * σ.M = S * σ.Pt t * σ.M * (σ.Mt t * σ.Pt t)ᵀ := by
  conv_lhs => rw [Matrix.mul_assoc S, PM_eq σ hσ hM t]
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

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


namespace PDLDRCommon

open PrimalDualLDR.Multistage PrimalDualLDR.Multistage.Setting

variable (σ : Setting)

theorem integrable_mul_MtPt (hσ : σ.Standing) (t : Fin σ.T) {f : (Fin σ.k → ℝ) → ℝ}
    (hf2 : MemLp f 2 σ.P) (j : Fin σ.k) :
    Integrable (fun ξ => f ξ * (σ.Mt t * σ.Pt t).mulVec ξ j) σ.P := by
  have : (fun ξ => f ξ * (σ.Mt t * σ.Pt t).mulVec ξ j) =
      fun ξ => ∑ b, (σ.Mt t * σ.Pt t) j b * (f ξ * ξ b) := by
    funext ξ; simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring
  rw [this]
  exact integrable_finsetSum _ fun b _ => (integrable_mul_coord σ hσ hf2 b).const_mul _

theorem sm_MtPt (t : Fin σ.T) (j : Fin σ.k) :
    StronglyMeasurable[σ.F t] (fun ξ => (σ.Mt t * σ.Pt t).mulVec ξ j) := by
  have : (fun ξ => (σ.Mt t * σ.Pt t).mulVec ξ j) = fun ξ => (σ.Mt t).mulVec (σ.tr t ξ) j := by
    funext ξ; exact mulVec_MtPt σ t ξ j
  rw [this]
  have hc : Continuous fun z : Fin (σ.kb t) → ℝ => (σ.Mt t).mulVec z j := by
    simp only [Matrix.mulVec, dotProduct]; fun_prop
  exact sm_comp_tr σ t (g := fun z => (σ.Mt t).mulVec z j) hc.measurable

theorem lemma3_proof (hσ : σ.Standing) (hM : σ.LinearCondMean) (t : Fin σ.T)
    (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ) :
    (∃ s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ), σ.IsL2RuleAt t s ∧
      σ.moment t s = S * σ.Pt t * σ.M ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ s (σ.tr t ξ) i) ↔
    (∃ st : (Fin σ.k → ℝ) → (Fin (σ.m t) → ℝ), PrimalDualLDR.FixedRecourse.IsL2Rule σ.P st ∧
      (fun i j => ∫ ξ, st ξ i * ξ j ∂σ.P) = S * σ.Pt t * σ.M ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ st ξ i) := by
  constructor
  · rintro ⟨s, hs, hmom, hnn⟩
    exact ⟨fun ξ => s (σ.tr t ξ), ⟨hs.1.comp (measurable_trunc σ.kk t), hs.2⟩, hmom, hnn⟩
  · rintro ⟨st, hst, hmom, hnn⟩
    set u := σ.P[st | σ.F t] with hu
    have hum : StronglyMeasurable[σ.F t] u := stronglyMeasurable_condExp
    obtain ⟨g, hg, hgu⟩ := hum.exists_eq_measurable_comp
    have hu2 : MemLp u 2 σ.P := hst.2.condExp one_le_two
    have hstint : Integrable st σ.P := hst.2.integrable one_le_two
    have hcomp : ∀ i, (fun ξ => u ξ i) =ᵐ[σ.P] σ.P[fun ξ => st ξ i | σ.F t] := fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (σ.m t) => ℝ) i).comp_condExp_comm
        (μ := σ.P) (m := σ.F t) hstint
    refine ⟨g, ⟨hg.measurable, ?_⟩, ?_, ?_⟩
    · have : (fun ξ => g (σ.tr t ξ)) = u := by rw [hgu]; rfl
      rw [this]; exact hu2
    · ext i j
      have hgi : ∀ ξ, g (σ.tr t ξ) i = u ξ i := fun ξ => by rw [hgu]; rfl
      show ∫ ξ, g (σ.tr t ξ) i * ξ j ∂σ.P = _
      simp_rw [hgi]
      have hui2 : MemLp (fun ξ => u ξ i) 2 σ.P := hu2.eval i
      have huim : StronglyMeasurable[σ.F t] (fun ξ => u ξ i) :=
        (continuous_apply i).comp_stronglyMeasurable hum
      rw [integral_mul_coord_eq σ hσ hM t huim hui2 j]
      have hsti2 : MemLp (fun ξ => st ξ i) 2 σ.P := hst.2.eval i
      rw [integral_congr_ae (g := fun ξ => σ.P[fun ξ => st ξ i | σ.F t] ξ *
        (σ.Mt t * σ.Pt t).mulVec ξ j) ((hcomp i).mono fun ξ hξ => by
          simp only at hξ; simp only [hξ])]
      rw [integral_condExp_mul σ (F_le σ t) (sm_MtPt σ t j)
        (integrable_mul_MtPt σ hσ t hsti2 j) (hsti2.integrable one_le_two)]
      rw [integral_mul_MtPt σ hσ t hsti2 j]
      have hmomi : ∀ b, ∫ ξ, st ξ i * ξ b ∂σ.P = (S * σ.Pt t * σ.M) i b := fun b =>
        congrFun (congrFun hmom i) b
      simp_rw [hmomi]
      conv_rhs => rw [PM_eq' σ hσ hM t S]
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl; intro b _
      rw [Matrix.transpose_apply]; ring
    · have hall : ∀ i, ∀ᵐ ξ ∂σ.P, 0 ≤ u ξ i := by
        intro i
        have h0 : 0 ≤ᵐ[σ.P] σ.P[fun ξ => st ξ i | σ.F t] :=
          condExp_nonneg (hnn.mono fun ξ hξ => hξ i)
        filter_upwards [h0, hcomp i] with ξ h1 h2
        rw [h2]; exact h1
      rw [← ae_all_iff] at hall
      filter_upwards [hall] with ξ hξ i
      have : g (σ.tr t ξ) = u ξ := by rw [hgu]; rfl
      rw [this]; exact hξ i

end PDLDRCommon


namespace PDLDRCommon

open PrimalDualLDR.Multistage PrimalDualLDR.Multistage.Setting

variable (σ : Setting)

/-- The cone `𝒦_P` of first-order moments of nonnegative square-integrable densities. -/
def KP : Set (Fin σ.k → ℝ) :=
  {z | ∃ s : (Fin σ.k → ℝ) → ℝ, Measurable s ∧ MemLp s 2 σ.P ∧ (∀ᵐ ξ ∂σ.P, 0 ≤ s ξ) ∧
    ∀ b, ∫ ξ, s ξ * ξ b ∂σ.P = z b}

/-- The strict version of `𝒦`: every nonzero row of `W − h e₁ᵀ` is strictly positive on `z`. -/
def Ustr : Set (Fin σ.k → ℝ) :=
  {z | ∀ i, σ.Wtilde i ≠ 0 → 0 < (σ.Wtilde.mulVec z) i}

theorem Wtilde_mulVec (z : Fin σ.k → ℝ) (i : Fin σ.l) (hk : 0 < σ.k) :
    (σ.Wtilde.mulVec z) i = (σ.W.mulVec z) i - σ.h i * z ⟨0, hk⟩ := by
  simp only [Setting.Wtilde, Matrix.sub_mulVec, Pi.sub_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, PrimalDualLDR.FixedRecourse.e1]
  rw [Finset.sum_eq_single ⟨0, hk⟩]
  · simp
  · intro b _ hb
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [this]
  · simp

/-- `Ξ = {v : v₀ = 1, (W − h e₁ᵀ) v ≥ 0}`. -/
theorem mem_Xi_iff (hσ : σ.Standing) (v : Fin σ.k → ℝ) :
    v ∈ σ.Xi ↔ v ⟨0, k_pos σ hσ⟩ = 1 ∧ ∀ i, 0 ≤ (σ.Wtilde.mulVec v) i := by
  constructor
  · intro hv
    have h1 := Xi_first σ hσ v hv
    refine ⟨h1, fun i => ?_⟩
    rw [Wtilde_mulVec σ v i (k_pos σ hσ), h1]
    have := hv i
    linarith
  · rintro ⟨h1, h2⟩ i
    have := h2 i
    rw [Wtilde_mulVec σ v i (k_pos σ hσ), h1] at this
    show σ.h i ≤ σ.W.mulVec v i
    linarith

theorem Wtilde_row_ne (hσ : σ.Standing) (i : Fin σ.l) (hi : σ.Wtilde i ≠ 0) :
    2 ≤ i.val ∧ σ.Wtilde i = σ.W i := by
  have hrows := hσ.2.2.2.2.2.1 i
  have key : ∀ j, σ.Wtilde i j = σ.W i j - σ.h i * PrimalDualLDR.FixedRecourse.e1 σ.k j := by
    intro j; simp [Setting.Wtilde, Matrix.vecMulVec_apply]
  by_cases h0 : i.val = 0
  · obtain ⟨hW, hh⟩ := hrows.1 h0
    exfalso; apply hi; funext j; rw [key, hW, hh]; simp
  by_cases h1 : i.val = 1
  · obtain ⟨hW, hh⟩ := hrows.2.1 h1
    exfalso; apply hi; funext j; rw [key, hW, hh]; simp
  have h2 : 2 ≤ i.val := by omega
  refine ⟨h2, ?_⟩
  funext j; rw [key, hrows.2.2 h2]; simp

/-- Under the repair hypothesis, `W − h e₁ᵀ` has a nonzero row. -/
theorem exists_Wtilde_row (hσ : σ.Standing)
    (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) : ∃ i, σ.Wtilde i ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hk := k_pos σ hσ
  rcases hW with hk2 | ⟨i, hi2, hWi⟩
  · -- all rows vanish, so `Ξ = {v₀ = 1}` is unbounded
    obtain ⟨R, hR0, hR⟩ := Xi_bound σ hσ
    let v : Fin σ.k → ℝ := fun j => if j.val = 0 then 1 else if j.val = 1 then R + 1 else 0
    have hv : v ∈ σ.Xi := by
      rw [mem_Xi_iff σ hσ]
      refine ⟨by simp [v], fun i => ?_⟩
      simp only [Matrix.mulVec]; rw [hcon i]; simp
    have := hR v hv ⟨1, by omega⟩
    simp [v] at this
    rw [abs_of_pos (by linarith)] at this
    linarith
  · apply hWi
    have := hcon i
    have hrows := hσ.2.2.2.2.2.1 i
    funext j
    have h := congrFun this j
    simp only [Setting.Wtilde, Matrix.sub_apply, Matrix.vecMulVec_apply, hrows.2.2 hi2,
      zero_mul, sub_zero] at h
    simpa using h

theorem Ustr_subset_K (z : Fin σ.k → ℝ) (hz : z ∈ (Ustr σ)) (i : Fin σ.l) :
    0 ≤ (σ.Wtilde.mulVec z) i := by
  by_cases hi : σ.Wtilde i = 0
  · simp [Matrix.mulVec, dotProduct, hi]
  · exact (hz i hi).le

/-- Points of `Ustr` have positive first coordinate. -/
theorem Ustr_first_pos (hσ : σ.Standing)
    (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) (z : Fin σ.k → ℝ) (hz : z ∈ (Ustr σ)) :
    0 < z ⟨0, k_pos σ hσ⟩ := by
  have hk := k_pos σ hσ
  set z0 := z ⟨0, hk⟩
  by_contra hneg
  push Not at hneg
  obtain ⟨i0, hi0⟩ := exists_Wtilde_row σ hσ hW
  obtain ⟨ξ0, hξ0⟩ := hσ.2.2.1
  have hξ0' := (mem_Xi_iff σ hσ ξ0).mp hξ0
  set y := z - z0 • ξ0
  have hline : ∀ t : ℝ, 0 ≤ t → ξ0 + t • y ∈ σ.Xi := by
    intro t ht
    rw [mem_Xi_iff σ hσ]
    refine ⟨?_, fun i => ?_⟩
    · simp [y, hξ0'.1, z0]
    · simp only [y, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.add_apply,
        Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have a := hξ0'.2 i
      have b := Ustr_subset_K σ z hz i
      have c : 0 ≤ -z0 * (σ.Wtilde.mulVec ξ0) i := mul_nonneg (by linarith) a
      nlinarith
  have hy : y = 0 := by
    obtain ⟨R, hR0, hR⟩ := Xi_bound σ hσ
    funext j
    by_contra hyj
    have hyj' : 0 < |y j| := abs_pos.mpr hyj
    set t := (R + |ξ0 j| + 1) / |y j|
    have ht : 0 ≤ t := div_nonneg (by positivity) hyj'.le
    have := hR _ (hline t ht) j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have e : t * |y j| = R + |ξ0 j| + 1 := div_mul_cancel₀ _ hyj'.ne'
    have h1 : |t * y j| ≤ |ξ0 j + t * y j| + |ξ0 j| := by
      have := abs_sub (ξ0 j + t * y j) (ξ0 j)
      simpa using this
    rw [abs_mul, abs_of_nonneg ht, e] at h1
    linarith
  have hzeq : z = z0 • ξ0 := by
    have : z - z0 • ξ0 = 0 := hy
    exact sub_eq_zero.mp this
  have := hz i0 hi0
  rw [hzeq, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at this
  have := mul_nonpos_of_nonpos_of_nonneg hneg (hξ0'.2 i0)
  linarith

theorem KP_convex (hσ : σ.Standing) : Convex ℝ (KP σ) := by
  rintro z1 ⟨s1, hm1, hl1, hn1, he1⟩ z2 ⟨s2, hm2, hl2, hn2, he2⟩ a b ha hb _
  refine ⟨fun ξ => a * s1 ξ + b * s2 ξ, (hm1.const_mul a).add (hm2.const_mul b),
    (hl1.const_mul a).add (hl2.const_mul b), ?_, fun j => ?_⟩
  · filter_upwards [hn1, hn2] with ξ h1 h2
    positivity
  · have i1 := integrable_mul_coord σ hσ hl1 j
    have i2 := integrable_mul_coord σ hσ hl2 j
    have : (fun ξ : Fin σ.k → ℝ => (a * s1 ξ + b * s2 ξ) * ξ j) =
        fun ξ => a * (s1 ξ * ξ j) + b * (s2 ξ * ξ j) := by funext ξ; ring
    rw [this, integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul,
      integral_const_mul, he1, he2]
    simp

theorem smul_mem_KP (c : ℝ) (hc : 0 ≤ c) (z : Fin σ.k → ℝ) (hz : z ∈ (KP σ)) : c • z ∈ (KP σ) := by
  obtain ⟨s, hm, hl, hn, he⟩ := hz
  refine ⟨fun ξ => c * s ξ, hm.const_mul c, hl.const_mul c, ?_, fun j => ?_⟩
  · filter_upwards [hn] with ξ h; positivity
  · have : (fun ξ : Fin σ.k → ℝ => c * s ξ * ξ j) = fun ξ => c * (s ξ * ξ j) := by
      funext ξ; ring
    rw [this, integral_const_mul, he]; simp

theorem zero_mem_KP : (0 : Fin σ.k → ℝ) ∈ (KP σ) :=
  ⟨fun _ => 0, measurable_const, MemLp.zero' , Filter.Eventually.of_forall fun _ => le_rfl,
    fun j => by simp⟩

/-- A linear functional that is nonpositive on `𝒦_P` is nonpositive on `Ξ`. -/
theorem nonpos_on_Xi_of_KP (hσ : σ.Standing) (π : Fin σ.k → ℝ)
    (hπ : ∀ z ∈ (KP σ), π ⬝ᵥ z ≤ 0) : ∀ ξ ∈ σ.Xi, π ⬝ᵥ ξ ≤ 0 := by
  obtain ⟨R, hR0, hR⟩ := ae_bound σ hσ
  have hcπ : Continuous fun ξ : Fin σ.k → ℝ => π ⬝ᵥ ξ := by
    simp only [dotProduct]; fun_prop
  let s : (Fin σ.k → ℝ) → ℝ := fun ξ => if 0 < π ⬝ᵥ ξ then 1 else 0
  have hsm : Measurable s :=
    Measurable.ite (measurableSet_lt measurable_const hcπ.measurable) measurable_const
      measurable_const
  have hsl : MemLp s 2 σ.P := by
    refine MemLp.of_bound hsm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [s]; split_ifs <;> simp
  have hmem : (fun b => ∫ ξ, s ξ * ξ b ∂σ.P) ∈ (KP σ) :=
    ⟨s, hsm, hsl, Filter.Eventually.of_forall fun ξ => by simp only [s]; split_ifs <;> simp,
      fun b => rfl⟩
  have h1 := hπ _ hmem
  have hsum : π ⬝ᵥ (fun b => ∫ ξ, s ξ * ξ b ∂σ.P) = ∫ ξ, s ξ * (π ⬝ᵥ ξ) ∂σ.P := by
    simp only [dotProduct, Finset.mul_sum]
    rw [integral_finsetSum _ fun b _ => (integrable_mul_coord σ hσ hsl b).const_mul (π b)
      |>.congr (Filter.Eventually.of_forall fun ξ => by ring)]
    apply Finset.sum_congr rfl; intro b _
    rw [← integral_const_mul]; congr 1; funext ξ; ring
  rw [hsum] at h1
  have hnn : 0 ≤ fun ξ => s ξ * (π ⬝ᵥ ξ) := fun ξ => by
    simp only [s]; split_ifs with h
    · simp [h.le]
    · simp
  have hint : Integrable (fun ξ => s ξ * (π ⬝ᵥ ξ)) σ.P := by
    have : (fun ξ => s ξ * (π ⬝ᵥ ξ)) = fun ξ => ∑ b, π b * (s ξ * ξ b) := by
      funext ξ; simp only [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _; ring
    rw [this]
    exact integrable_finsetSum _ fun b _ => (integrable_mul_coord σ hσ hsl b).const_mul _
  have h0 : ∫ ξ, s ξ * (π ⬝ᵥ ξ) ∂σ.P = 0 := le_antisymm h1 (integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp h0
  have hae' : ∀ᵐ ξ ∂σ.P, 0 ≤ -(π ⬝ᵥ ξ) := by
    filter_upwards [hae] with ξ hξ
    simp only [s, Pi.zero_apply] at hξ
    split_ifs at hξ with h
    · simp at hξ; linarith
    · push Not at h; linarith
  intro ξ hξ
  have := nonneg_on_Xi_of_ae σ hσ (f := fun ξ => -(π ⬝ᵥ ξ)) hcπ.neg hae' ξ hξ
  linarith

theorem Ustr_subset_closure_KP (hσ : σ.Standing)
    (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) : (Ustr σ) ⊆ closure (KP σ) := by
  intro w hw
  by_contra hcl
  obtain ⟨f, u, hfu, hfw⟩ :=
    geometric_hahn_banach_closed_point (KP_convex σ hσ).closure isClosed_closure hcl
  have hu : 0 < u := by
    have := hfu 0 (subset_closure (zero_mem_KP σ))
    rwa [ContinuousLinearMap.map_zero] at this
  have hf_nonpos : ∀ a ∈ (KP σ), f a ≤ 0 := by
    intro a ha
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (u / f a)
    have := hfu ((n : ℝ) • a) (subset_closure (smul_mem_KP σ n (Nat.cast_nonneg n) a ha))
    rw [ContinuousLinearMap.map_smul, smul_eq_mul] at this
    rw [div_lt_iff₀ hpos] at hn
    linarith
  let π : Fin σ.k → ℝ := fun b => f (Pi.single b 1)
  have hfπ : ∀ z, f z = π ⬝ᵥ z := by
    intro z
    conv_lhs => rw [pi_eq_sum_univ z]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, π]
    apply Finset.sum_congr rfl; intro b _
    rw [mul_comm]; congr 2; funext j; simp [Pi.single_apply, eq_comm]
  have hXi := nonpos_on_Xi_of_KP σ hσ π (fun z hz => by rw [← hfπ]; exact hf_nonpos z hz)
  have hk := k_pos σ hσ
  have hw0 := Ustr_first_pos σ hσ hW w hw
  have hv : (w ⟨0, hk⟩)⁻¹ • w ∈ σ.Xi := by
    rw [mem_Xi_iff σ hσ]
    refine ⟨by simp [hw0.ne'], fun i => ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hw0.le) (Ustr_subset_K σ w hw i)
  have := hXi _ hv
  rw [dotProduct_smul, smul_eq_mul] at this
  have hπw : π ⬝ᵥ w ≤ 0 := by
    by_contra h; push Not at h
    have := mul_pos (inv_pos.mpr hw0) h
    linarith
  rw [hfπ] at hfw
  linarith

theorem Ustr_open : IsOpen (Ustr σ) := by
  have : (Ustr σ) = ⋂ i, {z : Fin σ.k → ℝ | σ.Wtilde i ≠ 0 → 0 < (σ.Wtilde.mulVec z) i} := by
    ext z; simp [Ustr]
  rw [this]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : σ.Wtilde i = 0
  · simp [hi]
  · simp only [ne_eq, hi, not_false_eq_true, forall_true_left]
    apply isOpen_lt continuous_const
    simp only [Matrix.mulVec, dotProduct]; fun_prop

/-- Proposition 3 (the inclusion `int 𝒦 ⊂ 𝒦_P`, in the form used for (4.6)). -/
theorem Ustr_subset_KP (hσ : σ.Standing)
    (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) : (Ustr σ) ⊆ (KP σ) := by
  intro z hz
  have hconv := KP_convex σ hσ
  have hsub : (Ustr σ) ⊆ interior (closure (KP σ)) :=
    interior_maximal (Ustr_subset_closure_KP σ hσ hW) (Ustr_open σ)
  have hne : (interior (closure (KP σ))).Nonempty := ⟨z, hsub hz⟩
  have haff : affineSpan ℝ (closure (KP σ)) = ⊤ :=
    (hconv.closure.interior_nonempty_iff_affineSpan_eq_top).mp hne
  have haff2 : affineSpan ℝ (KP σ) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← haff]
    apply affineSpan_le.mpr
    exact closure_minimal (subset_affineSpan ℝ _)
      (AffineSubspace.closed_of_finiteDimensional _)
  have hint : (interior (KP σ)).Nonempty := (hconv.interior_nonempty_iff_affineSpan_eq_top).mpr haff2
  rw [hconv.interior_closure_eq_interior_of_nonempty_interior hint] at hsub
  exact interior_subset (hsub hz)

end PDLDRCommon


namespace PDLDRCommon

open PrimalDualLDR.Multistage PrimalDualLDR.Multistage.Setting

variable (σ : Setting)

theorem trace_eq_sum (t : Fin σ.T) (X : Matrix (Fin (σ.n t)) (Fin (σ.kb t)) ℝ) :
    Matrix.trace (σ.Pt t * σ.M * (σ.Pt t)ᵀ * (σ.C t)ᵀ * X) =
      ∑ a, ∑ b, (σ.C t * σ.Pt t) a b * (X * σ.Pt t * σ.M) a b := by
  rw [Matrix.trace_mul_comm]
  have : X * (σ.Pt t * σ.M * (σ.Pt t)ᵀ * (σ.C t)ᵀ) =
      (X * σ.Pt t * σ.M) * (σ.C t * σ.Pt t)ᵀ := by
    rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  rw [this]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring

theorem ruleObj_eq (hσ : σ.Standing) (x : σ.XRules) (X : σ.XFam)
    (hx : ∀ t, σ.IsL2RuleAt t (x t)) (hX : ∀ t, X t * σ.Pt t * σ.M = σ.moment t (x t)) :
    σ.ruleObj x = σ.linObj X := by
  unfold Setting.ruleObj Setting.linObj
  have hpt : ∀ ξ : Fin σ.k → ℝ, ∑ t, ((σ.C t * σ.Pt t).mulVec ξ) ⬝ᵥ x t (σ.tr t ξ) =
      ∑ t, ∑ a, ∑ b, (σ.C t * σ.Pt t) a b * (x t (σ.tr t ξ) a * ξ b) := by
    intro ξ; apply Finset.sum_congr rfl; intro t _
    simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
  simp_rw [hpt]
  have hi : ∀ t a b, Integrable (fun ξ => x t (σ.tr t ξ) a * ξ b) σ.P :=
    fun t a b => integrable_mul_coord σ hσ ((hx t).2.eval a) b
  rw [integral_finsetSum (f := fun t ξ => ∑ a, ∑ b, (σ.C t * σ.Pt t) a b *
      (x t (σ.tr t ξ) a * ξ b)) _ (fun t _ => integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun b _ => (hi t a b).const_mul _)]
  apply Finset.sum_congr rfl; intro t _
  rw [trace_eq_sum, hX t]
  rw [integral_finsetSum (f := fun a ξ => ∑ b, (σ.C t * σ.Pt t) a b *
      (x t (σ.tr t ξ) a * ξ b)) _
    (fun a _ => integrable_finsetSum _ fun b _ => (hi t a b).const_mul _)]
  apply Finset.sum_congr rfl; intro a _
  rw [integral_finsetSum (f := fun b ξ => (σ.C t * σ.Pt t) a b * (x t (σ.tr t ξ) a * ξ b)) _
    (fun b _ => (hi t a b).const_mul _)]
  apply Finset.sum_congr rfl; intro b _
  rw [integral_const_mul]; rfl

theorem memLp_lin (hσ : σ.Standing) (t : Fin σ.T) {d : ℕ}
    (Y : Matrix (Fin d) (Fin (σ.kb t)) ℝ) : MemLp (fun ξ => Y.mulVec (σ.tr t ξ)) 2 σ.P := by
  apply MemLp.of_eval; intro a
  simp only [Matrix.mulVec, dotProduct]
  exact memLp_finsetSum _ fun c _ => ((memLp_tr σ hσ t).eval c).const_mul (Y a c)

theorem isL2_lin (hσ : σ.Standing) (t : Fin σ.T) {d : ℕ}
    (Y : Matrix (Fin d) (Fin (σ.kb t)) ℝ) : σ.IsL2RuleAt t (fun z => Y.mulVec z) :=
  ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, memLp_lin σ hσ t Y⟩

theorem moment_lin (hσ : σ.Standing) (t : Fin σ.T) {d : ℕ}
    (Y : Matrix (Fin d) (Fin (σ.kb t)) ℝ) :
    σ.moment t (fun z => Y.mulVec z) = Y * σ.Pt t * σ.M := by
  ext a b
  have hi : ∀ c, Integrable (fun ξ => Y a c * σ.tr t ξ c * ξ b) σ.P := fun c =>
    ((integrable_mul_coord σ hσ ((memLp_tr σ hσ t).eval c) b).const_mul (Y a c)).congr
      (Filter.Eventually.of_forall fun ξ => by simp only; ring)
  simp only [Setting.moment, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [integral_finsetSum _ fun c _ => hi c]
  rw [Matrix.mul_assoc, Matrix.mul_apply, ← moment_id σ t]
  apply Finset.sum_congr rfl; intro c _
  rw [show (fun ξ => Y a c * σ.tr t ξ c * ξ b) = fun ξ => Y a c * (σ.tr t ξ c * ξ b) by
    funext ξ; ring, integral_const_mul]
  rfl

theorem cone_entry (t : Fin σ.T) (S : Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ)
    (i : Fin σ.l) (j : Fin (σ.m t)) :
    (σ.Wtilde * σ.M * (σ.Pt t)ᵀ * Sᵀ) i j = (σ.Wtilde.mulVec ((S * σ.Pt t * σ.M) j)) i := by
  have : σ.Wtilde * σ.M * (σ.Pt t)ᵀ * Sᵀ = σ.Wtilde * (S * σ.Pt t * σ.M)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, M_transpose]; simp only [Matrix.mul_assoc]
  rw [this, Matrix.mul_apply]; rfl

theorem integrable_mul_dot (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ} (hf : MemLp f 2 σ.P)
    (v : Fin σ.k → ℝ) : Integrable (fun ξ => f ξ * (v ⬝ᵥ ξ)) σ.P := by
  have : (fun ξ => f ξ * (v ⬝ᵥ ξ)) = fun ξ => ∑ b, v b * (f ξ * ξ b) := by
    funext ξ; simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _; ring
  rw [this]
  exact integrable_finsetSum _ fun b _ => (integrable_mul_coord σ hσ hf b).const_mul _

theorem Wtilde_moment (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ} (hf : MemLp f 2 σ.P)
    (i : Fin σ.l) :
    (σ.Wtilde.mulVec (fun b => ∫ ξ, f ξ * ξ b ∂σ.P)) i =
      ∫ ξ, f ξ * (σ.Wtilde.mulVec ξ) i ∂σ.P := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [integral_finsetSum _ fun b _ => ((integrable_mul_coord σ hσ hf b).const_mul
    (σ.Wtilde i b)).congr (Filter.Eventually.of_forall fun ξ => by simp only; ring)]
  apply Finset.sum_congr rfl; intro b _; rw [← integral_const_mul]; congr 1; funext ξ; ring

theorem ae_Wtilde_nonneg (hσ : σ.Standing) : ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ (σ.Wtilde.mulVec ξ) i := by
  filter_upwards [ae_mem_Xi σ hσ] with ξ hξ
  exact ((mem_Xi_iff σ hσ ξ).mp hξ).2

theorem eq_zero_of_dot_Xi (hσ : σ.Standing) (v : Fin σ.k → ℝ)
    (hv : ∀ ξ ∈ σ.Xi, v ⬝ᵥ ξ = 0) : v = 0 := by
  have hspan : Submodule.span ℝ σ.Xi ≤ LinearMap.ker (dotProductBilin ℝ ℝ v) := by
    rw [Submodule.span_le]
    intro ξ hξ
    simp [hv ξ hξ]
  rw [hσ.2.2.2.2.2.2] at hspan
  funext i
  have := hspan (Submodule.mem_top (x := Pi.single i 1))
  simpa using this

/-- A real number bounded above by `L + θ c` for all `θ ∈ (0,1]` is at most `L`. -/
theorem ereal_limit (V : EReal) (L c : ℝ)
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → V ≤ ((L + θ * c : ℝ) : EReal)) : V ≤ (L : EReal) := by
  induction V using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd (h 1 one_pos le_rfl) (not_le.mpr (EReal.coe_lt_top _))
  | coe v =>
    rw [EReal.coe_le_coe_iff]
    by_contra hlt
    push Not at hlt
    set θ := min 1 ((v - L) / (2 * (|c| + 1)))
    have hpos : 0 < (v - L) / (2 * (|c| + 1)) := by
      apply div_pos (by linarith); positivity
    have hθ : 0 < θ := lt_min one_pos hpos
    have hθ1 : θ ≤ 1 := min_le_left _ _
    have hθ2 : θ ≤ (v - L) / (2 * (|c| + 1)) := min_le_right _ _
    have := h θ hθ hθ1
    rw [EReal.coe_le_coe_iff] at this
    have h3 : θ * c ≤ θ * (|c| + 1) := by
      apply mul_le_mul_of_nonneg_left _ hθ.le; linarith [le_abs_self c]
    have h4 : θ * (|c| + 1) ≤ (v - L) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      rw [le_div_iff₀ (by positivity)] at hθ2
      nlinarith
    linarith

/-- The strictly feasible point of (4.6) induced by strict feasibility of `𝓜𝒮𝒫`. -/
theorem strict_point (hσ : σ.Standing) (hM : σ.LinearCondMean) (hsf : σ.StrictlyFeasible) :
    ∃ (Xb : σ.XFam) (Sb : σ.SFam),
      (∀ t, ∑ r, σ.A t r * Xb r * σ.Pt r * σ.N t * σ.Pt t + Sb t * σ.Pt t = σ.B t * σ.Pt t) ∧
      ∀ t j i, σ.Wtilde i ≠ 0 → 0 < (σ.Wtilde.mulVec ((Sb t * σ.Pt t * σ.M) j)) i := by
  obtain ⟨ε, hε, xb, sb, hxb, hsb, hfeas⟩ := hsf
  choose Xb hXb using fun t => (lemma2_gen σ hσ hM t (xb t) (hxb t)).exists
  choose Sb hSb using fun t => (lemma2_gen σ hσ hM t (sb t) (hsb t)).exists
  refine ⟨Xb, Sb, fun t => ?_, fun t j i hi => ?_⟩
  · have hEq : σ.eqMSPl t xb (sb t) := by
      intro i j
      set V : (Fin σ.k → ℝ) → (Fin (σ.m t) → ℝ) :=
        fun ξ' => ∑ s, (σ.A t s).mulVec (xb s (σ.tr s ξ')) with hV
      have hVi : ∀ i, (fun ξ => V ξ i) =
          fun ξ => ∑ r, ∑ a, σ.A t r i a * xb r (σ.tr r ξ) a := by
        intro i; funext ξ; simp [hV, Finset.sum_apply, Matrix.mulVec, dotProduct]
      have hVi2 : ∀ i, MemLp (fun ξ => V ξ i) 2 σ.P := by
        intro i; rw [hVi]
        exact memLp_finsetSum _ fun r _ => memLp_finsetSum _ fun a _ =>
          ((hxb r).2.eval a).const_mul _
      have hV2 : MemLp V 2 σ.P := MemLp.of_eval hVi2
      have hVint : Integrable V σ.P := hV2.integrable one_le_two
      set c := Fin.castLE (kbar_le_ksum σ.kk t) j
      have hw : StronglyMeasurable[σ.F t] (fun ξ : Fin σ.k → ℝ => ξ c) :=
        sm_comp_tr σ t (g := fun z => z j) (measurable_pi_apply j)
      have hcomp : (fun ξ => (σ.P[V | σ.F t]) ξ i) =ᵐ[σ.P] σ.P[fun ξ => V ξ i | σ.F t] :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (σ.m t) => ℝ) i).comp_condExp_comm
          (μ := σ.P) (m := σ.F t) hVint
      have hCi2 : MemLp (fun ξ => (σ.P[V | σ.F t]) ξ i) 2 σ.P :=
        (hV2.condExp one_le_two).eval i
      have hae : (fun ξ => ((∑ r, (σ.A t r).mulVec (xb r (σ.tr r ξ))) + sb t (σ.tr t ξ) -
          (σ.B t * σ.Pt t).mulVec ξ) i * σ.tr t ξ j) =ᵐ[σ.P]
          fun ξ => V ξ i * ξ c - (σ.P[V | σ.F t]) ξ i * ξ c := by
        filter_upwards [hfeas t] with ξ hξ
        have h1 := congrFun hξ.1 i
        simp only [Pi.add_apply] at h1
        rw [tr_apply]
        simp only [Pi.sub_apply, Pi.add_apply]
        rw [← h1]
        simp only [hV]; ring
      rw [integral_congr_ae hae, integral_sub (integrable_mul_coord σ hσ (hVi2 i) c)
        (integrable_mul_coord σ hσ hCi2 c)]
      have e2 : ∫ ξ, (σ.P[V | σ.F t]) ξ i * ξ c ∂σ.P = ∫ ξ, V ξ i * ξ c ∂σ.P := by
        rw [integral_congr_ae (f := fun ξ => (σ.P[V | σ.F t]) ξ i * ξ c)
          (g := fun ξ => (σ.P[fun ξ => V ξ i | σ.F t]) ξ * ξ c)
          (hcomp.mono fun ξ hξ => by simp only at hξ; simp only [hξ])]
        exact integral_condExp_mul σ (F_le σ t) hw (integrable_mul_coord σ hσ (hVi2 i) c)
          ((hVi2 i).integrable one_le_two)
      rw [e2, sub_self]
    have h47 := ((sec_4_eq_4_7_proof σ hσ t).1 xb (sb t) Xb (Sb t) hxb (hsb t) hXb (hSb t)).mp hEq
    exact ((sec_4_eq_4_7_proof σ hσ t).2 Xb (Sb t)).mp h47
  · have hrow : (Sb t * σ.Pt t * σ.M) j = fun b => ∫ ξ, sb t (σ.tr t ξ) j * ξ b ∂σ.P := by
      rw [hSb t]; rfl
    have hf2 : MemLp (fun ξ => sb t (σ.tr t ξ) j) 2 σ.P := (hsb t).2.eval j
    rw [hrow, Wtilde_moment σ hσ hf2 i]
    have hWi : Integrable (fun ξ : Fin σ.k → ℝ => (σ.Wtilde.mulVec ξ) i) σ.P := by
      simp only [Matrix.mulVec, dotProduct]
      exact integrable_finsetSum _ fun b _ => (integrable_coord σ hσ b).const_mul _
    have hpos : 0 < ∫ ξ, (σ.Wtilde.mulVec ξ) i ∂σ.P := by
      have hnn : ∀ᵐ ξ ∂σ.P, 0 ≤ (σ.Wtilde.mulVec ξ) i :=
        (ae_Wtilde_nonneg σ hσ).mono fun ξ hξ => hξ i
      rcases (integral_nonneg_of_ae hnn).lt_or_eq with h | h
      · exact h
      exfalso
      have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hWi).mp h.symm
      have hc : Continuous fun ξ : Fin σ.k → ℝ => (σ.Wtilde.mulVec ξ) i := by
        simp only [Matrix.mulVec, dotProduct]; fun_prop
      have h1 := nonneg_on_Xi_of_ae σ hσ (f := fun ξ => -(σ.Wtilde.mulVec ξ) i) hc.neg
        (hz.mono fun ξ hξ => by simp only [Pi.zero_apply] at hξ; simp [hξ])
      apply hi
      apply eq_zero_of_dot_Xi σ hσ
      intro ξ hξ
      have := h1 ξ hξ
      have := ((mem_Xi_iff σ hσ ξ).mp hξ).2 i
      show (σ.Wtilde.mulVec ξ) i = 0
      linarith
    have hmono : ∫ ξ, ε * (σ.Wtilde.mulVec ξ) i ∂σ.P ≤
        ∫ ξ, sb t (σ.tr t ξ) j * (σ.Wtilde.mulVec ξ) i ∂σ.P := by
      apply integral_mono_ae (hWi.const_mul ε) (integrable_mul_dot σ hσ hf2 (σ.Wtilde i))
      filter_upwards [ae_Wtilde_nonneg σ hσ, hfeas t] with ξ h1 h2
      exact mul_le_mul_of_nonneg_right (h2.2 j) (h1 i)
    rw [integral_const_mul] at hmono
    have := mul_pos hε hpos
    linarith

/-- Every point of (4.6) whose slack rows lie in `Ustr` is attained by `𝓜𝒮𝒫^l`. -/
theorem realize (hσ : σ.Standing) (hM : σ.LinearCondMean)
    (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) (X : σ.XFam) (S : σ.SFam)
    (heq : ∀ t, ∑ r, σ.A t r * X r * σ.Pt r * σ.N t * σ.Pt t + S t * σ.Pt t = σ.B t * σ.Pt t)
    (hrow : ∀ t j, (S t * σ.Pt t * σ.M) j ∈ Ustr σ) :
    ∃ p ∈ σ.feasMSPl, σ.ruleObj p.1 = σ.linObj X := by
  have hKP : ∀ t j, (S t * σ.Pt t * σ.M) j ∈ KP σ := fun t j =>
    Ustr_subset_KP σ hσ hW (hrow t j)
  choose st hstm hstl hstn hste using hKP
  have hs : ∀ t, ∃ s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ), σ.IsL2RuleAt t s ∧
      σ.moment t s = S t * σ.Pt t * σ.M ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ s (σ.tr t ξ) i := by
    intro t
    apply (lemma3_proof σ hσ hM t (S t)).mpr
    refine ⟨fun ξ j => st t j ξ, ⟨measurable_pi_lambda _ fun j => hstm t j,
      MemLp.of_eval fun j => hstl t j⟩, ?_, ?_⟩
    · ext i b; exact hste t i b
    · rw [ae_all_iff]; exact fun i => hstn t i
  choose s hsl hsm hsn using hs
  let x : σ.XRules := fun t z => (X t).mulVec z
  have hxl : ∀ t, σ.IsL2RuleAt t (x t) := fun t => isL2_lin σ hσ t (X t)
  have hxm : ∀ t, X t * σ.Pt t * σ.M = σ.moment t (x t) := fun t =>
    (moment_lin σ hσ t (X t)).symm
  refine ⟨(x, s), ⟨hxl, hsl, fun t => ⟨?_, hsn t⟩⟩, ruleObj_eq σ hσ x X hxl hxm⟩
  apply ((sec_4_eq_4_7_proof σ hσ t).1 x (s t) X (S t) hxl (hsl t) hxm (hsm t).symm).mpr
  exact ((sec_4_eq_4_7_proof σ hσ t).2 X (S t)).mpr (heq t)

theorem dual_main (hσ : σ.Standing) (hM : σ.LinearCondMean) (hsf : σ.StrictlyFeasible)
    (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) :
    σ.valMSPl = σ.valLP46 := by
  apply le_antisymm
  · unfold Setting.valLP46
    apply le_iInf₂
    rintro ⟨X, S⟩ hp
    obtain ⟨Xb, Sb, hbeq, hbrow⟩ := strict_point σ hσ hM hsf
    have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → σ.valMSPl ≤
        ((σ.linObj X + θ * (σ.linObj Xb - σ.linObj X) : ℝ) : EReal) := by
      intro θ hθ hθ1
      let Xθ : σ.XFam := fun t => (1 - θ) • X t + θ • Xb t
      let Sθ : σ.SFam := fun t => (1 - θ) • S t + θ • Sb t
      have heq : ∀ t, ∑ r, σ.A t r * Xθ r * σ.Pt r * σ.N t * σ.Pt t + Sθ t * σ.Pt t =
          σ.B t * σ.Pt t := by
        intro t
        have e : ∑ r, σ.A t r * Xθ r * σ.Pt r * σ.N t * σ.Pt t + Sθ t * σ.Pt t =
            (1 - θ) • (∑ r, σ.A t r * X r * σ.Pt r * σ.N t * σ.Pt t + S t * σ.Pt t) +
            θ • (∑ r, σ.A t r * Xb r * σ.Pt r * σ.N t * σ.Pt t + Sb t * σ.Pt t) := by
          simp only [Xθ, Sθ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
          abel
        rw [e, (hp t).1, hbeq t, ← add_smul]; simp
      have hrow : ∀ t j, (Sθ t * σ.Pt t * σ.M) j ∈ Ustr σ := by
        intro t j i hi
        have e : Sθ t * σ.Pt t * σ.M = (1 - θ) • (S t * σ.Pt t * σ.M) + θ • (Sb t * σ.Pt t * σ.M) := by
          simp only [Sθ, Matrix.add_mul, Matrix.smul_mul]
        rw [e]
        show 0 < (σ.Wtilde.mulVec ((1 - θ) • (S t * σ.Pt t * σ.M) j +
          θ • (Sb t * σ.Pt t * σ.M) j)) i
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 : 0 ≤ (σ.Wtilde.mulVec ((S t * σ.Pt t * σ.M) j)) i := by
          rw [← cone_entry]; exact (hp t).2 i j
        have h2 := hbrow t j i hi
        have h3 : 0 ≤ (1 - θ) * (σ.Wtilde.mulVec ((S t * σ.Pt t * σ.M) j)) i :=
          mul_nonneg (by linarith) h1
        have h4 := mul_pos hθ h2
        linarith
      obtain ⟨q, hq, hobj⟩ := realize σ hσ hM hW Xθ Sθ heq hrow
      have hlin : σ.linObj Xθ = σ.linObj X + θ * (σ.linObj Xb - σ.linObj X) := by
        simp only [Setting.linObj, Xθ, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
          Matrix.trace_smul, Finset.sum_add_distrib, smul_eq_mul, ← Finset.mul_sum]
        ring
      rw [← hlin, ← hobj]
      exact iInf₂_le (f := fun (p : σ.XRules × σ.SRules) (_ : p ∈ σ.feasMSPl) =>
        ((σ.ruleObj p.1 : ℝ) : EReal)) q hq
    exact ereal_limit _ _ _ key
  · unfold Setting.valMSPl
    apply le_iInf₂
    rintro ⟨x, s⟩ hp
    obtain ⟨hx, hs, hc⟩ := hp
    choose X hX using fun t => (lemma2_gen σ hσ hM t (x t) (hx t)).exists
    choose S hS using fun t => (lemma2_gen σ hσ hM t (s t) (hs t)).exists
    have hmem : (X, S) ∈ σ.feasLP46 := by
      intro t
      refine ⟨?_, fun i j => ?_⟩
      · have h47 := ((sec_4_eq_4_7_proof σ hσ t).1 x (s t) X (S t) hx (hs t) hX (hS t)).mp
          (hc t).1
        exact ((sec_4_eq_4_7_proof σ hσ t).2 X (S t)).mp h47
      · show 0 ≤ (σ.Wtilde * σ.M * (σ.Pt t)ᵀ * (S t)ᵀ) i j
        rw [cone_entry]
        have hrow : (S t * σ.Pt t * σ.M) j = fun b => ∫ ξ, s t (σ.tr t ξ) j * ξ b ∂σ.P := by
          rw [hS t]; rfl
        rw [hrow, Wtilde_moment σ hσ ((hs t).2.eval j) i]
        apply integral_nonneg_of_ae
        filter_upwards [ae_Wtilde_nonneg σ hσ, (hc t).2] with ξ h1 h2
        exact mul_nonneg (h2 j) (h1 i)
    rw [ruleObj_eq σ hσ x X hx hX]
    exact iInf₂_le (f := fun (p : σ.XFam × σ.SFam) (_ : p ∈ σ.feasLP46) =>
      ((σ.linObj p.1 : ℝ) : EReal)) (X, S) hmem

end PDLDRCommon


theorem solution (σ : PrimalDualLDR.Multistage.Setting) (hσ : σ.Standing) (hM : σ.LinearCondMean)
    (hsf : σ.StrictlyFeasible) (hW : 2 ≤ σ.k ∨ ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) :
    σ.valMSPl = σ.valLP46 :=
  PDLDRCommon.dual_main σ hσ hM hsf hW
