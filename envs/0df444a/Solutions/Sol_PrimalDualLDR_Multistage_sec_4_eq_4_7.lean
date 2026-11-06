-- Prove2me | solution 1 for PrimalDualLDR.Multistage.sec_4_eq_4_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:18:33.411762+00:00
-- url     : https://prove2.me/submissions/48ece685-e7d0-4bd8-ac81-09a72ed021d0

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


theorem solution (σ : PrimalDualLDR.Multistage.Setting) (hσ : σ.Standing) (t : Fin σ.T) :
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
          ∑ r, σ.A t r * X r * σ.Pt r * σ.N t * σ.Pt t + S * σ.Pt t = σ.B t * σ.Pt t) :=
  PDLDRCommon.sec_4_eq_4_7_proof σ hσ t
