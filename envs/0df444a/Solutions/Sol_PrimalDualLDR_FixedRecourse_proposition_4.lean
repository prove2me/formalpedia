-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:56:53.69583+00:00
-- url     : https://prove2.me/submissions/f8fa808f-d5fd-4539-a439-bbaa7b643690

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems
import Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_3

open MeasureTheory Matrix

namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma ae_mem_Xi (σ : Setting) (hσ : σ.Standing) : ∀ᵐ ξ ∂σ.P, ξ ∈ σ.Xi :=
  mem_ae_iff.2 hσ.1.2.1

lemma Xi_subset_of_closed (σ : Setting) (hσ : σ.Standing) (C : Set (Fin σ.k → ℝ))
    (hC : IsClosed C) (hae : ∀ᵐ ξ ∂σ.P, ξ ∈ C) : σ.Xi ⊆ C := by
  intro ξ hξ
  by_contra hξC
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hC.isOpen_compl ξ hξC
  have h0 : σ.P Cᶜ = 0 := by
    rw [← mem_ae_iff]; exact hae
  have := hσ.1.2.2 ξ hξ ε hε
  exact absurd (measure_mono_null hball h0) this.ne'

lemma exists_bound (σ : Setting) (hσ : σ.Standing) : ∃ R : ℝ, ∀ ξ ∈ σ.Xi, ‖ξ‖ ≤ R :=
  isBounded_iff_forall_norm_le.1 hσ.2.2.1

lemma ae_norm_le (σ : Setting) (hσ : σ.Standing) : ∃ R : ℝ, ∀ᵐ ξ ∂σ.P, ‖ξ‖ ≤ R := by
  obtain ⟨R, hR⟩ := exists_bound σ hσ
  exact ⟨R, (ae_mem_Xi σ hσ).mono fun ξ hξ => hR ξ hξ⟩

lemma ae_coord_le (σ : Setting) (hσ : σ.Standing) : ∃ R : ℝ, ∀ᵐ ξ ∂σ.P, ∀ j, ‖ξ j‖ ≤ R := by
  obtain ⟨R, hR⟩ := ae_norm_le σ hσ
  exact ⟨R, hR.mono fun ξ hξ j => (norm_le_pi_norm ξ j).trans hξ⟩

/-- an integrable function times a coordinate is integrable -/
lemma integrable_mul_coord (σ : Setting) (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ}
    (hf : Integrable f σ.P) (j : Fin σ.k) : Integrable (fun ξ => f ξ * ξ j) σ.P := by
  obtain ⟨R, hR⟩ := ae_coord_le σ hσ
  exact hf.mul_bdd (continuous_apply j).aestronglyMeasurable (hR.mono fun ξ h => h j)

lemma integrable_coord (σ : Setting) (hσ : σ.Standing) (j : Fin σ.k) :
    Integrable (fun ξ : Fin σ.k → ℝ => ξ j) σ.P := by
  simpa using integrable_mul_coord σ hσ (integrable_const (1 : ℝ)) j

lemma integrable_coord_mul_coord (σ : Setting) (hσ : σ.Standing) (i j : Fin σ.k) :
    Integrable (fun ξ : Fin σ.k → ℝ => ξ i * ξ j) σ.P :=
  integrable_mul_coord σ hσ (integrable_coord σ hσ i) j

lemma M_symm (σ : Setting) : σ.Mᵀ = σ.M := by
  ext i j; simp only [transpose_apply, Setting.M, mul_comm]

end LDRAux
namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma rule_comp_integrable (σ : Setting) {n : ℕ} {x : (Fin σ.k → ℝ) → (Fin n → ℝ)}
    (hx : IsL2Rule σ.P x) (i : Fin n) : Integrable (fun ξ => x ξ i) σ.P :=
  integrable_pi_iff.1 (hx.2.integrable one_le_two) i

lemma rule_mul_coord_integrable (σ : Setting) (hσ : σ.Standing) {n : ℕ}
    {x : (Fin σ.k → ℝ) → (Fin n → ℝ)} (hx : IsL2Rule σ.P x) (i : Fin n) (j : Fin σ.k) :
    Integrable (fun ξ => x ξ i * ξ j) σ.P :=
  integrable_mul_coord σ hσ (rule_comp_integrable σ hx i) j

/-- the objective of a rule in terms of its first moments -/
lemma ruleObj_eq (σ : Setting) (hσ : σ.Standing) {x : (Fin σ.k → ℝ) → (Fin σ.n → ℝ)}
    (hx : IsL2Rule σ.P x) :
    σ.ruleObj x = ∑ i, ∑ j, σ.C i j * ∫ ξ, x ξ i * ξ j ∂σ.P := by
  unfold Setting.ruleObj
  have hpt : ∀ ξ, (σ.C.mulVec ξ) ⬝ᵥ x ξ = ∑ i, ∑ j, σ.C i j * (x ξ i * ξ j) := by
    intro ξ
    simp only [dotProduct, mulVec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  refine (integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    (rule_mul_coord_integrable σ hσ hx i j).const_mul (σ.C i j))).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (integral_finset_sum _ (fun j _ =>
    (rule_mul_coord_integrable σ hσ hx i j).const_mul (σ.C i j))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

lemma linObj_eq (σ : Setting) (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) :
    σ.linObj X = ∑ i, ∑ j, σ.C i j * (X * σ.M) i j := by
  unfold Setting.linObj
  rw [trace_mul_cycle, trace]
  simp only [diag, mul_apply, transpose_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm (_ : ℝ) _

/-- the moment constraint of `SP^l` in terms of first moments -/
lemma constr_eq (σ : Setting) (hσ : σ.Standing) {x : (Fin σ.k → ℝ) → (Fin σ.n → ℝ)}
    {s : (Fin σ.k → ℝ) → (Fin σ.m → ℝ)} (hx : IsL2Rule σ.P x) (hs : IsL2Rule σ.P s)
    (i : Fin σ.m) (j : Fin σ.k) :
    ∫ ξ, (σ.A.mulVec (x ξ) + s ξ - σ.B.mulVec ξ) i * ξ j ∂σ.P =
      (σ.A * Matrix.of (fun a b => ∫ ξ, x ξ a * ξ b ∂σ.P)) i j + (∫ ξ, s ξ i * ξ j ∂σ.P)
        - (σ.B * σ.M) i j := by
  have hpt : ∀ ξ, (σ.A.mulVec (x ξ) + s ξ - σ.B.mulVec ξ) i * ξ j =
      (∑ l, σ.A i l * (x ξ l * ξ j)) + s ξ i * ξ j - ∑ l, σ.B i l * (ξ l * ξ j) := by
    intro ξ
    simp only [Pi.add_apply, Pi.sub_apply, mulVec, dotProduct, sub_mul, add_mul,
      Finset.sum_mul]
    congr 1; congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hpt]
  have i1 : Integrable (fun ξ => ∑ l, σ.A i l * (x ξ l * ξ j)) σ.P :=
    integrable_finset_sum _ fun l _ => (rule_mul_coord_integrable σ hσ hx l j).const_mul _
  have i2 : Integrable (fun ξ => s ξ i * ξ j) σ.P := rule_mul_coord_integrable σ hσ hs i j
  have i3 : Integrable (fun ξ : Fin σ.k → ℝ => ∑ l, σ.B i l * (ξ l * ξ j)) σ.P :=
    integrable_finset_sum _ fun l _ => (integrable_coord_mul_coord σ hσ l j).const_mul _
  have e0 := integral_sub (i1.add i2) i3
  have e1 := integral_add i1 i2
  have e2 : ∫ ξ, ∑ l, σ.A i l * (x ξ l * ξ j) ∂σ.P = ∑ l, σ.A i l * ∫ ξ, x ξ l * ξ j ∂σ.P :=
    (integral_finset_sum _ fun l _ =>
      (rule_mul_coord_integrable σ hσ hx l j).const_mul (σ.A i l)).trans
      (Finset.sum_congr rfl fun l _ => integral_const_mul _ _)
  have e3 : ∫ ξ, ∑ l, σ.B i l * (ξ l * ξ j) ∂σ.P = ∑ l, σ.B i l * ∫ ξ, ξ l * ξ j ∂σ.P :=
    (integral_finset_sum _ fun l _ =>
      (integrable_coord_mul_coord σ hσ l j).const_mul (σ.B i l)).trans
      (Finset.sum_congr rfl fun l _ => integral_const_mul _ _)
  refine e0.trans ?_
  have r1 : (σ.A * Matrix.of (fun a b => ∫ ξ, x ξ a * ξ b ∂σ.P)) i j =
      ∑ l, σ.A i l * ∫ ξ, x ξ l * ξ j ∂σ.P := by simp [Matrix.mul_apply]
  have r2 : (σ.B * σ.M) i j = ∑ l, σ.B i l * ∫ ξ, ξ l * ξ j ∂σ.P := by
    simp [Matrix.mul_apply, Setting.M]
  show (∫ a, (∑ l, σ.A i l * (x a l * a j) + s a i * a j) ∂σ.P)
      - ∫ a, ∑ l, σ.B i l * (a l * a j) ∂σ.P = _
  rw [r1, r2]
  linear_combination e1 + e2 - e3

end LDRAux
namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma quad_eq (σ : Setting) (hσ : σ.Standing) (v : Fin σ.k → ℝ) :
    v ⬝ᵥ (σ.M *ᵥ v) = ∫ ξ, (v ⬝ᵥ ξ) ^ 2 ∂σ.P := by
  have hpt : ∀ ξ : Fin σ.k → ℝ, (v ⬝ᵥ ξ) ^ 2 = ∑ i, ∑ j, v i * (ξ i * ξ j) * v j := by
    intro ξ
    simp only [dotProduct, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ =>
    ((integrable_coord_mul_coord σ hσ i j).const_mul (v i)).mul_const (v j))]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ =>
    ((integrable_coord_mul_coord σ hσ i j).const_mul (v i)).mul_const (v j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, integral_const_mul]
  simp only [Setting.M]; ring

lemma M_posDef_isUnit (σ : Setting) (hσ : σ.Standing) : σ.M.PosDef ∧ IsUnit σ.M := by
  have hpd : σ.M.PosDef := by
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
    · ext i j; simp only [conjTranspose_apply, star_trivial, Setting.M, mul_comm]
    · rw [star_trivial, quad_eq σ hσ v]
      have hint : Integrable (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) σ.P := by
        have : (fun ξ : Fin σ.k → ℝ => (v ⬝ᵥ ξ) ^ 2) =
            fun ξ => ∑ i, ∑ j, v i * (ξ i * ξ j) * v j := by
          funext ξ
          simp only [dotProduct, sq, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        rw [this]
        exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
          ((integrable_coord_mul_coord σ hσ i j).const_mul (v i)).mul_const (v j)
      refine lt_of_le_of_ne (integral_nonneg fun ξ => sq_nonneg _) fun h0 => hv ?_
      have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => sq_nonneg _) hint).1 h0.symm
      have hsub : σ.Xi ⊆ {ξ | v ⬝ᵥ ξ = 0} := by
        refine Xi_subset_of_closed σ hσ _ (isClosed_eq (by fun_prop) continuous_const) ?_
        filter_upwards [hae] with ξ hξ
        simpa using hξ
      have hker : σ.Xi ⊆ (LinearMap.ker (dotProductBilin ℝ ℝ v) : Set _) := by
        intro ξ hξ
        simpa using hsub hξ
      have htop := Submodule.span_le.2 hker
      rw [hσ.2.2.2.2.2.2, top_le_iff] at htop
      have hvv : v ⬝ᵥ v = 0 := by
        have : v ∈ LinearMap.ker (dotProductBilin ℝ ℝ v) := by rw [htop]; trivial
        simpa using this
      exact dotProduct_self_eq_zero.1 hvv
  exact ⟨hpd, hpd.isUnit⟩

end LDRAux

namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma Wt_mulVec (σ : Setting) (ξ : Fin σ.k → ℝ) (i : Fin σ.l) :
    (σ.Wtilde *ᵥ ξ) i = (σ.W *ᵥ ξ) i - σ.h i * (e1 σ.k ⬝ᵥ ξ) := by
  simp only [Setting.Wtilde, sub_mulVec, vecMulVec_mulVec, Pi.sub_apply, Pi.smul_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

lemma e1_dot_on_Xi (σ : Setting) (hσ : σ.Standing) {ξ : Fin σ.k → ℝ} (hξ : ξ ∈ σ.Xi) :
    e1 σ.k ⬝ᵥ ξ = 1 := by
  obtain ⟨-, -, -, -, hl, hrows, -⟩ := hσ
  set i0 : Fin σ.l := ⟨0, by omega⟩
  set i1 : Fin σ.l := ⟨1, by omega⟩
  have h0 := hξ i0
  have h1 := hξ i1
  obtain ⟨hW0, hh0⟩ := (hrows i0).1 rfl
  obtain ⟨hW1, hh1⟩ := (hrows i1).2.1 rfl
  have e0 : (σ.W *ᵥ ξ) i0 = e1 σ.k ⬝ᵥ ξ := by
    show σ.W i0 ⬝ᵥ ξ = _; rw [hW0]
  have e1' : (σ.W *ᵥ ξ) i1 = -(e1 σ.k ⬝ᵥ ξ) := by
    show σ.W i1 ⬝ᵥ ξ = _; rw [hW1, neg_dotProduct]
  rw [e0, hh0] at h0
  rw [e1', hh1] at h1
  linarith

lemma Wt_on_Xi (σ : Setting) (hσ : σ.Standing) {ξ : Fin σ.k → ℝ} (hξ : ξ ∈ σ.Xi)
    (i : Fin σ.l) : 0 ≤ (σ.Wtilde *ᵥ ξ) i := by
  rw [Wt_mulVec, e1_dot_on_Xi σ hσ hξ, mul_one]
  exact sub_nonneg.2 (hξ i)

lemma rule_comp_memLp (σ : Setting) {n : ℕ} {x : (Fin σ.k → ℝ) → (Fin n → ℝ)}
    (hx : IsL2Rule σ.P x) (i : Fin n) : MemLp (fun ξ => x ξ i) 2 σ.P :=
  memLp_pi_iff.1 hx.2 i

lemma coord_memLp (σ : Setting) (hσ : σ.Standing) (j : Fin σ.k) :
    MemLp (fun ξ : Fin σ.k → ℝ => ξ j) 2 σ.P := by
  obtain ⟨R, hR⟩ := ae_coord_le σ hσ
  exact MemLp.of_bound (continuous_apply j).aestronglyMeasurable R (hR.mono fun ξ h => h j)

lemma linear_rule (σ : Setting) (hσ : σ.Standing) {n : ℕ} (X : Matrix (Fin n) (Fin σ.k) ℝ) :
    IsL2Rule σ.P (fun ξ => X *ᵥ ξ) := by
  refine ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, ?_⟩
  refine memLp_pi_iff.2 fun i => ?_
  have : (fun ξ : Fin σ.k → ℝ => (X *ᵥ ξ) i) = fun ξ => ∑ j, X i j * ξ j := by
    funext ξ; rfl
  rw [this]
  exact memLp_finsetSum _ fun j _ => (coord_memLp σ hσ j).const_mul _

lemma linear_rule_moment (σ : Setting) (hσ : σ.Standing) {n : ℕ}
    (X : Matrix (Fin n) (Fin σ.k) ℝ) :
    X * σ.M = fun i l => ∫ ξ, (X *ᵥ ξ) i * ξ l ∂σ.P := by
  funext i l
  have hpt : ∀ ξ : Fin σ.k → ℝ, (X *ᵥ ξ) i * ξ l = ∑ a, X i a * (ξ a * ξ l) := by
    intro ξ
    simp only [mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [hpt]
  refine Eq.trans ?_ (integral_finset_sum _ fun a _ =>
    (integrable_coord_mul_coord σ hσ a l).const_mul (X i a)).symm
  simp only [mul_apply, Setting.M]
  exact Finset.sum_congr rfl fun a _ => (integral_const_mul _ _).symm

/-- pairing a moment vector with `w` -/
lemma dot_moment (σ : Setting) (hσ : σ.Standing) {f : (Fin σ.k → ℝ) → ℝ}
    (hf : Integrable f σ.P) (w : Fin σ.k → ℝ) :
    w ⬝ᵥ (fun l => ∫ ξ, f ξ * ξ l ∂σ.P) = ∫ ξ, f ξ * (w ⬝ᵥ ξ) ∂σ.P := by
  have hpt : ∀ ξ : Fin σ.k → ℝ, f ξ * (w ⬝ᵥ ξ) = ∑ l, w l * (f ξ * ξ l) := by
    intro ξ
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [hpt]
  refine Eq.trans ?_ (integral_finset_sum _ fun l _ =>
    (integrable_mul_coord σ hσ hf l).const_mul (w l)).symm
  simp only [dotProduct]
  exact Finset.sum_congr rfl fun a _ => (integral_const_mul _ _).symm

lemma entry_eq (σ : Setting) (S : Matrix (Fin σ.m) (Fin σ.k) ℝ) (i : Fin σ.l) (j : Fin σ.m) :
    (σ.Wtilde * σ.M * Sᵀ) i j = σ.Wtilde i ⬝ᵥ (S * σ.M) j := by
  have h1 : σ.Wtilde * σ.M * Sᵀ = σ.Wtilde * (S * σ.M)ᵀ := by
    rw [transpose_mul, M_symm, Matrix.mul_assoc]
  rw [h1]
  simp only [mul_apply, transpose_apply, dotProduct]

lemma U_sub_interior (σ : Setting) :
    {z : Fin σ.k → ℝ | ∀ i, σ.Wtilde i ≠ 0 → 0 < σ.Wtilde i ⬝ᵥ z} ⊆ interior σ.coneK := by
  apply interior_maximal
  · intro z hz i
    show 0 ≤ σ.Wtilde i ⬝ᵥ z
    by_cases h : σ.Wtilde i = 0
    · rw [h, zero_dotProduct]
    · exact (hz i h).le
  · have : {z : Fin σ.k → ℝ | ∀ i, σ.Wtilde i ≠ 0 → 0 < σ.Wtilde i ⬝ᵥ z} =
        ⋂ i, {z | σ.Wtilde i ≠ 0 → 0 < σ.Wtilde i ⬝ᵥ z} := by
      ext z; simp
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases h : σ.Wtilde i = 0
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, forall_const]
      exact isOpen_lt continuous_const (by fun_prop)

end LDRAux

open PrimalDualLDR.FixedRecourse LDRAux in
theorem solution (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) (hsf : σ.StrictlyFeasible) :
    σ.valLP26 = σ.valLP28 := by
  obtain ⟨_, hint, hKPK⟩ := proposition_3 σ hσ hW
  have hU := (M_posDef_isUnit σ hσ).2
  have hdet : IsUnit σ.M.det := (Matrix.isUnit_iff_isUnit_det σ.M).1 hU
  have hinv : σ.M⁻¹ * σ.M = 1 := Matrix.nonsing_inv_mul σ.M hdet
  have hinv' : σ.M * σ.M⁻¹ = 1 := Matrix.mul_nonsing_inv σ.M hdet
  apply le_antisymm
  swap
  · -- (2.8) is a relaxation of (2.6), by `𝒦_P ⊆ 𝒦`
    refine le_iInf₂ fun p hp => ?_
    obtain ⟨hAS, -, ⟨s, hs, hsM, hsnn⟩⟩ := hp
    have hmem : p ∈ σ.feasLP28 := by
      refine ⟨hAS, fun i j => ?_⟩
      rw [entry_eq]
      have hz : (p.2 * σ.M) j ∈ σ.coneKP := by
        refine ⟨fun ξ => s ξ j, hs.1.eval, rule_comp_memLp σ hs j, fun l => ?_,
          hsnn.mono fun ξ h => h j⟩
        rw [hsM]
      exact hKPK hz i
    exact iInf₂_le (f := fun q (_ : q ∈ σ.feasLP28) => ((σ.linObj q.1 : ℝ) : EReal)) p hmem
  · -- strict feasibility of (2.8) and approximation from the strictly feasible side
    obtain ⟨ε, hε, xb, sb, hxb, hsb, hae⟩ := hsf
    set Ex : Matrix (Fin σ.n) (Fin σ.k) ℝ := Matrix.of (fun a b => ∫ ξ, xb ξ a * ξ b ∂σ.P)
    set Es : Matrix (Fin σ.m) (Fin σ.k) ℝ := Matrix.of (fun a b => ∫ ξ, sb ξ a * ξ b ∂σ.P)
    have hcon' : σ.A * Ex + Es = σ.B * σ.M := by
      ext i j
      have h0 : ∫ ξ, (σ.A.mulVec (xb ξ) + sb ξ - σ.B.mulVec ξ) i * ξ j ∂σ.P = 0 := by
        rw [integral_eq_zero_of_ae]
        filter_upwards [hae] with ξ hξ
        simp [hξ.1]
      rw [constr_eq σ hσ hxb hsb i j] at h0
      rw [Matrix.add_apply]
      have : (σ.A * Ex) i j + Es i j - (σ.B * σ.M) i j = 0 := h0
      linarith
    set Xb := Ex * σ.M⁻¹
    set Sb := Es * σ.M⁻¹
    have hSbM : Sb * σ.M = Es := by
      simp only [Sb]; rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    have hAb : σ.A * Xb + Sb = σ.B := by
      calc σ.A * Xb + Sb = (σ.A * Ex + Es) * σ.M⁻¹ := by
            simp only [Xb, Sb]; rw [Matrix.add_mul, Matrix.mul_assoc]
        _ = σ.B := by rw [hcon', Matrix.mul_assoc, hinv', Matrix.mul_one]
    -- strict positivity of the rows of `S̄ M` along nonzero rows of `W̃`
    have hstrict : ∀ i j, σ.Wtilde i ≠ 0 → 0 < σ.Wtilde i ⬝ᵥ (Sb * σ.M) j := by
      intro i j hi
      have hrow : (Sb * σ.M) j = fun l => ∫ ξ, sb ξ j * ξ l ∂σ.P := by
        rw [hSbM]; rfl
      rw [hrow, dot_moment σ hσ (rule_comp_integrable σ hsb j)]
      have hWi : Integrable (fun ξ : Fin σ.k → ℝ => σ.Wtilde i ⬝ᵥ ξ) σ.P := by
        have : (fun ξ : Fin σ.k → ℝ => σ.Wtilde i ⬝ᵥ ξ) =
            fun ξ => ∑ l, σ.Wtilde i l * ξ l := by funext ξ; rfl
        rw [this]
        exact integrable_finset_sum _ fun l _ => (integrable_coord σ hσ l).const_mul _
      have hnn : ∀ᵐ ξ ∂σ.P, 0 ≤ σ.Wtilde i ⬝ᵥ ξ :=
        (ae_mem_Xi σ hσ).mono fun ξ hξ => Wt_on_Xi σ hσ hξ i
      have hpos : 0 < ∫ ξ, σ.Wtilde i ⬝ᵥ ξ ∂σ.P := by
        refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) fun h0 => hi ?_
        have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hWi).1 h0.symm
        have hsub : σ.Xi ⊆ {ξ | σ.Wtilde i ⬝ᵥ ξ = 0} := by
          refine Xi_subset_of_closed σ hσ _ (isClosed_eq (by fun_prop) continuous_const) ?_
          filter_upwards [hz] with ξ hξ
          simpa using hξ
        have hker : σ.Xi ⊆ (LinearMap.ker (dotProductBilin ℝ ℝ (σ.Wtilde i)) : Set _) := by
          intro ξ hξ
          simpa using hsub hξ
        have htop := Submodule.span_le.2 hker
        rw [hσ.2.2.2.2.2.2, top_le_iff] at htop
        have hvv : σ.Wtilde i ⬝ᵥ σ.Wtilde i = 0 := by
          have : σ.Wtilde i ∈ LinearMap.ker (dotProductBilin ℝ ℝ (σ.Wtilde i)) := by
            rw [htop]; trivial
          simpa using this
        exact dotProduct_self_eq_zero.1 hvv
      have hle : ∫ ξ, ε * (σ.Wtilde i ⬝ᵥ ξ) ∂σ.P ≤ ∫ ξ, sb ξ j * (σ.Wtilde i ⬝ᵥ ξ) ∂σ.P := by
        refine integral_mono_ae (hWi.const_mul ε) ?_ ?_
        · have : (fun ξ => sb ξ j * (σ.Wtilde i ⬝ᵥ ξ)) =
              fun ξ => ∑ l, σ.Wtilde i l * (sb ξ j * ξ l) := by
            funext ξ; simp only [dotProduct, Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by ring
          rw [this]
          exact integrable_finset_sum _ fun l _ =>
            (rule_mul_coord_integrable σ hσ hsb j l).const_mul _
        · filter_upwards [hae, hnn] with ξ hξ hξn
          exact mul_le_mul_of_nonneg_right (hξ.2 j) hξn
      rw [integral_const_mul] at hle
      exact lt_of_lt_of_le (mul_pos hε hpos) hle
    -- approximation
    refine le_iInf₂ fun p hp => ?_
    obtain ⟨hAS, hp28⟩ := hp
    have happrox : ∀ t : ℝ, 0 < t → t ≤ 1 →
        σ.valLP26 ≤ ((σ.linObj ((1 - t) • p.1 + t • Xb) : ℝ) : EReal) := by
      intro t ht0 ht1
      set Xt := (1 - t) • p.1 + t • Xb
      set St := (1 - t) • p.2 + t • Sb
      have hrowK : ∀ j, (St * σ.M) j ∈ σ.coneKP := by
        intro j
        apply hint
        apply U_sub_interior
        intro i hi
        have : (St * σ.M) j = (1 - t) • (p.2 * σ.M) j + t • (Sb * σ.M) j := by
          funext l
          simp [St, Matrix.add_mul, Matrix.smul_mul]
        rw [this, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have h1 : 0 ≤ σ.Wtilde i ⬝ᵥ (p.2 * σ.M) j := by rw [← entry_eq]; exact hp28 i j
        have h2 := hstrict i j hi
        have : 0 ≤ 1 - t := by linarith
        nlinarith
      choose sj hsjm hsjL hsjmom hsjnn using hrowK
      have hmem : (Xt, St) ∈ σ.feasLP26 := by
        refine ⟨?_, ⟨fun ξ => Xt *ᵥ ξ, linear_rule σ hσ Xt, linear_rule_moment σ hσ Xt⟩,
          ⟨fun ξ j => sj j ξ, ⟨measurable_pi_lambda _ hsjm, memLp_pi_iff.2 hsjL⟩, ?_,
            ae_all_iff.2 hsjnn⟩⟩
        · calc σ.A * Xt + St = (1 - t) • (σ.A * p.1 + p.2) + t • (σ.A * Xb + Sb) := by
                simp only [Xt, St, Matrix.mul_add, Matrix.mul_smul]; module
            _ = σ.B := by rw [hAS, hAb]; module
        · funext j l
          exact (hsjmom j l).symm
      exact iInf₂_le (f := fun q (_ : q ∈ σ.feasLP26) => ((σ.linObj q.1 : ℝ) : EReal))
        (Xt, St) hmem
    have hlin : ∀ t : ℝ, σ.linObj ((1 - t) • p.1 + t • Xb) =
        σ.linObj p.1 + t * (σ.linObj Xb - σ.linObj p.1) := by
      intro t
      simp only [Setting.linObj, Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul,
        smul_eq_mul]
      ring
    show σ.valLP26 ≤ ((σ.linObj p.1 : ℝ) : EReal)
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
    have hr1' : σ.linObj p.1 < r := EReal.coe_lt_coe_iff.1 hr1
    set b := σ.linObj Xb - σ.linObj p.1
    set t : ℝ := min 1 ((r - σ.linObj p.1) / (|b| + 1))
    have hb1 : 0 < |b| + 1 := by positivity
    have hd : 0 < (r - σ.linObj p.1) / (|b| + 1) := div_pos (by linarith) hb1
    have ht0 : 0 < t := lt_min one_pos hd
    have ht1 : t ≤ 1 := min_le_left _ _
    have htb : t * b ≤ r - σ.linObj p.1 := by
      have h1 : t * b ≤ t * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) ht0.le
      have h2 : t * |b| ≤ t * (|b| + 1) := by nlinarith
      have h3 : t * (|b| + 1) ≤ (r - σ.linObj p.1) / (|b| + 1) * (|b| + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hb1.le
      rw [div_mul_cancel₀ _ hb1.ne'] at h3
      linarith
    calc σ.valLP26 ≤ ((σ.linObj ((1 - t) • p.1 + t • Xb) : ℝ) : EReal) := happrox t ht0 ht1
      _ ≤ (r : EReal) := by
          rw [hlin t]; exact EReal.coe_le_coe_iff.2 (by linarith)
      _ ≤ c := hr2.le
