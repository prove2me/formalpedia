-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T18:02:28.445084+00:00
-- url     : https://prove2.me/submissions/66d6aded-dd35-4ba9-b363-df81e99e580d

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems
import Theorems.Thm_PrimalDualLDR_FixedRecourse_proposition_1

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

namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma KP_sub_K (σ : Setting) (hσ : σ.Standing) : σ.coneKP ⊆ σ.coneK := by
  rintro z ⟨s, -, hsL, hmom, hnn⟩ i
  have hz : z = fun l => ∫ ξ, s ξ * ξ l ∂σ.P := by funext l; exact (hmom l).symm
  show 0 ≤ σ.Wtilde i ⬝ᵥ z
  rw [hz, dot_moment σ hσ (hsL.integrable one_le_two)]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hnn, ae_mem_Xi σ hσ] with ξ h1 h2
  exact mul_nonneg h1 (Wt_on_Xi σ hσ h2 i)

lemma KP_combo (σ : Setting) (hσ : σ.Standing) {z w : Fin σ.k → ℝ} (hz : z ∈ σ.coneKP)
    (hw : w ∈ σ.coneKP) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a • z + b • w ∈ σ.coneKP := by
  obtain ⟨s, hsm, hsL, hsmom, hsnn⟩ := hz
  obtain ⟨r, hrm, hrL, hrmom, hrnn⟩ := hw
  refine ⟨fun ξ => a * s ξ + b * r ξ, (hsm.const_mul a).add (hrm.const_mul b),
    (hsL.const_mul a).add (hrL.const_mul b), fun j => ?_, ?_⟩
  · have i1 := integrable_mul_coord σ hσ (hsL.integrable one_le_two) j
    have i2 := integrable_mul_coord σ hσ (hrL.integrable one_le_two) j
    have : (fun ξ : Fin σ.k → ℝ => (a * s ξ + b * r ξ) * ξ j) =
        fun ξ => a * (s ξ * ξ j) + b * (r ξ * ξ j) := by funext ξ; ring
    rw [this, integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul,
      integral_const_mul, hsmom, hrmom]
    simp
  · filter_upwards [hsnn, hrnn] with ξ h1 h2
    positivity

lemma zero_mem_KP (σ : Setting) : (0 : Fin σ.k → ℝ) ∈ σ.coneKP :=
  ⟨fun _ => 0, measurable_const, MemLp.zero, fun j => by simp, Filter.Eventually.of_forall
    fun _ => le_rfl⟩

lemma dot_e1 (σ : Setting) (hσ : σ.Standing) (z : Fin σ.k → ℝ) (i : Fin σ.l)
    (hi : 2 ≤ i.val) : (σ.Wtilde *ᵥ z) i = σ.W i ⬝ᵥ z := by
  rw [Wt_mulVec, (hσ.2.2.2.2.2.1 i).2.2 hi, zero_mul, sub_zero]; rfl

lemma e1_nonneg_of_K (σ : Setting) (hσ : σ.Standing) (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0)
    {z : Fin σ.k → ℝ} (hz : z ∈ σ.coneK) : 0 ≤ e1 σ.k ⬝ᵥ z := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨R, hR⟩ := exists_bound σ hσ
  -- for every `ξ ∈ Ξ`, the direction `d = -(e1⬝z) ξ + z` is a recession direction, hence `0`
  have hd0 : ∀ ξ ∈ σ.Xi, -(e1 σ.k ⬝ᵥ z) • ξ + z = 0 := by
    intro ξ hξ
    set d := -(e1 σ.k ⬝ᵥ z) • ξ + z
    have hray : ∀ t : ℝ, 0 ≤ t → ξ + t • d ∈ σ.Xi := by
      intro t ht i
      have he1 : e1 σ.k ⬝ᵥ d = 0 := by
        simp only [d, dotProduct_add, dotProduct_smul, smul_eq_mul, e1_dot_on_Xi σ hσ hξ]; ring
      have hWd : ∀ i : Fin σ.l, 2 ≤ i.val → 0 ≤ σ.W i ⬝ᵥ d := by
        intro i hi
        have h1 : 0 ≤ σ.W i ⬝ᵥ ξ := by rw [← dot_e1 σ hσ ξ i hi]; exact Wt_on_Xi σ hσ hξ i
        have h2 : 0 ≤ σ.W i ⬝ᵥ z := by rw [← dot_e1 σ hσ z i hi]; exact hz i
        simp only [d, dotProduct_add, dotProduct_smul, smul_eq_mul]
        nlinarith
      have hrows := hσ.2.2.2.2.2.1 i
      show σ.h i ≤ σ.W i ⬝ᵥ (ξ + t • d)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hξi : σ.h i ≤ σ.W i ⬝ᵥ ξ := hξ i
      rcases Nat.lt_or_ge i.val 2 with hlt | hge
      · interval_cases hv : i.val
        · rw [(hrows.1 rfl).1, he1, mul_zero, add_zero]
          exact (hrows.1 rfl).1 ▸ hξi
        · rw [(hrows.2.1 rfl).1]
          simp only [neg_dotProduct, he1, neg_zero, mul_zero, add_zero]
          have := hξi; rw [(hrows.2.1 rfl).1, neg_dotProduct] at this; exact this
      · have := hWd i hge
        nlinarith
    by_contra hd
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
    set t := (R + ‖ξ‖ + 1) / ‖d‖
    have ht : 0 ≤ t := div_nonneg (by linarith [norm_nonneg ξ, (norm_nonneg ξ).trans (hR ξ hξ)])
      hdpos.le
    have h1 := hR _ (hray t ht)
    have h2 : ‖t • d‖ ≤ ‖ξ + t • d‖ + ‖ξ‖ := by
      have := norm_sub_le (ξ + t • d) ξ
      simpa using this
    rw [norm_smul, Real.norm_of_nonneg ht, div_mul_cancel₀ _ hdpos.ne'] at h2
    linarith
  -- hence every row `i ≥ 2` of `W` vanishes on `Ξ`
  obtain ⟨i, hi, hWi⟩ := hW
  apply hWi
  have hzero : ∀ ξ ∈ σ.Xi, σ.W i ⬝ᵥ ξ = 0 := by
    intro ξ hξ
    have h := congrArg (fun v => σ.W i ⬝ᵥ v) (hd0 ξ hξ)
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero] at h
    have h1 : 0 ≤ σ.W i ⬝ᵥ ξ := by rw [← dot_e1 σ hσ ξ i hi]; exact Wt_on_Xi σ hσ hξ i
    have h2 : 0 ≤ σ.W i ⬝ᵥ z := by rw [← dot_e1 σ hσ z i hi]; exact hz i
    nlinarith
  have hker : σ.Xi ⊆ (LinearMap.ker (dotProductBilin ℝ ℝ (σ.W i)) : Set _) := by
    intro ξ hξ; simpa using hzero ξ hξ
  have htop := Submodule.span_le.2 hker
  rw [hσ.2.2.2.2.2.2, top_le_iff] at htop
  have hvv : σ.W i ⬝ᵥ σ.W i = 0 := by
    have : σ.W i ∈ LinearMap.ker (dotProductBilin ℝ ℝ (σ.W i)) := by rw [htop]; trivial
    simpa using this
  exact dotProduct_self_eq_zero.1 hvv

end LDRAux

namespace LDRAux
open PrimalDualLDR.FixedRecourse

lemma KP_convex (σ : Setting) (hσ : σ.Standing) : Convex ℝ σ.coneKP :=
  fun _ hz _ hw _ _ ha hb _ => KP_combo σ hσ hz hw ha hb

lemma K_closed (σ : Setting) : IsClosed σ.coneK := by
  have : σ.coneK = ⋂ i, {z : Fin σ.k → ℝ | 0 ≤ (σ.Wtilde *ᵥ z) i} := by
    ext z; simp [Setting.coneK]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const
    ((continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id))

lemma K_sub_closure_KP (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) : σ.coneK ⊆ closure σ.coneKP := by
  intro z hz
  by_contra hzc
  obtain ⟨f, u, hfz, hfC⟩ :=
    geometric_hahn_banach_point_closed (KP_convex σ hσ).closure isClosed_closure hzc
  have hu : u < 0 := by simpa using hfC 0 (subset_closure (zero_mem_KP σ))
  have hfKP : ∀ b ∈ σ.coneKP, 0 ≤ f b := by
    intro b hb
    by_contra hneg
    rw [not_le] at hneg
    have ht : 0 ≤ u / f b := div_nonneg_of_nonpos hu.le hneg.le
    have hmem : (u / f b) • b ∈ σ.coneKP := by
      simpa using KP_combo σ hσ hb (zero_mem_KP σ) ht le_rfl
    have := hfC _ (subset_closure hmem)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  classical
  set π : Fin σ.k → ℝ := fun j => f (fun l => if j = l then 1 else 0)
  have hf : ∀ v, f v = π ⬝ᵥ v := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ v]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, π]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  -- `π ⬝ ξ ≥ 0` on `Ξ`
  have hπ : ∀ ξ ∈ σ.Xi, 0 ≤ π ⬝ᵥ ξ := by
    set N := {ξ : Fin σ.k → ℝ | π ⬝ᵥ ξ < 0}
    have hNo : IsOpen N := isOpen_lt (by fun_prop) continuous_const
    set s : (Fin σ.k → ℝ) → ℝ := N.indicator (fun _ => (1 : ℝ))
    have hsm : Measurable s := measurable_const.indicator hNo.measurableSet
    have hsL : MemLp s 2 σ.P := MemLp.of_bound hsm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ξ => by
        by_cases h : ξ ∈ N <;> simp [s, h])
    have hsi : Integrable s σ.P := hsL.integrable one_le_two
    have hmemKP : (fun j => ∫ ξ, s ξ * ξ j ∂σ.P) ∈ σ.coneKP :=
      ⟨s, hsm, hsL, fun j => rfl, Filter.Eventually.of_forall fun ξ => by
        by_cases h : ξ ∈ N <;> simp [s, h]⟩
    have h1 := hfKP _ hmemKP
    rw [hf, dot_moment σ hσ hsi] at h1
    have hle : ∀ ξ, s ξ * (π ⬝ᵥ ξ) ≤ 0 := by
      intro ξ
      by_cases h : ξ ∈ N
      · simp only [s, Set.indicator, h, if_true, one_mul]; exact (show π ⬝ᵥ ξ < 0 from h).le
      · simp [s, h]
    have hint : Integrable (fun ξ => s ξ * (π ⬝ᵥ ξ)) σ.P := by
      have : (fun ξ => s ξ * (π ⬝ᵥ ξ)) = fun ξ => ∑ l, π l * (s ξ * ξ l) := by
        funext ξ; simp only [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
      rw [this]
      exact integrable_finset_sum _ fun l _ => (integrable_mul_coord σ hσ hsi l).const_mul _
    have h0 : ∫ ξ, -(s ξ * (π ⬝ᵥ ξ)) ∂σ.P = 0 := by
      rw [integral_neg]
      have := integral_nonpos (μ := σ.P) hle
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg (fun ξ => neg_nonneg.2 (hle ξ)) hint.neg).1 h0
    refine Xi_subset_of_closed σ hσ {ξ | 0 ≤ π ⬝ᵥ ξ}
      (isClosed_le continuous_const (by fun_prop)) ?_
    filter_upwards [hae] with ξ hξ
    show 0 ≤ π ⬝ᵥ ξ
    by_contra hneg
    rw [not_le] at hneg
    have : ξ ∈ N := hneg
    simp [s, this] at hξ
    linarith
  obtain ⟨lam, hl0, hlW, hlh⟩ := (proposition_1 σ.W σ.h hσ.2.1 π).1 hπ
  have hfz' : 0 ≤ f z := by
    rw [hf, ← hlW, mulVec_transpose, ← dotProduct_mulVec]
    have he := e1_nonneg_of_K σ hσ hW hz
    have hrow : ∀ i, lam i * σ.h i * (e1 σ.k ⬝ᵥ z) ≤ lam i * (σ.W *ᵥ z) i := by
      intro i
      have h1 := Wt_mulVec σ z i
      have h2 : 0 ≤ (σ.Wtilde *ᵥ z) i := hz i
      have h3 : lam i * (σ.W *ᵥ z) i - lam i * σ.h i * (e1 σ.k ⬝ᵥ z) =
          lam i * (σ.Wtilde *ᵥ z) i := by rw [h1]; ring
      nlinarith [hl0 i, mul_nonneg (hl0 i) h2]
    have hsum : ∑ i, lam i * σ.h i * (e1 σ.k ⬝ᵥ z) ≤ lam ⬝ᵥ σ.W.mulVec z :=
      Finset.sum_le_sum fun i _ => hrow i
    have heq : ∑ i, lam i * σ.h i * (e1 σ.k ⬝ᵥ z) = (e1 σ.k ⬝ᵥ z) * (σ.h ⬝ᵥ lam) := by
      show _ = (e1 σ.k ⬝ᵥ z) * ∑ i, σ.h i * lam i
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    nlinarith [mul_nonneg he hlh]
  linarith

end LDRAux

open PrimalDualLDR.FixedRecourse LDRAux in
theorem solution (σ : Setting) (hσ : σ.Standing)
    (hW : ∃ i : Fin σ.l, 2 ≤ i.val ∧ σ.W i ≠ 0) :
    (interior σ.coneK).Nonempty ∧ interior σ.coneK ⊆ σ.coneKP ∧ σ.coneKP ⊆ σ.coneK := by
  have hsub := KP_sub_K σ hσ
  have hcl : closure σ.coneKP = σ.coneK :=
    subset_antisymm (closure_minimal hsub (K_closed σ)) (K_sub_closure_KP σ hσ hW)
  have hKconv : Convex ℝ σ.coneK := hcl ▸ (KP_convex σ hσ).closure
  have h0K : (0 : Fin σ.k → ℝ) ∈ σ.coneK := hsub (zero_mem_KP σ)
  have hXiK : σ.Xi ⊆ σ.coneK := fun ξ hξ i => Wt_on_Xi σ hσ hξ i
  have hspanK : affineSpan ℝ σ.coneK = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin σ.k → ℝ) (Fin σ.k → ℝ) ⟨0, h0K⟩,
      vectorSpan_def, eq_top_iff, ← hσ.2.2.2.2.2.2]
    apply Submodule.span_mono
    intro ξ hξ
    exact ⟨ξ, hXiK hξ, 0, h0K, by simp⟩
  have hintK : (interior σ.coneK).Nonempty := hKconv.interior_nonempty_iff_affineSpan_eq_top.2 hspanK
  have hspanKP : affineSpan ℝ σ.coneKP = ⊤ := by
    rw [eq_top_iff, ← hspanK]
    apply affineSpan_le.2
    rw [← hcl]
    exact closure_minimal (subset_affineSpan ℝ _)
      (AffineSubspace.closed_of_finiteDimensional _)
  have hintKP : (interior σ.coneKP).Nonempty :=
    (KP_convex σ hσ).interior_nonempty_iff_affineSpan_eq_top.2 hspanKP
  refine ⟨hintK, ?_, hsub⟩
  rw [← hcl, (KP_convex σ hσ).interior_closure_eq_interior_of_nonempty_interior hintKP]
  exact interior_subset
