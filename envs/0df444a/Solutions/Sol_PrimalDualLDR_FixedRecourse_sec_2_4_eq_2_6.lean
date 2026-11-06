-- Prove2me | solution 1 for PrimalDualLDR.FixedRecourse.sec_2_4_eq_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:52:28.610094+00:00
-- url     : https://prove2.me/submissions/373faff3-46cb-4e31-b4ec-466c0f2ef2c7

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting
import Definitions.Def_PrimalDualLDR_FixedRecourse_Problems

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

open PrimalDualLDR.FixedRecourse LDRAux in
theorem solution (σ : Setting) (hσ : σ.Standing) : σ.valSPl = σ.valLP26 := by
  have hU := (M_posDef_isUnit σ hσ).2
  have hdet : IsUnit σ.M.det := (Matrix.isUnit_iff_isUnit_det σ.M).1 hU
  have hinv : σ.M⁻¹ * σ.M = 1 := Matrix.nonsing_inv_mul σ.M hdet
  have hinv' : σ.M * σ.M⁻¹ = 1 := Matrix.mul_nonsing_inv σ.M hdet
  apply le_antisymm
  · -- every point of (2.6) gives a point of SP^l with the same value
    refine le_iInf₂ fun p hp => ?_
    obtain ⟨hAS, ⟨x, hx, hxM⟩, ⟨s, hs, hsM, hsnn⟩⟩ := hp
    have hmem : (x, s) ∈ σ.feasSPl := by
      refine ⟨hx, hs, fun i j => ?_, hsnn⟩
      rw [constr_eq σ hσ hx hs i j]
      have e1 : Matrix.of (fun a b => ∫ ξ, x ξ a * ξ b ∂σ.P) = p.1 * σ.M := by
        rw [hxM]; rfl
      have e2 : (∫ ξ, s ξ i * ξ j ∂σ.P) = (p.2 * σ.M) i j := by rw [hsM]
      rw [e1, e2, ← Matrix.mul_assoc, ← Matrix.add_apply, ← Matrix.add_mul, hAS, sub_self]
    have hobj : σ.ruleObj x = σ.linObj p.1 := by
      rw [ruleObj_eq σ hσ hx, linObj_eq, hxM]
    calc σ.valSPl ≤ ((σ.ruleObj x : ℝ) : EReal) :=
          iInf₂_le (f := fun q (_ : q ∈ σ.feasSPl) => ((σ.ruleObj q.1 : ℝ) : EReal)) (x, s) hmem
      _ = _ := by rw [hobj]
  · refine le_iInf₂ fun q hq => ?_
    obtain ⟨hx, hs, hcon, hsnn⟩ := hq
    set Ex : Matrix (Fin σ.n) (Fin σ.k) ℝ := Matrix.of (fun a b => ∫ ξ, q.1 ξ a * ξ b ∂σ.P)
      with hEx
    set Es : Matrix (Fin σ.m) (Fin σ.k) ℝ := Matrix.of (fun a b => ∫ ξ, q.2 ξ a * ξ b ∂σ.P)
      with hEs
    have hcon' : σ.A * Ex + Es = σ.B * σ.M := by
      ext i j
      have := hcon i j
      rw [constr_eq σ hσ hx hs i j] at this
      rw [Matrix.add_apply]
      have : (σ.A * Ex) i j + Es i j - (σ.B * σ.M) i j = 0 := this
      linarith
    have hXM : Ex * σ.M⁻¹ * σ.M = Ex := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    have hSM : Es * σ.M⁻¹ * σ.M = Es := by rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
    have hmem : (Ex * σ.M⁻¹, Es * σ.M⁻¹) ∈ σ.feasLP26 := by
      refine ⟨?_, ⟨q.1, hx, hXM⟩, ⟨q.2, hs, hSM, hsnn⟩⟩
      calc σ.A * (Ex * σ.M⁻¹) + Es * σ.M⁻¹ = (σ.A * Ex + Es) * σ.M⁻¹ := by
            rw [Matrix.add_mul, Matrix.mul_assoc]
        _ = σ.B := by rw [hcon', Matrix.mul_assoc, hinv', Matrix.mul_one]
    have hobj : σ.linObj (Ex * σ.M⁻¹) = σ.ruleObj q.1 := by
      rw [ruleObj_eq σ hσ hx, linObj_eq, hXM]; rfl
    show σ.valLP26 ≤ ((σ.ruleObj q.1 : ℝ) : EReal)
    rw [← hobj]
    clear_value Ex Es
    exact iInf₂_le (f := fun p (_ : p ∈ σ.feasLP26) => ((σ.linObj p.1 : ℝ) : EReal))
      (Ex * σ.M⁻¹, Es * σ.M⁻¹) hmem
