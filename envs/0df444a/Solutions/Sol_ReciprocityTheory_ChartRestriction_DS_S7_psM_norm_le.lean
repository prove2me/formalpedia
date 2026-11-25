-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psM_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:22.152071+00:00
-- url     : https://prove2.me/submissions/8c152ca8-aa9b-4d96-81fc-c95a5c8fd8b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_muK_univ_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_op_inv_eq_adjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_differentiableOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_phiM_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_posSet_subset_omega
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
private lemma dp_op_inv (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  exact op_inv_eq_adjoint T k
private lemma dpP_apply (T : KType ε Λ) (k : KG ε) (v : T.V) :
    dpP T k v = ⟪T.op k T.w, v⟫_ℂ • T.op k T.w := by
  show T.op k (projW T (T.op k⁻¹ v)) = _
  unfold projW
  rw [ContinuousLinearMap.smulRight_apply, map_smul, dp_op_inv]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right _ _ _
private lemma dp_inner_P (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ⟪v, dpP T k v⟫_ℂ = ((‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [dpP_apply, inner_smul_right, ← inner_conj_symm v (T.op k T.w)]
  first
  | (rw [RCLike.mul_conj]; rfl)
  | (rw [RCLike.mul_conj]; norm_cast)
  | (rw [RCLike.mul_conj]; push_cast; ring)
  | (rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
  | simp [RCLike.mul_conj]
private lemma dp_cont_P (T : KType ε Λ) : Continuous (dpP T) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hinv : Continuous fun k : KG ε => T.op k⁻¹ := hop.comp continuous_inv
  exact (hop.mul continuous_const).mul hinv
private lemma dp_integrable (T : KType ε Λ) {g : KG ε → ℝ} (hg : Continuous g) :
    Integrable (fun k => ((g k : ℝ) : ℂ) • dpP T k) (muK ε) := by
  haveI := compactSpace_KG ε
  have hf : Continuous (fun k => ((g k : ℝ) : ℂ) • dpP T k) :=
    (Complex.continuous_ofReal.comp hg).smul (dp_cont_P T)
  exact integrableOn_univ.mp (ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn)
private lemma dp_isPositive (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) {g : KG ε → ℝ} (hg : Continuous g)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)).IsPositive := by
  have hI := dp_integrable T hg

  have key : ∀ u v : T.V, ⟪u, (∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ =
      ∫ k, ((g k : ℝ) : ℂ) * ⟪u, dpP T k v⟫_ℂ ∂(muK ε) := by
    intro u v
    have hIv : Integrable (fun k => (((g k : ℝ) : ℂ) • dpP T k) v) (muK ε) :=
      (ContinuousLinearMap.apply ℂ T.V v).integrable_comp hI
    rw [ContinuousLinearMap.integral_apply hI, ← integral_inner hIv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

  have hsym : ∀ k (u v : T.V), ⟪dpP T k u, v⟫_ℂ = ⟪u, dpP T k v⟫_ℂ := by
    intro k u v
    rw [dpP_apply, dpP_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  refine ⟨?_, ?_⟩
  · intro u v
    change ⟪(((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) u, v⟫_ℂ =
      ⟪u, (((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ
    rw [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      ← inner_conj_symm _ v, key, key, ← integral_conj, Complex.conj_ofReal]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [map_mul, Complex.conj_ofReal, inner_conj_symm, hsym]
  · intro v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, ContinuousLinearMap.smul_apply,
      inner_smul_right, key]
    have e : ∫ k, ((g k : ℝ) : ℂ) * ⟪v, dpP T k v⟫_ℂ ∂(muK ε) =
        ((∫ k, g k * ‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
      first
      | rw [← integral_complex_ofReal]
      | rw [← integral_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [dp_inner_P]
      push_cast
      ring
    rw [e, ← Complex.ofReal_mul]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact mul_nonneg hc (integral_nonneg fun k => mul_nonneg (hg0 k) (sq_nonneg _))
private lemma dp_posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  have hinj : Function.Injective (toMK k).mulVec := by
    intro a b h
    have h2 := congrArg ((toMK k)ᴴ).mulVec h
    simpa [Matrix.mulVec_mulVec, (toMK_facts k).1] using h2
  rw [toMK_inv]
  exact hx.conjTranspose_mul_mul_same hinj
private lemma dp_cont_phi (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (fun k : KG ε => (PhiM μ (toMK k⁻¹ * x * toMK k)).re) := by
  have htoMK : Continuous (toMK : KG ε → Matrix (Fin n) (Fin n) ℂ) := by
    unfold toMK toM
    first
    | fun_prop
    | continuity
    | exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcont : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    ((htoMK.comp continuous_inv).mul continuous_const).mul htoMK
  have hmem : ∀ k : KG ε, toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    intro k
    first
    | exact posSet_subset_omega (dp_posDef_conj k hx)
    | exact posSet_subset_omega (by simpa [posSet] using dp_posDef_conj k hx)
  exact Complex.continuous_re.comp
    ((phiM_differentiableOn μ).continuousOn.comp_continuous hcont hmem)
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {B : ℝ}
    (hB : ∀ k : KG ε, (PhiM μ (toMK k⁻¹ * x * toMK k)).re ≤ B) : ‖psM T μ x‖ ≤ B := by
  set c : ℝ := (Module.finrank ℂ T.V : ℝ) / (muK ε Set.univ).toReal with hc_def
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (muK_univ_pos ε).le
  set g : KG ε → ℝ := fun k => (PhiM μ (toMK k⁻¹ * x * toMK k)).re with hg_def
  have hgc : Continuous g := dp_cont_phi μ hx
  have hg0 : ∀ k, 0 ≤ g k := fun k => (phiM_posDef μ (dp_posDef_conj k hx)).1.le
  have hPhi : ∀ k, PhiM μ (toMK k⁻¹ * x * toMK k) = ((g k : ℝ) : ℂ) := by
    intro k
    apply Complex.ext
    · simp [hg_def]
    · simp [(phiM_posDef μ (dp_posDef_conj k hx)).2]
  have hA : psM T μ x = ((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hPhi, dpP]
  have hone : (1 : T.V →L[ℂ] T.V) = ((c : ℝ) : ℂ) • ∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [← psM_one T μ]
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have h1 : toMK k⁻¹ * 1 * toMK k = 1 := by rw [Matrix.mul_one, toMK_inv, (toMK_facts k).1]
    simp only [h1, phiM_one, one_smul, dpP]
  have i1 := dp_integrable T (g := fun _ => (1 : ℝ)) continuous_const
  have i2 := dp_integrable T hgc
  have hlin : ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) =
      (B : ℂ) • (∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε)) -
        ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    have i1' : Integrable (fun k => (B : ℂ) • ((((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k)) (muK ε) :=
      i1.smul (B : ℂ)
    have e1 := integral_sub i1' i2
    rw [integral_smul] at e1
    refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans e1
    beta_reduce
    rw [smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring
  have hdiff : (B : ℂ) • (1 : T.V →L[ℂ] T.V) - psM T μ x =
      ((c : ℝ) : ℂ) • ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [hlin, smul_sub, smul_comm ((c : ℝ) : ℂ) (B : ℂ), ← hone, ← hA]
  have hpos1 := dp_isPositive T hc hgc hg0
  have hpos2 := dp_isPositive T hc (g := fun k => B - g k) (continuous_const.sub hgc)
    (fun k => sub_nonneg.mpr (hB k))
  have h0 : 0 ≤ psM T μ x := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, hA]
    exact hpos1
  have hle : psM T μ x ≤ (B : ℂ) • (1 : T.V →L[ℂ] T.V) := by
    rw [ContinuousLinearMap.le_def, hdiff]
    exact hpos2
  have hB0 : 0 ≤ B := (hg0 1).trans (hB 1)
  calc ‖psM T μ x‖ ≤ ‖(B : ℂ) • (1 : T.V →L[ℂ] T.V)‖ := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hle
    _ ≤ ‖(B : ℂ)‖ * ‖(1 : T.V →L[ℂ] T.V)‖ := norm_smul_le _ _
    _ ≤ B * 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hB0]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hB0
    _ = B := mul_one B
end ReciprocityTheory.ChartRestriction.DS.S7
