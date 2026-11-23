-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psM_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:32.964799+00:00
-- url     : https://prove2.me/submissions/84cc5ba1-d8c9-4324-87e7-cf85b10c0be6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_muK_univ_pos

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
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
private lemma toMatrix_mul_alt (a b : KG ε) : toMK (a * b) = toMK a * toMK b := rfl
private lemma toMatrix_one_alt : toMK (1 : KG ε) = 1 := rfl
private lemma toMatrix_inv_mul (a : KG ε) : toMK a⁻¹ * toMK a = 1 := by
  rw [← toMatrix_mul_alt, inv_mul_cancel, toMatrix_one_alt]
private lemma toMatrix_mul_inv (a : KG ε) : toMK a * toMK a⁻¹ = 1 := by
  rw [← toMatrix_mul_alt, mul_inv_cancel, toMatrix_one_alt]
private lemma kType_schur_lemma (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : Module.End ℂ T.V)
  refine ⟨c, ?_⟩
  have key : ∀ k v, A (T.op k v) = T.op k (A v) := fun k v => by
    have := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c,
      ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
        Module.End.eigenspace (A : Module.End ℂ T.V) c := by
    intro k v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    change A (T.op k v) = c • T.op k v
    rw [key, show A v = c • v from hv, map_smul]
  rcases T.irred _ hinv with h | h
  · exfalso
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv1 : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [Module.End.mem_eigenspace_iff]
      exact hv.apply_eq_smul
    rw [h] at hv1
    exact hv.2 ((Submodule.mem_bot ℂ).1 hv1)
  · ext v
    have hv : v ∈ Module.End.eigenspace (A : Module.End ℂ T.V) c := by
      rw [h]
      exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa using hv
private lemma continuous_kType_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
private lemma continuous_conj_projection (T : KType ε Λ) :
    Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := ((continuous_kType_op T).mul continuous_const).mul ((continuous_kType_op T).comp continuous_inv)
end ReciprocityTheory.ChartRestriction.DS.S7
end
end

set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) : psM T μ 1 = 1 := by
  have hw : T.w ≠ 0 := fun h => by
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  haveI : Nontrivial T.V := ⟨⟨T.w, 0, hw⟩⟩
  haveI : CompactSpace (KG ε) := compactSpace_KG ε
  haveI : IsFiniteMeasureOnCompacts (muK ε) := by
    unfold muK
    infer_instance
  have hPhi1 : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    unfold PhiM
    refine Finset.prod_eq_one fun i _ => ?_
    unfold lead
    rw [dif_pos (by have := i.isLt; omega), Matrix.submatrix_one _ (Fin.castLE_injective _),
      Matrix.det_one, _root_.one_zpow]
  have hcomm : ∀ k : KG ε, T.op k * psM T μ 1 = psM T μ 1 * T.op k := by
    intro k
    have h := psM_conj T μ k 1
    rw [Matrix.mul_one, toMatrix_mul_inv] at h
    calc T.op k * psM T μ 1 = T.op k * psM T μ 1 * (T.op k⁻¹ * T.op k) := by
          rw [kType_op_inv_mul, mul_one]
      _ = T.op k * psM T μ 1 * T.op k⁻¹ * T.op k := by simp only [mul_assoc]
      _ = psM T μ 1 * T.op k := by rw [← h]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (psM T μ 1) hcomm
  obtain ⟨tr, htr⟩ : ∃ tr : (T.V →L[ℂ] T.V) →L[ℂ] ℂ,
      ∀ A, tr A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) :=
    ⟨LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)),
      fun A => rfl⟩
  have hP : LinearMap.trace ℂ T.V (projW T : T.V →ₗ[ℂ] T.V) = 1 := by
    have e2 : (projW T : T.V →ₗ[ℂ] T.V) =
        ((innerSL ℂ T.w : T.V →L[ℂ] ℂ) : T.V →ₗ[ℂ] ℂ).smulRight T.w := LinearMap.ext fun v => rfl
    rw [e2, LinearMap.trace_smulRight]
    simp [inner_self_eq_norm_sq_to_K, T.w_norm]
  have htrk : ∀ k, tr (T.op k * projW T * T.op k⁻¹) = 1 := by
    intro k
    rw [htr]
    have e1 : ((T.op k * projW T * T.op k⁻¹ : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V) =
        (ps2E T k).toLinearEquiv.conj (projW T : T.V →ₗ[ℂ] T.V) := LinearMap.ext fun v => rfl
    rw [e1, LinearMap.trace_conj', hP]
  have hint : Integrable (fun k : KG ε => T.op k * projW T * T.op k⁻¹) (muK ε) :=
    (continuous_conj_projection T).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have hv : ((muK ε Set.univ).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (muK_univ_pos ε).ne'
  have hd : (Module.finrank ℂ T.V : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h1 : tr (psM T μ 1) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [htr, hc]
    simp [LinearMap.trace_one]
  have hI : psM T μ 1 = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
      ∫ k, (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
    simp only [psM]
    congr 1
    congr 1
    funext k
    rw [Matrix.mul_one, toMatrix_inv_mul, hPhi1, one_smul]
  have h2 : tr (psM T μ 1) = (Module.finrank ℂ T.V : ℂ) := by
    rw [hI, map_smul, ← ContinuousLinearMap.integral_comp_comm tr hint]
    simp only [htrk, integral_const, smul_eq_mul, Complex.real_smul, mul_one]
    exact div_mul_cancel₀ _ hv
  have hc1 : c = 1 := by
    have := h1.symm.trans h2
    exact mul_right_cancel₀ hd (this.trans (one_mul _).symm)
  rw [hc, hc1, one_smul]
end ReciprocityTheory.ChartRestriction.DS.S7
