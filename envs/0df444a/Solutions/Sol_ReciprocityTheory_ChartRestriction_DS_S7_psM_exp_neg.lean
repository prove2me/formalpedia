-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psM_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:07.864036+00:00
-- url     : https://prove2.me/submissions/ff530d22-d35a-48e8-8e3c-034dfdb62053

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_psM_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Jm_mul_self

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
private lemma toMatrix_signElement : toMK (ps2J ε) = Jm ε := rfl
private lemma signElement_inv : (ps2J ε)⁻¹ = ps2J ε := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * Jm ε = 1
  exact Jm_mul_self ε
private lemma signElement_central (k : KG ε) : ps2J ε * k = k * ps2J ε := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show Jm ε * toMK k = toMK k * Jm ε
  exact (show toMK k ∈ Kset ε from k.2).2.symm
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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    psM T μ (NormedSpace.exp (-X)) = psM T μ (NormedSpace.exp X) := by
  have hJ : Jm ε * X * Jm ε = -X := by
    calc Jm ε * X * Jm ε = Jm ε * (X * Jm ε) := Matrix.mul_assoc _ _ _
      _ = Jm ε * -(Jm ε * X) := by rw [hX.2]
      _ = -X := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv (Jm_mul_self ε)
  have hU : IsUnit (Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse (Jm_mul_self ε))
  have hE := Matrix.exp_conj (Jm ε) X hU
  rw [hinv, hJ] at hE
  have hE' : NormedSpace.exp (-X) = toMK (ps2J ε) * NormedSpace.exp X * toMK (ps2J ε)⁻¹ := by
    rw [signElement_inv, toMatrix_signElement]
    exact hE
  rw [hE', psM_conj]
  obtain ⟨c, hc⟩ := kType_schur_lemma T (T.op (ps2J ε)) (fun k => by
    rw [← kType_op_mul, ← kType_op_mul, signElement_central])
  have hm := kType_op_mul_inv T (ps2J ε)
  rw [hc] at hm ⊢
  calc c • (1 : T.V →L[ℂ] T.V) * psM T μ (NormedSpace.exp X) * T.op (ps2J ε)⁻¹ =
        psM T μ (NormedSpace.exp X) * (c • (1 : T.V →L[ℂ] T.V) * T.op (ps2J ε)⁻¹) := by
        simp only [smul_mul_assoc, one_mul, mul_smul_comm]
    _ = psM T μ (NormedSpace.exp X) := by rw [hm, mul_one]
end ReciprocityTheory.ChartRestriction.DS.S7
