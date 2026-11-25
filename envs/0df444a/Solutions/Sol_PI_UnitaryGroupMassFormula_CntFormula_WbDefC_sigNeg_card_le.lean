-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.WbDefC.sigNeg_card_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:44:24.554932+00:00
-- url     : https://prove2.me/submissions/c84cc783-fefc-4111-93cb-290da04917e8

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_MiscLemmasI_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_CTEqConjTranspose
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_WbDefC_cT_eq_conjTranspose
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_WbDefC_jpq_mulVec_of_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.WbDefC
namespace PI.UnitaryGroupMassFormula.CntFormula.WbDefC
theorem _root_.solution {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    (J : Matrix n n ℂ) (p q : ℕ) (hJ : Formalism.UG.HasSignature J p q) (u : ι → n → ℂ)
    (hu : LinearIndependent ℂ u)
    (hneg : ∀ d : ι → ℂ, (star (∑ a, d a • u a) ⬝ᵥ (J *ᵥ ∑ a, d a • u a)).re ≤ 0) :
    Fintype.card ι ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_eq_conjTranspose] at hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ
  set Qi : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  have key : ∀ v : n → ℂ, star v ⬝ᵥ (J *ᵥ v) =
      star (Qi *ᵥ (v ∘ e.symm)) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (Qi *ᵥ (v ∘ e.symm))) := by
    intro v
    have hv : Q *ᵥ (Qi *ᵥ (v ∘ e.symm)) = v ∘ e.symm := by
      rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    conv_rhs =>
      rw [← hP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, dotProduct_mulVec,
        ← Matrix.star_mulVec, hv, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    simp only [dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by simp [Function.comp_def])
  by_contra hlt
  push_neg at hlt
  let L : (ι → ℂ) →ₗ[ℂ] (Fin q → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ (Matrix.mulVecLin Qi) ∘ₗ
      (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Fintype.linearCombination ℂ u)
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hLd : L d = 0 := hdk
  have hyr : ∀ j, (Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm)) (Sum.inr j) = 0 := by
    intro j
    have := congrFun hLd j
    simp only [L, LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply] at this
    exact this
  have hform := hneg d
  rw [key, jpq_mulVec_of_inr _ hyr] at hform
  set y := Qi *ᵥ ((∑ a, d a • u a) ∘ e.symm) with hy
  have hnn : 0 ≤ star y ⬝ᵥ y := dotProduct_star_self_nonneg y
  have hz : star y ⬝ᵥ y = 0 := by
    rw [Complex.nonneg_iff] at hnn
    apply Complex.ext
    · simp only [Complex.zero_re]; linarith [hnn.1]
    · simpa using hnn.2.symm
  have hy0 : y = 0 := dotProduct_star_self_eq_zero.1 hz
  have hv0 : (∑ a, d a • u a) ∘ e.symm = 0 := by
    rw [← Matrix.one_mulVec ((∑ a, d a • u a) ∘ e.symm), ← hQQi, ← Matrix.mulVec_mulVec, ← hy, hy0,
      Matrix.mulVec_zero]
  have hsum : ∑ a, d a • u a = 0 := by
    funext x
    have := congrFun hv0 (e x)
    simpa using this
  exact hd0 (funext (Fintype.linearIndependent_iff.1 hu d hsum))
end PI.UnitaryGroupMassFormula.CntFormula.WbDefC
