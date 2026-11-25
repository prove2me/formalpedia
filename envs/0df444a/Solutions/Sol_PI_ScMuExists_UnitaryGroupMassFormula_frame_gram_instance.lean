-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.frame_gram_instance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:01.162296+00:00
-- url     : https://prove2.me/submissions/39e8831f-fbee-4653-990c-e01ccfbf532b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_FrameGramInstance
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_gram_entry
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_rv_frame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution : InstFrameGram := by
  intro I r e f z hF v
  obtain ⟨hee, hff, hef, hz, hzz⟩ := rv_frame (I := I) hF v
  have hJH : (Formalism.REAL.Jm (I.ε v))ᴴ = Formalism.REAL.Jm (I.ε v) := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : I.ε v a <;> simp [h]
  have hH : ((instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z)ᴴ =
      (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.mul_assoc]
  have hent := gram_entry I v e f z
  generalize (instBmat I v e f z)ᴴ * Formalism.REAL.Jm (I.ε v) * instBmat I v e f z = G at hH hent ⊢
  have hS : ∀ j k, G j k = star (G k j) := by
    intro j k
    have hjk := congrFun (congrFun hH j) k
    rw [Matrix.conjTranspose_apply] at hjk
    exact hjk.symm
  have h1 : ∀ a b, G (Sum.inl a) (Sum.inl b) = 0 := fun a b => by rw [hent]; exact hee a b
  have h3 : ∀ a b, G (Sum.inl a) (Sum.inr (Sum.inl b)) = if a = b then 1 else 0 :=
    fun a b => by rw [hent]; exact hef a b
  have h4 : ∀ a (u : Unit), G (Sum.inl a) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).1
  have h5 : ∀ a (u : Unit), G (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr u)) = 0 :=
    fun a u => by rw [hent]; exact (hz a).2
  have h3' : ∀ a b, G (Sum.inr (Sum.inl a)) (Sum.inl b) = if b = a then 1 else 0 := by
    intro a b
    rw [hS, h3]
    split_ifs <;> simp
  have h4' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inl a) = 0 := by
    intro a u
    rw [hS, h4, star_zero]
  have h5' : ∀ a (u : Unit), G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inl a)) = 0 := by
    intro a u
    rw [hS, h5, star_zero]
  have h6 : ∀ u u' : Unit, G (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr u')) ≠ 0 := by
    intro u u'
    rw [hent]
    exact hzz
  have hker : ∀ w, G *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hf : ∀ a, w (Sum.inr (Sum.inl a)) = 0 := by
      intro a
      have := congrFun hw (Sum.inl a)
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h1, h3, h4] using this
    have he : ∀ a, w (Sum.inl a) = 0 := by
      intro a
      have := congrFun hw (Sum.inr (Sum.inl a))
      simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h3', h5, hf] using this
    have hzw : ∀ u : Unit, w (Sum.inr (Sum.inr u)) = 0 := by
      intro u
      have := congrFun hw (Sum.inr (Sum.inr u))
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, h4', h5', zero_mul,
        Finset.sum_const_zero, zero_add, Pi.zero_apply] at this
      rw [Fintype.sum_unique] at this
      rcases (mul_eq_zero.mp this) with h | h
      · exact absurd h (h6 _ _)
      · cases u
        exact h
    funext j
    rcases j with a | a | u
    · exact he a
    · exact hf a
    · exact hzw u
  refine Matrix.mulVec_injective_iff_isUnit.mp ?_
  intro w₁ w₂ h
  have h0 : G *ᵥ (w₁ - w₂) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (hker _ h0)
end PI.ScMuExists.UnitaryGroupMassFormula
