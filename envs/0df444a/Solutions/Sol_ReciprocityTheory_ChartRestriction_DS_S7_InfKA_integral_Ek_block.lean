-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.integral_Ek_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:42.301261+00:00
-- url     : https://prove2.me/submissions/23af07f7-f7b0-49b7-a8bf-ad2aa1ddc8d9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_Ek
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_integrable_of_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_integral_Ek_inK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_Ek_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution [CompactSpace (KG ε)] (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x.PosDef) (φ : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsBlock ε M) : ∫ k, Ek T μ x φ A M k ∂(muK ε) = 0 := by
  have key : ∀ X : Matrix (Fin n) (Fin n) ℂ, IsBlock ε X → Xᴴ = -X → inK ε X := by
    intro X hX hs
    have hc : X * Jm ε = Jm ε * X := by
      ext a b
      simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases h : ε a = ε b
      · rw [h]; ring
      · rw [hX a b h]; ring
    show inG ε X ∧ X * Jm ε = Jm ε * X
    refine ⟨?_, hc⟩
    show Xᴴ * Jm ε + Jm ε * X = 0
    rw [hs, Matrix.neg_mul, hc]
    abel
  have hMh : ∀ a b, ε a ≠ ε b → Mᴴ a b = 0 := fun a b h => by
    simp [Matrix.conjTranspose_apply, hM b a (Ne.symm h)]
  obtain ⟨P, Q, hP, hQ, rfl⟩ : ∃ P Q : Matrix (Fin n) (Fin n) ℂ,
      inK ε P ∧ inK ε Q ∧ M = P + Complex.I • Q := by
    refine ⟨(1 / 2 : ℂ) • (M - Mᴴ), (-Complex.I / 2) • (M + Mᴴ), key _ ?_ ?_, key _ ?_ ?_, ?_⟩
    · intro a b h
      first
      | simp only [Matrix.smul_apply, Matrix.sub_apply, hM a b h, hMh a b h, sub_zero, smul_zero]
      | simp [hM a b h, hMh a b h]
    · ext a b
      first
      | (simp [Matrix.conjTranspose_apply]; ring)
      | (simp [Matrix.conjTranspose_apply, Complex.star_def]; ring)
      | simp [Matrix.conjTranspose_apply]
      | simp [Matrix.conjTranspose_apply, Complex.star_def]
    · intro a b h
      first
      | simp only [Matrix.smul_apply, Matrix.add_apply, hM a b h, hMh a b h, add_zero, smul_zero]
      | simp [hM a b h, hMh a b h]
    · ext a b
      first
      | (simp [Matrix.conjTranspose_apply, Complex.star_def]; ring)
      | (simp [Matrix.conjTranspose_apply]; ring)
      | simp [Matrix.conjTranspose_apply, Complex.star_def]
      | simp [Matrix.conjTranspose_apply]
    · ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      linear_combination (M a b + Mᴴ a b) / 2 * Complex.I_sq
  have hIP : Integrable (Ek T μ x φ A P) (muK ε) := integrable_of_cont (continuous_Ek T μ hx φ A P)
  have hIQ : Integrable (fun k => Complex.I • Ek T μ x φ A Q k) (muK ε) :=
    (integrable_of_cont (continuous_Ek T μ hx φ A Q)).smul Complex.I
  simp_rw [Ek_decomp]
  rw [integral_add hIP hIQ, integral_smul, integral_Ek_inK T μ hx φ A hP, integral_Ek_inK T μ hx φ A hQ,
    smul_zero, add_zero]
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
