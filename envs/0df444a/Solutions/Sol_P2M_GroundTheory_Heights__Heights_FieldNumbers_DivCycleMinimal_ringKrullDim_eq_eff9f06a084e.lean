-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_ringKrullDim_eq_eff9f06a084e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:06.916033+00:00
-- url     : https://prove2.me/submissions/17e2e58e-9019-4661-95bd-d0466afc3ab4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleMinimal
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_lt_top
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_lt_top_f6ad9b5ae3d3


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DivCycleMinimal
theorem _root_.solution {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type u} [Field F] (Q : Ideal (MRing ι F)) (m : ℕ)
    (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MRing ι F ⧸ Q) = d := by
    have h2 := PFContracted.ringKrullDim_lt_top Q
    cases hc : ringKrullDim (MRing ι F ⧸ Q) with
    | bot =>
      rw [relDim, hc] at h
      exact absurd h (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        rw [hc] at h2
        exact absurd h2 (by simp)
      | coe d => exact ⟨d, rfl⟩
  rw [PFContracted.relDim_eq_int hd, PFContracted.natCast_withBot_withTop] at h
  have h' : (d : ℤ) - Fintype.card K = m := by
    have := WithBot.coe_injective h
    exact_mod_cast WithTop.coe_injective this
  rw [hd]
  congr 1
  omega
end DivCycleMinimal
end GroundTheory.Heights₂.Heights.FieldNumbers
