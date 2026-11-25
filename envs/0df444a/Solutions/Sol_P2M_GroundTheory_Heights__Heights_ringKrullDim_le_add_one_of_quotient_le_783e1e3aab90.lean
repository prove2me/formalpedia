-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ringKrullDim_le_add_one_of_quotient_le_783e1e3aab90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:45:43.660217+00:00
-- url     : https://prove2.me/submissions/96cc278e-8459-40ae-8e34-1464a388eb95

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimBounds
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_coheight_eq_ringKrullDim_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal
open scoped TensorProduct
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : Type} [CommRing B] [IsDomain B] (n : ℕ∞)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → ringKrullDim (B ⧸ Q) ≤ n) :
    ringKrullDim B ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
  let P0 : PrimeSpectrum B := ⟨⊥, Ideal.isPrime_bot⟩
  have hco : Order.coheight P0 ≤ n + 1 := by
    rw [Order.coheight_eq_iSup_gt_coheight]
    refine iSup₂_le fun Q hQ => ?_
    have hQ0 : Q.asIdeal ≠ ⊥ := by
      intro h0
      have : Q = P0 := PrimeSpectrum.ext h0
      rw [this] at hQ
      exact lt_irrefl _ hQ
    have h1 := h Q.asIdeal Q.isPrime hQ0
    rw [← GroundTheory.Arith.Abelian.Jacobian.coheight_eq_ringKrullDim_quotient] at h1
    have h2 : Order.coheight Q ≤ n := by exact_mod_cast h1
    exact add_le_add h2 le_rfl
  show Order.krullDim (PrimeSpectrum B) ≤ _
  rw [Order.krullDim_eq_iSup_coheight_of_nonempty]
  refine WithBot.coe_le_coe.mpr (iSup_le fun Q => ?_)
  have hle : P0 ≤ Q := by
    change (⊥ : Ideal B) ≤ Q.asIdeal
    exact bot_le
  exact (Order.coheight_anti hle).trans hco
end GroundTheory.Heights₂.Heights
