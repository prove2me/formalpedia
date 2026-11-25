-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegralReal_transfer_of_syzygy_46d401452df6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:35.94252+00:00
-- url     : https://prove2.me/submissions/a285ccda-330c-4b00-a9b4-b19d9cad4dd3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_1030665b7766
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_map_mul_301e0e18d5cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_coeffMap_sum_93079432c036
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_dual_flagIntegralReal_b52c6bfda3fc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegral_sub_smul_3d94798dc890
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_blockPowerSum_8334d045ed2f
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
namespace GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
theorem _root_.solution (f N j k : ℕ) (h : N = j + k) (F : RootRing f N)
    (Q₀ : ℕ → Fin f → RootRing f N) (hQ₀ : IsPowerSumDecomposition f N F Q₀)
    (Q' : Fin f → ℕ → IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hQ' : rootRingToReal f N j k h F =
      ∑ τ : Fin f, ∑ m ∈ Icc 1 (j + k), IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * Q' τ m)
    (m : ℕ) (τ : Fin f) (G : RootRing f N)
    (hS : ∀ S : ℕ → Fin f → RootRing f N, IsPowerSumDecomposition f N 0 S →
      flagIntegral f N (G * S m τ) = 0) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h G * Q' τ m) =
      (flagIntegral f N (G * Q₀ m τ) : ℝ) := by
  subst h
  have hid : (Prod.map id (finCongr (rfl : j + k = j + k)) : Fin f × Fin (j + k) → _) = id :=
    funext fun _ => rfl
  have hr : ∀ P : RootRing f (j + k), rootRingToReal f (j + k) j k rfl P = map (algebraMap ℚ ℝ) P :=
    fun P => by simp only [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, hid, rename_id_apply]
  have hp : ∀ m τ, IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ =
      map (algebraMap ℚ ℝ) (blockPowerSum f (j + k) m τ) := fun m τ => by
    rw [← hr, rootRingToReal_blockPowerSum]
  rw [hr] at hQ' ⊢
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  have e1 := congrArg (TermBoundEq.coeffMap φ) hQ'
  simp only [TermBoundEq.coeffMap_map, TermBoundEq.coeffMap_sum, hp,
    TermBoundEq.coeffMap_map_mul] at e1
  have h0 : IsPowerSumDecomposition f (j + k) 0
      (fun m τ => TermBoundEq.coeffMap φ (Q' τ m) - φ 1 • Q₀ m τ) := by
    unfold IsPowerSumDecomposition at hQ₀ ⊢
    simp only [mul_sub, mul_smul_comm, sum_sub_distrib, ← smul_sum]
    rw [← hQ₀, sum_comm, ← e1, sub_self]
  have hT := hS _ h0
  rw [mul_sub, mul_smul_comm, TermBoundEq.flagIntegral_sub_smul] at hT
  have hc : φ ((flagIntegral f (j + k) (G * Q₀ m τ) : ℚ) : ℝ) =
      flagIntegral f (j + k) (G * Q₀ m τ) * φ 1 := by
    rw [← mul_one ((flagIntegral f (j + k) (G * Q₀ m τ) : ℚ) : ℝ), ← Rat.smul_def, map_smul,
      smul_eq_mul]
  rw [map_sub, TermBoundEq.dual_flagIntegralReal, TermBoundEq.coeffMap_map_mul, hc]
  linarith
end GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
