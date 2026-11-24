-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_LemmaA_proof_9dec2ef3e4c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:29.279615+00:00
-- url     : https://prove2.me/submissions/a5ce712f-3662-4ced-9562-25d45f948775

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaA
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockVandermonde_ne_zero_737fbd71d1a2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace LemmaA
theorem _root_.solution (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) (h3 : FlagDividedDifferencePoly.Statement)
    (h4 : FlagAntisymDecomposition.Statement) (h5 : FlagVandermondeHomogeneous.Statement)
    (h6 : FlagAntisymHomogeneous.Statement) (h7 : FlagQuotientHomogeneous.Statement)
    (h8 : FlagRestrictHomogeneous.Statement) (h9 : FlagRestrictSymmetric.Statement)
    (h10 : FlagRestrictDecomposition.Statement) (h11 : FlagPowerSumPreimage.Statement)
    (h12 : FlagRestrictConstantCoeff.Statement) (h13 : FlagIntegralViaQuotient.Statement) :
    LemmaA.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr N.factorial_ne_zero))
  · exact fun H hH => h1 f N H hH
  intro F Q hF k hk1 hkN τ G hG
  choose R hR hRsym using fun l σ => h3 f N (G * Q l σ)
  set P : RootRing f N := ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ
    with hPdef
  have hanti : antisymmetrize f N (G * F) = blockVandermonde f N * P := h4 f N F G Q R hF hR
  refine ⟨P, ?_, ?_, ?_⟩
  · have hΔ : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (RootRing f N) _)).mpr
        (Flag.blockVandermonde_ne_zero f N)
    rw [dividedDifference, hanti, map_mul, mul_div_cancel_left₀ _ hΔ]
  · intro hFh
    have hGF : (G * F).IsHomogeneous (topDegree f N + k) := by
      have := hG.mul hFh
      rwa [show k - 1 + (topDegree f N + 1) = topDegree f N + k by omega] at this
    have hA := h6 f N (G * F) _ hGF
    rw [hanti] at hA
    exact h8 f N τ P k (h7 _ _ _ _ _ (Flag.blockVandermonde_ne_zero f N) (h5 f N) hA)
  · obtain ⟨S, hS, hScoeff⟩ := h11 N (fun l => restrictToBlock f N τ (R l τ))
      (fun l => h9 f N τ (R l τ) (hRsym l τ))
    refine ⟨S, ?_, ?_⟩
    · rw [hS, hPdef, h10]
    · rw [hScoeff k hk1 hkN, h12, h13 f N _ _ (hR k τ)]
end LemmaA
end GroundTheory.Heights₂.Heights.RestTerms
