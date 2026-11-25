-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestCutCompare_proof_c95c9bdb9801
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:03.436788+00:00
-- url     : https://prove2.me/submissions/7c33bcfd-8138-4bc2-b567-998f8eccde51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompare_flagIntegral_sub_C_mul_389d5f87c2ed

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace RestCutCompare
theorem _root_.solution (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestCutStairHom.Statement) (h₃ : RestCutFlagKillsIdeal.Statement)
    (h₄ : RestCutIKillsIdeal.Statement) : RestCutCompare.Statement := by
  intro f j k N e I hI hs H hH
  have hN : N = j + k := by
    have := Fintype.card_congr e
    simpa using this
  have hD : flagDim f j k = RestTerms.topDegree f N := by
    subst hN
    rfl
  rw [hD] at hH
  obtain ⟨b, hb⟩ := h₁ f N H hH
  change H - C b * restStair f N ∈ restPsumIdeal f N at hb
  have hAh : (H - C b * restStair f N).IsHomogeneous (flagDim f j k) := by
    rw [hD]
    exact hH.sub ((h₂ f N).C_mul b)
  have hflag : RestTerms.flagIntegral f N H = b * RestTerms.flagIntegral f N (restStair f N) := by
    have h := h₃ f N _ hb
    rw [RestCutCompare.flagIntegral_sub_C_mul] at h
    linarith
  have hC : restTransport f j k N e (C b) = C (b : ℝ) := by
    simp [restTransport, restRename]
  have hIH : I (restTransport f j k N e H) =
      (b : ℝ) * I (restTransport f j k N e (restStair f N)) := by
    have h := h₄ f j k N e I hI _ hb hAh
    rw [map_sub, map_mul, hC, C_mul', map_sub, map_smul, smul_eq_mul] at h
    linarith
  have hs' : (RestTerms.flagIntegral f N (restStair f N) : ℝ) ≠ 0 := by exact_mod_cast hs
  unfold restCompareConst
  rw [hIH, hflag]
  push_cast
  field_simp
end RestCutCompare
end GroundTheory.Heights₂.Heights
