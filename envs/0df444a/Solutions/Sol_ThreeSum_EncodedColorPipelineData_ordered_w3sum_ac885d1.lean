-- Prove2me | solution 1 for ThreeSum.EncodedColorPipelineData.ordered_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:12:40.479291+00:00
-- url     : https://prove2.me/submissions/cbe3e76c-5f3b-4a69-a776-de37f579ac61

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_LightEncodedColorResult
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Theorems.Thm_ThreeSum_EncodedColorLayout_free_le_prime
import Theorems.Thm_ThreeSum_EncodedColorLayout_prime_le_cover
import Theorems.Thm_ThreeSum_EncodedColorWantedData_header_le_nextFree
import Theorems.Thm_ThreeSum_LightEncodedColorFiniteSources_free_le_base
import Theorems.Thm_ThreeSum_SourceFiniteData_source_ends


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPipelineData
open Light Scales BandScales ColorClassLists EncodedColorNormalizedData
attribute [local instance] ThreeSum.EncodedColorPipelineData._p2m_local_instance_be6b5e3d97_11
namespace ThreeSum.EncodedColorPipelineData
theorem _root_.solution (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    EncodedColorLayout.prime free n (bandSize n)+6 ≤ coverBase free n ∧
    free+8 ≤ coverBase free n ∧ coverBase free n ≤ controls free n A B C hsA hsB hsC ∧
    wantedHeader free n (incidences n A B C hsA hsB hsC).length+4 ≤ controls free n A B C hsA hsB hsC ∧
    controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC := by
  have hp := EncodedColorLayout.prime_le_cover free n (bandSize n) (radix n) (primeWindow n)
  have hf := EncodedColorLayout.free_le_prime free n (bandSize n)
  have hc := LightEncodedColorFiniteSources.free_le_base (coverBase free n) n
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (radix n) (incidences n A B C hsA hsB hsC)
  have hw := EncodedColorWantedData.header_le_nextFree
    (wantedHeader free n (incidences n A B C hsA hsB hsC).length) (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hs := SourceFiniteData.source_ends (controls free n A B C hsA hsB hsC) B.length C.length
    (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)
  change _ ≤ coverBase free n at hp
  change _ ≤ controls free n A B C hsA hsB hsC at hc hw
  change controls free n A B C hsA hsB hsC+3 ≤ finish free n A B C hsA hsB hsC ∧ _ ∧
    bankHeader free n A B C hsA hsB hsC+5 ≤ finish free n A B C hsA hsB hsC at hs
  exact ⟨hp,by omega,hc,hw,hs.1,hs.2.2⟩
end ThreeSum.EncodedColorPipelineData
