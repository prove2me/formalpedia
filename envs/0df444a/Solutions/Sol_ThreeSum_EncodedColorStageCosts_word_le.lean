-- Prove2me | solution 1 for ThreeSum.EncodedColorStageCosts.word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:21:00.052673+00:00
-- url     : https://prove2.me/submissions/5c72e8a6-cfd0-4ae5-9dab-02dd75863f50

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_EncodedColorStageCosts_source_word_mono
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_word_mono
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_word_mono
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono
import Theorems.Thm_ThreeSum_SourceBandBankLayout_word_mono
import Theorems.Thm_ThreeSum_SourceFiniteCosts_word_mono


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds
namespace ThreeSum.EncodedColorStageCosts
theorem _root_.solution {n p P M U len len' : ℕ} (hp : p ≤ P) (hlen : len ≤ len') :
    LightEncodedColorWantedSources.word n p M U len ≤ word n P M U len' :=
  max_le_max (EncodedColorWantedCosts.word_mono hp hlen) (source_word_mono hp)
end ThreeSum.EncodedColorStageCosts
