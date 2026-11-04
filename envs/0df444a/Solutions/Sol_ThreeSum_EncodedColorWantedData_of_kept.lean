-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedData.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:56:23.166669+00:00
-- url     : https://prove2.me/submissions/00f9e5cb-69c1-4704-8a85-cc07db5b1f1f

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
import Theorems.Thm_ThreeSum_EncodedColorWantedData_header_le_nextFree
import Theorems.Thm_Light_Seg_of_kept
import Theorems.Thm_ThreeSum_BandCandidateRows_cells_length
import Theorems.Thm_ThreeSum_BandRawA_Stored_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_00da40658bb1c003
import Definitions.Def_WeightedCache3SUM_Alias_7dc97c785b0d6c4c
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83
import Definitions.Def_WeightedCache3SUM_Alias_470e48753c64c7fc
import Theorems.Thm_ThreeSum_SourceBandBankLayout_At_of_kept
import Theorems.Thm_ThreeSum_SourceBandData_At_of_kept
import Definitions.Def_WeightedCache3SUM_Alias_78e5c19e1b3827d6
import Theorems.Thm_ThreeSum_WantedPairs_cells_length


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys
namespace ThreeSum.EncodedColorWantedData
theorem _root_.solution {μ ν : ℕ → ℤ} {out M NL NR bound : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift)
    (K : Kept μ ν bound) (hb : nextFree out M left right NL NR shift ≤ bound) :
    LightWantedSetup.Output ν out M left right NL NR shift := by
  have hh := (header_le_nextFree out M left right NL NR shift).trans hb
  obtain ⟨hcount,hpair,hnext,hshift,ps,hlen,hnodup,hmem,hrows⟩ := H
  refine ⟨(K _ (by omega)).trans hcount,(K _ (by omega)).trans hpair,
    (K _ (by omega)).trans hnext,(K _ (by omega)).trans hshift,ps,hlen,hnodup,hmem,?_⟩
  apply hrows.of_kept K
  rw [WantedPairs.cells_length,hlen]
  exact hb
end ThreeSum.EncodedColorWantedData
