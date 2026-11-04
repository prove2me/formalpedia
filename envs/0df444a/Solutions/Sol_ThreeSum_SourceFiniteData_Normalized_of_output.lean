-- Prove2me | solution 1 for ThreeSum.SourceFiniteData.Normalized.of_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:00:24.656378+00:00
-- url     : https://prove2.me/submissions/8ae4fd65-c539-43d2-9366-24080bef20df

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA
namespace ThreeSum.SourceFiniteData
namespace Normalized
theorem _root_.solution {μ : ℕ → ℤ} {av ae bv be cv ce tables rec vals g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r : ℤ}
    (H : LightBandRawAColor.Output μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC r) :
    ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
      (B : List ℤ) (hsB : B.Pairwise (· < ·)) (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := H
end Normalized
end ThreeSum.SourceFiniteData
