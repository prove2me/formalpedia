-- Prove2me | solution 1 for ThreeSum.SourceFiniteData.Normalized.to_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:55:13.115974+00:00
-- url     : https://prove2.me/submissions/c3f93779-0c9c-4b6b-a0fd-ab37b8be5696

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceFiniteData

set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA
namespace ThreeSum.SourceFiniteData
namespace Normalized
theorem _root_.solution {μ : ℕ → ℤ} {av ae bv be cv ce tables rec vals g : ℕ} {hg : 0 < g}
    {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r) :
    LightBandRawAColor.Output μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC r :=
  ⟨A,hsA,B,hsB,C,hsC,H⟩
end Normalized
end ThreeSum.SourceFiniteData
