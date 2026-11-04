-- Prove2me | solution 1 for ThreeSum.BandCandidateRows.fromOwner_sound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:38.642193+00:00
-- url     : https://prove2.me/submissions/fd9348f8-c8a2-4b40-b046-93ef1d0ff9e0

import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Theorems.Thm_ThreeSum_BandCandidateRows_make_flag_one_iff
import Definitions.Def_WeightedCache3SUM_Alias_183fd7d896c180f9
import Theorems.Thm_ThreeSum_LightBandEnumeration_lookup_sound


set_option autoImplicit false
open ThreeSum ThreeSum.BandCandidateRows
open BandEnumeration
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
namespace ThreeSum.BandCandidateRows
theorem _root_.solution (A B C : Family) (o : Owner A B C)
    (hf : (fromOwner A B C o).flag=1) :
    let r := fromOwner A B C o
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩
  · have hp := (make_flag_one_iff .bc j.val k.val _).mp hf
    let r := LightBandLookup.result A.lower A.upper A.size (C.lower k-B.upper j)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound A (i := r-1) hr
    have hB := B.nonempty j j.isLt
    have hC := C.nonempty k k.isLt
    refine ⟨hs.1,j.isLt,k.isLt,?_⟩
    change A.lower (r-1) ≤ C.upper k-B.lower j ∧ C.lower k-B.upper j ≤ A.upper (r-1)
    omega
  · have hp := (make_flag_one_iff .ab i.val j.val _).mp hf
    let r := LightBandLookup.result C.lower C.upper C.size (A.lower i+B.lower j)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound C (i := r-1) hr
    have hA := A.nonempty i i.isLt
    have hB := B.nonempty j j.isLt
    refine ⟨i.isLt,j.isLt,hs.1,?_⟩
    change A.lower i ≤ C.upper (r-1)-B.lower j ∧ C.lower (r-1)-B.upper j ≤ A.upper i
    omega
  · have hp := (make_flag_one_iff .ac i.val k.val _).mp hf
    let r := LightBandLookup.result B.lower B.upper B.size (C.lower k-A.lower i)
    have hr : r=(r-1)+1 := by omega
    have hs := LightBandEnumeration.lookup_sound B (i := r-1) hr
    have hA := A.nonempty i i.isLt
    have hC := C.nonempty k k.isLt
    refine ⟨i.isLt,hs.1,k.isLt,?_⟩
    change A.lower i ≤ C.upper k-B.lower (r-1) ∧ C.lower k-B.upper (r-1) ≤ A.upper i
    omega
end ThreeSum.BandCandidateRows
