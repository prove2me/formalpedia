-- Prove2me | solution 1 for ThreeSum.LightBlockSourceHashes.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:14.017736+00:00
-- url     : https://prove2.me/submissions/2d8d2917-7646-4e3b-b7a4-ce270d043cb6

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_left
import Theorems.Thm_ThreeSum_BlockCoefficientRows_eval_right
import Theorems.Thm_ThreeSum_BlockCoefficientRows_mapRow_le
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_lt
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceHashes
theorem _root_.solution
    {μ : ℕ → ℤ} {h J occ maps coeff0 coeff1 masks rawLeft rawRight n work : ℕ}
    (o : BlockEncoding.Occurrences h J)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h)))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+2 ≤ lim.depth)
    (hspace : space work J (512*h) ≤ lim.space)
    (hocc : occ+J ≤ coeff0)
    (hmaps : maps+2*(512*h)*GlobalEncoding.scheduleSize h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(512*h) ≤ coeff1)
    (hc1 : coeff1+J*(512*h) ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work)
    (hword : (word J (512*h) (LocalCoverBounds.localPrime h)
      (LocalCoverBounds.localPrime h) : ℤ) ≤ lim.word)
    (hselRead : ∀ j < J, μ (occ+j) = (occurrenceIndices o j : ℤ))
    (hread0 : ∀ s < GlobalEncoding.scheduleSize h, ∀ i < 512*h,
      μ (maps+2*(512*h)*s+i) = (mapRow h false s i : ℤ))
    (hread1 : ∀ s < GlobalEncoding.scheduleSize h, ∀ i < 512*h,
      μ (maps+2*(512*h)*s+512*h+i) = (mapRow h true s i : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (SubsetAddress.subsetMask (BlockIndex.indexSet (sets i)) : ℤ)) :
    Meets lim program 0 d
      [J,512*h,LocalCoverBounds.localPrime h,occ,maps,coeff0,coeff1,masks,
        rawLeft,rawRight,n,work] μ (time J (512*h) n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = BlockEncoding.endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = BlockEncoding.endpointRight o (sets i)) ∧
        LightBlockCoefficients.Rows ν coeff0 coeff1 (512*h) (LocalCoverBounds.localPrime h)
          (occurrenceIndices o) (mapRow h false) (mapRow h true) J ∧
        Kept μ ν coeff0) := by
  have run := programProcs.meets (d := d) (μ := μ) (J := J) (L := 512*h)
    (p := LocalCoverBounds.localPrime h) (occ := occ) (maps := maps)
    (coeff0 := coeff0) (coeff1 := coeff1) (masks := masks) (rawLeft := rawLeft)
    (rawRight := rawRight) (n := n) (work := work) (U := LocalCoverBounds.localPrime h)
    (M := GlobalEncoding.scheduleSize h) (occurrenceIndices o)
    (fun i => SubsetAddress.subsetMask (BlockIndex.indexSet (sets i)))
    (mapRow h false) (mapRow h true) hw (LocalCoverBounds.localPrime_pos h)
    hd hspace hocc hmaps hmasks hc0 hc1 hleft hright hword
    (fun _ hj => occurrenceIndices_lt o hj) hselRead hread0 hread1
    (fun _ hs _ hi => mapRow_le false hs hi) (fun _ hs _ hi => mapRow_le true hs hi)
    hmaskRead (fun i _ => (SubsetAddress.subsetMask_isMask (BlockIndex.indexSet (sets i))).1)
  refine run.mono le_rfl ?_
  rintro r ν ⟨leftValues,rightValues,rows,kept⟩
  exact ⟨fun i hi => (leftValues i hi).trans (eval_left o (sets i)),
    fun i hi => (rightValues i hi).trans (eval_right o (sets i)),rows,kept⟩
end ThreeSum.LightBlockSourceHashes
