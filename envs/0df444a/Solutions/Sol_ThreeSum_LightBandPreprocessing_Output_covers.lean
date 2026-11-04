-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.Output.covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:45.855836+00:00
-- url     : https://prove2.me/submissions/e368f764-162e-4e94-93d9-8772377323b3

import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_Submission_ThreeSum_BandPreprocessingCorrectness
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_storedCount_eq
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_inBand_iff
import Theorems.Thm_ThreeSum_BandPartition_covers
import Theorems.Thm_ThreeSum_LightBandEnumeration_Tables_covers
import Theorems.Thm_ThreeSum_LightSortedBands_family_covers


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
namespace ThreeSum.LightBandPreprocessing
namespace Output
theorem _root_.solution {μ : ℕ → ℤ} {av ae bv be cv ce dst g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r x y z : ℤ}
    (h : Output μ av ae bv be cv ce dst g hg originalA originalB originalC r)
    (hx : x ∈ originalA) (hy : y ∈ originalB) (hz : z ∈ originalC) (heq : x+y=z) :
    ∃ i j k, InBand μ ae i x ∧ InBand μ be j y ∧ InBand μ ce k z ∧
      Candidate μ ae be ce dst i j k := by
  obtain ⟨A,hsA,B,hsB,C,hsC,_,hA,hB,hC,ht⟩ := h
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  obtain ⟨i,hi,hix,hxi⟩ := LightSortedBands.family_covers hg hsA hA.2.2.1 hx
  obtain ⟨j,hj,hjy,hyj⟩ := LightSortedBands.family_covers hg hsB hB.2.2.1 hy
  obtain ⟨k,hk,hkz,hzk⟩ := LightSortedBands.family_covers hg hsC hC.2.2.1 hz
  change aFamily.lower i ≤ x at hix
  change x ≤ aFamily.upper i at hxi
  change bFamily.lower j ≤ y at hjy
  change y ≤ bFamily.upper j at hyj
  change cFamily.lower k ≤ z at hkz
  change z ≤ cFamily.upper k at hzk
  have hr : BandEnumeration.relevant aFamily bFamily cFamily (⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩) := by
    change aFamily.lower i ≤ cFamily.upper k-bFamily.lower j ∧
      cFamily.lower k-bFamily.upper j ≤ aFamily.upper i
    exact ⟨by omega,by omega⟩
  have hcand := ht.covers (⟨i,hi⟩ : aFamily.Index) (⟨j,hj⟩ : bFamily.Index) (⟨k,hk⟩ : cFamily.Index) hr
  refine ⟨i,j,k,(hA.inBand_iff hi).mpr ⟨hix,hxi⟩,
    (hB.inBand_iff hj).mpr ⟨hjy,hyj⟩,(hC.inBand_iff hk).mpr ⟨hkz,hzk⟩,?_⟩
  unfold Candidate
  rw [hA.storedCount_eq,hB.storedCount_eq,hC.storedCount_eq]
  exact ⟨hi,hj,hk,hcand⟩
end Output
end ThreeSum.LightBandPreprocessing
