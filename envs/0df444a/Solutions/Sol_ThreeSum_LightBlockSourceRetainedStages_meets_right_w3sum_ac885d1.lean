-- Prove2me | solution 1 for ThreeSum.LightBlockSourceRetainedStages.meets_right_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:26:21.76564+00:00
-- url     : https://prove2.me/submissions/172fc403-8ef6-4197-9d0f-5a2b85e579e4

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_histogram_le
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_source_eq_right
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_endpointRight_abs_le
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Theorems.Thm_ThreeSum_LightBlockSourceStages_source_eq_right
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
import Definitions.Def_WeightedCache3SUM_Alias_ce5ff1e60c39fd21
import Theorems.Thm_ThreeSum_LightSourceStages_Procs_meets
import Theorems.Thm_ThreeSum_LightSourceStages_ZetaProcs_meets
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Definitions.Def_WeightedCache3SUM_Alias_037fdff845f4735d
import Definitions.Def_WeightedCache3SUM_Alias_8a94481881de516b
import Definitions.Def_WeightedCache3SUM_Alias_c0e528b1e0cee255
import Definitions.Def_WeightedCache3SUM_Alias_44f02ed11cdb23f7
import Definitions.Def_WeightedCache3SUM_Alias_d110f06b53aa1a96
import Definitions.Def_WeightedCache3SUM_Alias_197272b1cee37ac5


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceRetainedStages
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hraw : raw+downsetCap (J*(512*h)) cut ≤ base)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ base)
    (htable : table+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ work)
    (hspace : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < modulus h J, μ (table+r) = (histogram p (modulus h J) shift v N r : ℤ))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [raw,flags,table,base,modulus h J,work,J*(512*h),cut,maskBase,downsetCap (J*(512*h)) cut]
      μ (LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν base) := by
  have run := C.meets (d := d) (μ := μ) (raw := raw) (flags := flags)
    (table := table) (base := base) (m := modulus h J) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (E := endpointBound h J) (B := N)
    (fun S => endpointRight (outputOccurrences q) (unindexSet S))
    (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    (histogram p (modulus h J) shift v N)
    hw hd (modulus_pos h J) hcut hraw hflags htable hdata hmasks hspace hword hrawRead
    (fun S _ => endpointRight_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega) hhistRead (fun r _ => histogram_le ..)
  rw [source_eq_right p shift B b q v e hinput] at run
  exact run
end ThreeSum.LightBlockSourceRetainedStages
