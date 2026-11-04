-- Prove2me | solution 1 for ThreeSum.LightBlockSourceStages.meets_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:00.594251+00:00
-- url     : https://prove2.me/submissions/8d8bf7aa-f582-4cfb-a606-48bc10d818f7

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Theorems.Thm_ThreeSum_LightBlockSourceStages_source_eq_right
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_endpointRight_abs_le
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_31257a44f822c74e
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets
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
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceStages
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags p hist base codes work cut maskBase U D : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrc : src+N ≤ hist) (hraw : raw+downsetCap (J*(512*h)) cut ≤ hist)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ hist)
    (hhist : hist+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceStages.space work (J*(512*h)) p U D (endpointBound h J) ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceStages.word N (J*(512*h)) p (modulus h J) U D (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [src,N,raw,flags,p,modulus h J,hist,base,codes,work,shift,J*(512*h),cut,maskBase,
        downsetCap (J*(512*h)) cut]
      μ (LightSourceStages.time N (J*(512*h)) cut p (modulus h J) U D (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν hist) := by
  have run := C.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw) (flags := flags)
    (p := p) (m := modulus h J) (hist := hist) (base := base) (codes := codes) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (U := U) (D := D)
    (E := endpointBound h J) (shift := shift)
    (fun S => endpointRight (outputOccurrences q) (unindexSet S))
    (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    hw hd hp (modulus_pos h J) hcut hsrc hraw hflags hhist hdata hmasks hcodes
    hspace hshift hword hvalues hrawRead
    (fun S _ => endpointRight_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega)
  rw [source_eq_right μ p shift B b q e hinput] at run
  exact run.mono le_rfl (fun _ _ h => ⟨h.1,h.2.2⟩)
end ThreeSum.LightBlockSourceStages
