-- Prove2me | solution 1 for ThreeSum.LightBlockSourceBuild.meets_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:51.522928+00:00
-- url     : https://prove2.me/submissions/892435ff-cf82-4c01-8b1c-86e4fe5fe319

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_endpointRight_abs_le
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_right_value
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_244efc85702348f3
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightBlockSourceBuild
theorem _root_.solution {β : Type*} [DecidableEq β] {pMain : ℕ}
    (S : LightSourceBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags n p hist dst codes work U D : ℕ} {shift : ℤ}
    (o : Occurrences h J) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (e : Fin N ≃ C)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 0 < p)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+modulus h J ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceBuild.space work p U D (endpointBound h J) ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceBuild.word p (modulus h J) U D (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = c (e i))
    (hrawRead : ∀ i < n, μ (raw+i) = endpointRight o (sets i))
    (hflagRead : ∀ i < n, μ (flags+i) = (if RightAllowed o (sets i) then 1 else 0 : ℕ)) :
    Meets lim P pMain d [src,N,raw,flags,n,p,modulus h J,hist,dst,codes,work,shift]
      μ (LightSourceBuild.time N n p (modulus h J) U D (endpointBound h J))
      (fun _ ν => (∀ i < n, ν (dst+i) = (rightWeights o (p : ℤ) shift C c (sets i) : ℤ)) ∧
        Kept μ ν hist) := by
  have run := S.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw)
    (flags := flags) (n := n) (p := p) (m := modulus h J) (hist := hist) (dst := dst)
    (codes := codes) (work := work) (U := U) (D := D) (E := endpointBound h J) (shift := shift)
    (fun i => endpointRight o (sets i)) (fun i => if RightAllowed o (sets i) then 1 else 0)
    hw hd hp (modulus_pos h J) hsrc hraw hflags hhist hdst hcodes hspace hshift
    hword hvalues hrawRead (fun i _ => endpointRight_abs_le o (sets i)) hflagRead
    (fun i _ => by split <;> omega)
  refine run.mono le_rfl ?_
  rintro r ν ⟨out,_,kept⟩
  refine ⟨?_,kept⟩
  intro i hi
  rw [out i hi,right_value o p shift C c sets (fun j => μ (src+j)) e hinput i]
end ThreeSum.LightBlockSourceBuild
