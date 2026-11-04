-- Prove2me | solution 1 for ThreeSum.LightModuloCounts.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:44.619386+00:00
-- url     : https://prove2.me/submissions/3fb9b55b-6c68-4644-aa73-136a4cdaf32d

import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e


set_option autoImplicit false
open ThreeSum ThreeSum.LightModuloCounts
open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightModuloCounts
namespace Procs
theorem _root_.solution {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free) :=
  LightModuloCounts.meets C.main C.capacity C.hist C.residues C.emod C.histogram
    C.cyclic C.multiply C.lookup hw hp ha hb hc hnA hnB hnC hspace hword hd hA hB hC
end Procs
end ThreeSum.LightModuloCounts
