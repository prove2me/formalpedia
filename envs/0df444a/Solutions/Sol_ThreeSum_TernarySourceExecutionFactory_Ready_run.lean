-- Prove2me | solution 1 for ThreeSum.TernarySourceExecutionFactory.Ready.run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:59:35.436464+00:00
-- url     : https://prove2.me/submissions/9f08bbd1-eccc-4d07-999a-910119d4b08d

import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_source_receipt
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost
namespace ThreeSum.TernarySourceExecutionFactory
namespace Ready
theorem _root_.solution {N : ℕ} {S : Setup} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Ready S lim d μ weight enumeration) :
    Meets lim (LightTernarySourceHost.program S.xs S.ys S.zs) 34 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.base0 ∧ LightTernarySourceCountHost.BankReads
        ν S.valueBase S.groups S.bank (fun g r => S.values enumeration weight g (enumeration r))) := by
  have hs := LightTernarySourceHost.program_meets S.xs S.ys S.zs H.hxy H.hxz
    (base0 := S.base0)
    (dst0 := S.dst0)
    (base1 := S.base1)
    (dst1 := S.dst1)
    (base2 := S.base2)
    (dst2 := S.dst2)
    (p0 := S.p0)
    (p1 := S.p1)
    (p2 := S.p2)
    (U0 := S.U0)
    (U1 := S.U1)
    (U2 := S.U2)
    (J := S.J)
    (src := S.src)
    (NL := S.NL)
    (M := S.M)
    (free := S.free)
    (a := S.a)
    (bank := S.bank)
    (powers := S.powers)
    (W := S.W)
    (L := S.L)
    (keyBase := S.keyBase)
    (valueBase := S.valueBase)
    (weightBase := S.weightBase)
    (weightU := S.weightU)
    (factor := S.factor)
    (groups := S.groups)
    (U := S.U)
    (d := d) μ S.input weight S.codes S.key S.group
    H.hw H.hm H.hbase0 H.hnext0 H.hbase1 H.hnext1 H.hbase2 H.hinitEnd H.hsrc H.hweights H.hbank H.hpowerEnd H.hkeyBase H.hkeyEnd H.hvalues H.hb0 H.hb1 H.hb2 H.hw0 H.hw1 H.hw2 H.hM H.hjoinWord H.hlookupWord H.hgroupWord H.hgroupSpace H.hfactor H.hweighted H.hhistWord H.hinput H.hinputBound H.hweightRead H.hweightBound H.hglobal H.hcodes H.hcodeBound H.hpowers H.hsorted H.hwordCode H.hkey H.hgroupCode H.hgroup H.hL H.hn H.hd
  exact LightTernarySourceCountHost.source_receipt S.argv μ S.input
    (dictionary S.xs S.p0 S.J) enumeration S.key S.group weight
    H.hkey H.hinjective H.hfactorModel hs
end Ready
end ThreeSum.TernarySourceExecutionFactory
