-- Prove2me | solution 1 for ThreeSum.TernarySourceExecutionFactory.Seed.finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:36:32.707904+00:00
-- url     : https://prove2.me/submissions/17379bd5-204a-49ef-a8d2-63c59b01e0e7

import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceExecutionFactory
open Light LightSubsetAddress LightTernarySourceHost
namespace ThreeSum.TernarySourceExecutionFactory
namespace Seed
theorem _root_.solution {N : ℕ} {S : Setup} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {weight : ℕ→ℤ} {enumeration : ℕ→TernaryJointType.TritWord N}
    (H : Seed S lim d μ weight enumeration)
    (hread : ∀ i<S.NL, μ (S.weightBase+i)=weight i) :
    Ready S lim d μ weight enumeration where
  hxy := H.hxy
  hxz := H.hxz
  hw := H.hw
  hm := H.hm
  hbase0 := H.hbase0
  hnext0 := H.hnext0
  hbase1 := H.hbase1
  hnext1 := H.hnext1
  hbase2 := H.hbase2
  hinitEnd := H.hinitEnd
  hsrc := H.hsrc
  hweights := H.hweights
  hbank := H.hbank
  hpowerEnd := H.hpowerEnd
  hkeyBase := H.hkeyBase
  hkeyEnd := H.hkeyEnd
  hvalues := H.hvalues
  hb0 := H.hb0
  hb1 := H.hb1
  hb2 := H.hb2
  hw0 := H.hw0
  hw1 := H.hw1
  hw2 := H.hw2
  hM := H.hM
  hjoinWord := H.hjoinWord
  hlookupWord := H.hlookupWord
  hgroupWord := H.hgroupWord
  hgroupSpace := H.hgroupSpace
  hfactor := H.hfactor
  hweighted := H.hweighted
  hhistWord := H.hhistWord
  hinput := H.hinput
  hinputBound := H.hinputBound
  hweightBound := H.hweightBound
  hglobal := H.hglobal
  hcodes := H.hcodes
  hcodeBound := H.hcodeBound
  hpowers := H.hpowers
  hsorted := H.hsorted
  hwordCode := H.hwordCode
  hkey := H.hkey
  hgroupCode := H.hgroupCode
  hgroup := H.hgroup
  hL := H.hL
  hn := H.hn
  hd := H.hd
  hinjective := H.hinjective
  hfactorModel := H.hfactorModel
  hweightRead := hread
end Seed
end ThreeSum.TernarySourceExecutionFactory
