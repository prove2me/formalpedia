-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorSearch.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:47:02.874498+00:00
-- url     : https://prove2.me/submissions/323ffe3b-6b2b-4583-9623-399cbfbc7201

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Theorems.Thm_ThreeSum_LightExtensionFactorSearch_result_flag
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightCoefficientDecode_program_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_Procs_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_time_mono
import Theorems.Thm_ThreeSum_LightExtensionFactorPredicate_word_mono
import Theorems.Thm_ThreeSum_LightPairSearch_meets
import Theorems.Thm_ThreeSum_LightPairSearch_program_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionFactorSearch._p2m_local_instance_9c16afeb32_9
namespace ThreeSum.LightExtensionFactorSearch
theorem _root_.solution (C : Layout) {ctx q depth : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+6<lim.depth)
    (hq : 0<q) (hp : 1<C.p) (he : 0<C.degree) (hed : C.degree<C.dim)
    (H : Seg μ ctx (header C)) (hctx : ctx+7≤C.left)
    (hpow : C.powers+(2*C.dim+1)≤C.left)
    (htarget : C.target+2*C.dim≤C.left) (hleft : C.left+2*C.dim≤C.right)
    (hspace : C.right+2*C.dim≤lim.space)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*C.dim, μ (C.target+i)=(f i : ℤ))
    (hword : (word C q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word) :
    Meets lim program 9 depth [q,ctx] μ
      (q*q*(time C q q+200)+100)
      (fun r ν => r=(LightPairSearch.first (LightPairSearch.goodCode q (good C f)) (q*q) : ℤ) ∧
        Kept μ ν C.left) := by
  let I := fun ν : ℕ → ℤ => Kept μ ν C.left
  apply LightPairSearch.program_meets LightExtensionFactorPredicate.program 0
    (good C f) I hq μ (fun _ _ => rfl) hsearchWord (by omega)
  intro u hu v hv ν hν
  have Hν : Seg ν ctx (header C) := by
    intro i hi
    have hi' : i<7 := by simpa [header] using hi
    exact (hν _ (by omega)).trans (H i hi)
  have hpowν (i : ℕ) (hi : i≤2*C.dim) : ν (C.powers+i)=((C.p^i : ℕ) : ℤ) :=
    (hν _ (by omega)).trans (hpowRead i hi)
  have hfν (i : ℕ) (hi : i<2*C.dim) : ν (C.target+i)=(f i : ℤ) :=
    (hν _ (by omega)).trans (hfRead i hi)
  have hwuv : (word C u v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (word_mono C hu.le hv.le)).trans hword
  have hc := LightExtensionFactorPredicate.procs.meets (depth := depth+2) C ν f hw (by omega)
    hp he hed Hν hctx hpow htarget hleft hspace hpowν hfν hwuv
  apply hc.mono (time_mono C hu.le hv.le)
  rintro r ξ ⟨hr,hkeep⟩
  refine ⟨hr.trans (result_flag C f u v),?_⟩
  intro a ha
  exact (hkeep a ha).trans (hν a ha)
end ThreeSum.LightExtensionFactorSearch
