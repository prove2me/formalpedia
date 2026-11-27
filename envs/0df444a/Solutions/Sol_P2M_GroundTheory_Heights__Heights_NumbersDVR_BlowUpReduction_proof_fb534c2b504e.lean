-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpReduction_proof_fb534c2b504e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:53.760244+00:00
-- url     : https://prove2.me/submissions/664f70f6-e8e4-419f-b8e6-7b7acfdd10a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ExceptionalDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentityRightSide_congr_of_sub_mem_07359d1569a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cutIdentity_iff_b8b36a9a2a81
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpReduction
theorem _root_.solution (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  obtain ⟨hinvl, hinvr⟩ := hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L
  set Q := blowUpOf P (blowUpGens s g f m e)
  set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none
  set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)
  have hQ : Q.IsPrime := hmodel.multiProj.isPrime
  have hfmQ := hE.1.num_not_mem
  have hgYQ := hE.1.den_not_mem
  rw [map_mul] at hfmQ
  have hfQ : liftForm f ∉ Q := fun h => hfmQ (Q.mul_mem_right _ h)
  have hgQ : liftForm g ∉ Q := fun h => hgYQ (Q.mul_mem_right _ h)
  have hqQ : liftForm m * Y₁ ∉ Q := fun h =>
    (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem

  have hcfq := hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f)
    (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by
      obtain ⟨h₁, h₂⟩ := hH₁ H hH hϖH
      have hHp := isPrime_of_divCycle_ne_zero hH
      refine ⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h),
        fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩
      rw [map_mul]; exact H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)
  obtain ⟨haddl, haddr⟩ := hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _
    hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)
  have hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁) := by rw [map_mul]; ring
  have hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁) := by ring
  have hdeg : residualDeg e + exceptionalDeg b e = liftDeg b := by
    funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]
  rw [hnum, hden, hcfq.1] at haddl
  rw [hnum, hden, hdeg, hcfq.2] at haddr

  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hE.1.degrees
  have ht := htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb
    (liftDegs L)
  have hdegs : liftMDeg c + bg = bf + Pi.single none 1 := by
    funext o
    have h := congrFun hb o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; omega
    | some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; have := he k; omega
  have hl₁ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg
    (liftDegs L)
  have hl₂ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf
    (Pi.single none 1) (liftDegs L)
  rw [hdegs] at hl₁
  have hrel := cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m))
    (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)
  have hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁) := by rw [map_mul]; ring
  rw [hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem,
    hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P] at hrel
  rw [cutIdentity_iff] at hId₁ hId₀ ⊢
  rw [← hinvl, ← hinvr]
  linarith
end BlowUpReduction
end GroundTheory.Heights₂.Heights.NumbersDVR
