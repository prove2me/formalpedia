-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpInvariance_proof_ab77533650ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:29.98936+00:00
-- url     : https://prove2.me/submissions/7ee2978b-2beb-40c1-9f56-bbb42e63b97e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_isMultiHomog_630b1c158ab9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_C_eq_4dac95f2f9a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_congr_on_support_d17f7ce7c14d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_ite_6e6e36b68b50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vecCons_liftMDeg_0832671ae59b

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
namespace BlowUpInvariance
theorem _root_.solution (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u}) :
    BlowUpInvariance.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e hce m hm hmP hmH L
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.1.degrees
  have hPp := hP.multiProj.isPrime

  have hdeg : bf + e = c + bg := by
    funext k
    have h1 := hce k
    have h2 := congrFun hb k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have hN : ∀ j, IsMultiHomog (blowUpGens s g f m e j) (c + bg) := by
    rintro (_ | _ | i)
    · exact hs.mul hg
    · exact hdeg ▸ hf.mul hm
    · exact hdeg ▸ hf.mul (powMonomial_isMultiHomog e i)
  have hfm : f * m ∉ P := fun h => (hPp.mem_or_mem h).elim hD.1.num_not_mem hmP
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [vecCons_liftMDeg]
    exact hdiv O ϖ hϖ K ι _ P (d + 1) hP b f g hD.1 _ _ hN ⟨some none, hfm⟩ _

  have hinv : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧
        v * blowUpGens s g f m e j' - w * blowUpGens s g f m e j ∈ P := by
    intro W hW hPW hrel hϖW
    choose i hi using hrel
    have hμ : powMonomial e i ∉ W := by
      rw [powMonomial, hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k (hW.mem_of_pow_mem _ hk)
    obtain ⟨u', v', hu', hv', h⟩ := hD.1.unit_off_special W hW hPW (fun k => ⟨i k, hi k⟩) hϖW
    refine ⟨some (some i), ?_⟩
    rintro (_ | _ | i')
    · refine ⟨v' * powMonomial e i, s * u', fun h' => (hW.mem_or_mem h').elim hv' hμ, ?_⟩
      have e1 : v' * powMonomial e i * (s * g) - s * u' * (f * powMonomial e i) =
          -(s * powMonomial e i) * (u' * f - v' * g) := by ring
      simpa only [blowUpGens, e1] using P.mul_mem_left _ h
    · exact ⟨powMonomial e i, m, hμ, by simp only [blowUpGens]; rw [show powMonomial e i * (f * m) -
        m * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩
    · exact ⟨powMonomial e i, powMonomial e i', hμ, by simp only [blowUpGens]; rw [show powMonomial e i *
        (f * powMonomial e i') - powMonomial e i' * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩

  obtain ⟨htrans, hpt⟩ := hhor O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ hinv c s hs hsP
  unfold cutIdentityRightSide
  rw [cycEval_ite _ _ _ _ (hfin O (Option K) (extIdx ι (BlowUpIdx ι)) (blowUpOf P (blowUpGens s g f m e))
    (liftForm s)), cycEval_ite _ _ _ _ (hfin O K ι P s)]
  congr 1
  · have hv := hvert O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ c s hs hsP (Matrix.vecCons b L)
    convert hv using 4
    congr 1
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  rw [← htrans (fun W => cycEval (fun G => vNum G L) (ratDiv W f g))]
  refine cycEval_congr_on_support _ fun W hW => ?_
  by_cases hϖ' : (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ W
  · simp only [if_pos hϖ']
  rw [if_neg hϖ', if_neg hϖ']
  obtain ⟨hWs, hWeq⟩ := hpt W hW hϖ'
  have hϖW : (C ϖ : MRing ι O) ∉ W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) := by
    rwa [Ideal.mem_comap, liftForm_C_eq]
  generalize W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) = V at hWs hWeq hϖW ⊢
  have hWm := hcomp O ϖ hϖ K ι P d hP c s hs hsP _ hWs hϖW
  have hWv := hsH _ hWs hϖW
  have hfmW : blowUpGens s g f m e (some none) ∉ V :=
    fun h => (hWm.multiProj.isPrime.mem_or_mem h).elim hWv.num_not_mem (hmH _ hWs hϖW)
  rw [hWeq ⟨_, hfmW⟩]
  exact hdiv O ϖ hϖ K ι _ _ d hWm b f g hWv _ _ hN ⟨_, hfmW⟩ L
end BlowUpInvariance
end GroundTheory.Heights₂.Heights.NumbersDVR
