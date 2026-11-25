-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ShiftByUniformiser_proof_6c6707f798bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:48.688799+00:00
-- url     : https://prove2.me/submissions/32d0d4f2-13ae-4c83-92c2-4c6398946550

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalEqAddMulOfCycle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_cycle_853620e3c541
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_cycEval_eq_add_mul_of_fun_7c469d4a8c8a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_vecCons_zero_22688d6f4d59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_one_e110294ad3db


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
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ShiftByUniformiser
theorem _root_.solution (h₁ : DivCycleMul.Statement.{u})
    (h₂ : DivCycleFiniteSupport.Statement.{u}) : ShiftByUniformiser.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s _ hsP hH L n hI₁ hI₂
  have hfin : ∀ (Q : Ideal (MRing ι O)) (x : MRing ι O), (Function.support (divCycle Q x)).Finite :=
    fun Q x => h₂ O K ι Q x
  have hrat : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ((hfin Q x).union (hfin Q y)).subset fun W hW => by
      by_contra hc
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
      exact hW (by simp [ratDiv, hc.1, hc.2])

  have hpow : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ m : ℕ,
      ∀ W, divCycle Q (C ϖ ^ m * f) W = divCycle Q f W + m * divCycle Q (C ϖ) W := by
    intro Q hQ hϖQ hfQ m
    induction m with
    | zero => intro W; simp
    | succ m ih =>
      intro W
      have hm : C ϖ ^ m * f ∉ Q := fun h =>
        (hQ.mem_or_mem h).elim (fun h' => hϖQ (hQ.mem_of_pow_mem _ h')) hfQ
      have e : (C ϖ : MRing ι O) ^ (m + 1) * f = C ϖ * (C ϖ ^ m * f) := by ring
      rw [e, congrFun (h₁ O K ι Q (C ϖ) (C ϖ ^ m * f) hQ hϖQ hm) W, Pi.add_apply, ih W]
      push_cast
      ring
  have hshift : ∀ (Q : Ideal (MRing ι O)), Q.IsPrime → (C ϖ : MRing ι O) ∉ Q → f ∉ Q → ∀ W,
      ratDiv Q (C ϖ ^ n * f) g W = ratDiv Q f g W + (n : ℤ) * ratDiv Q (C ϖ) 1 W := by
    intro Q hQ hϖQ hfQ W
    simp only [ratDiv, divCycle_one, sub_zero]
    rw [hpow Q hQ hϖQ hfQ n W]
    ring
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  unfold cutIdentity at hI₁ hI₂ ⊢
  rw [cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat P f g) (hrat P (C ϖ) 1)
      (hshift P hPp hϖP hD.num_not_mem)] at hI₁
  classical
  have hR : cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ ^ n * f) g)) (divCycle P s) =
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s) +
      (n : ℤ) * cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons (0 : K → ℤ) L)
        else cycEval (fun G => vNum G L) (ratDiv W (C ϖ) 1)) (divCycle P s) := by
    refine cycEval_eq_add_mul_of_fun (n : ℤ) (hfin P s) fun W hW => ?_
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · simp only [if_pos hϖW, vNum_vecCons_zero]
      ring
    · simp only [if_neg hϖW]
      have hV := hH W hW hϖW
      have hWp : W.IsPrime := by
        unfold divCycle at hW
        split_ifs at hW with hm
        · exact hm.1.1.1
        · exact absurd rfl hW
      exact cycEval_eq_add_mul_of_cycle _ (n : ℤ) (hrat W f g) (hrat W (C ϖ) 1)
        (hshift W hWp hϖW hV.num_not_mem)
  rw [hR, hI₂] at hI₁
  linarith
end ShiftByUniformiser
end GroundTheory.Heights₂.Heights.NumbersDVR
