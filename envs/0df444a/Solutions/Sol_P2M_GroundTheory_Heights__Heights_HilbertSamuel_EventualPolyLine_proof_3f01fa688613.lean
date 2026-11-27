-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_proof_3f01fa688613
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:10.938346+00:00
-- url     : https://prove2.me/submissions/53958b27-5e9d-4028-9349-cdea6b434666

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_eval_lineRestrict_787614e7168c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_lineRestrict_natDegree_coeff_5a94aa2474ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_fwdDiff_iter_poly_f9e7acfe1226
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_mixedDiff_const_73044126e9c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_foldr_diffStep_replicate_c134cf47ff40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_EventualValueFacts_proof_11bc4474d04d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open EventualPolyLine
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace EventualPolyLine
theorem _root_.solution : EventualPolyLine.Statement := by
  intro K _ _ D f p a₀ a m hp hf
  obtain ⟨aQ, haQ⟩ : ∃ aQ : K → ℚ, aQ = fun k => (a k : ℚ) := ⟨_, rfl⟩
  have key : ∀ x : K → ℤ, (∀ k, (a₀ : ℤ) + D * |a k| ≤ x k) →
      ((mixedDiff (fun _ : Fin D => a) f x : ℤ) : ℚ) = (D.factorial : ℚ) * topCoeff D aQ p := by
    intro x hx
    obtain ⟨c, hc⟩ : ∃ c : K → ℚ, c = fun k => (((x - D • a) k : ℤ) : ℚ) := ⟨_, rfl⟩
    obtain ⟨hdeg, hcoeff⟩ := lineRestrict_natDegree_coeff D aQ c p hp
    rw [mixedDiff_const, foldr_diffStep_replicate, fwdDiff_iter_eq_sum_shift, ← hcoeff,
      ← fwdDiff_iter_poly D _ hdeg, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnn : ∀ k, (a₀ : ℤ) ≤ (x - D • a + j • a) k := by
      intro k
      have h1 := hx k
      have hj' : (j : ℤ) ≤ D := by exact_mod_cast hjD
      have hj0 : (0 : ℤ) ≤ j := by positivity
      simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      rcases abs_cases (a k) with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> nlinarith
    have hge : ∀ k, a₀ ≤ ((x - D • a + j • a) k).toNat := fun k => by have := hnn k; omega
    have hy : (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) = x - D • a + j • a :=
      funext fun k => Int.toNat_of_nonneg (by have := hnn k; omega)
    have hfy : f (x - D • a + j • a) = f (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) := by
      rw [hy]
    rw [smul_eq_mul, zsmul_eq_mul, Int.cast_mul, hfy, hf _ hge, eval_lineRestrict]
    congr 2
    congr 1
    funext k
    have e2 : ((((x - D • a + j • a) k).toNat : ℕ) : ℚ) = (((x - D • a + j • a) k : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := hnn k; omega)]
    rw [e2, hc, haQ]
    simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, zero_add, mul_one]
    push_cast
    ring
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, mixedDiff (fun _ : Fin D => a) f (fun k => (a₀ : ℤ) + D * |a k|) = c₀ :=
    ⟨_, rfl⟩
  have h₀ := key (fun k => (a₀ : ℤ) + D * |a k|) (fun k => le_rfl)
  rw [hc₀] at h₀
  have hev : ∀ᶠ x in Filter.atTop, mixedDiff (fun _ : Fin D => a) f x = c₀ := by
    refine Filter.eventually_atTop.2 ⟨fun k => (a₀ : ℤ) + D * |a k|, fun x hx => ?_⟩
    have h1 := key x (fun k => hx k)
    exact_mod_cast h1.trans h₀.symm
  have hEV := (EventualValueFacts.proof K _ c₀ 0).1 hev
  obtain ⟨hdeg, hcoeff⟩ := lineRestrict_natDegree_coeff D aQ (fun k => (m k : ℚ)) p hp
  refine ⟨(lineRestrict aQ (fun k => (m k : ℚ)) p).map (algebraMap ℚ ℝ), natDegree_map_le.trans hdeg, ?_, ?_⟩
  · have hD : (D.factorial : ℝ) ≠ 0 := by positivity
    rw [Polynomial.coeff_map, hcoeff, hEV, eq_ratCast, eq_div_iff hD,
      show ((c₀ : ℤ) : ℝ) = (((c₀ : ℤ) : ℚ) : ℝ) by norm_cast, h₀]
    push_cast
    ring
  · intro n
    rw [Polynomial.eval_natCast_map, eval_lineRestrict, eq_ratCast]
    congr 2
    congr 1
    funext k
    rw [haQ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
end EventualPolyLine
end GroundTheory.Heights₂.Heights.HilbertSamuel
