-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.tStarPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:24:10.433442+00:00
-- url     : https://prove2.me/submissions/eca4c30b-4e89-41b2-95e9-6958388621b1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_TstarNormSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_cexp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_cexp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_cexp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_d_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
private theorem d_sub_of_ck_one (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y - g y) x = d n z j f x - d n z j g x := by
  have h := d_add n z (fun y => f y - g y) g (Ck.sub n z 1 f g hf hg) hg j x
  simp only [sub_add_cancel] at h
  rw [h]
  ring
end
end ReciprocityTheory.L2DbarEstimates.E
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] : TStarPointStatement n M := by
  intro z hz ph ψ f hph hψ hf x
  have hg : Ck n z 1 (fun y => (ψ y : ℂ) - (ph y : ℂ)) := Ck.sub n z 1 _ _ hψ hph
  have hE : Ck n z 1 (fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ))) := Ck.cexp n z 1 _ hg
  have hEfun : (fun y => (Real.exp (-(ph y - ψ y)) : ℂ)) =
      fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ)) := by
    funext y
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hdE : ∀ j, d n z j (fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ))) x =
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) *
        (d n z j (fun y => (ψ y : ℂ)) x - d n z j (fun y => (ph y : ℂ)) x) := by
    intro j
    rw [d_cexp n z _ hg j x, d_sub_of_ck_one n z _ _ hψ hph j x]
  have key : ∀ j, d n z j (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) x =
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) *
        (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x) := by
    intro j
    have hfun : (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) =
        fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ)) * f y j := by
      funext y
      rw [congrFun hEfun y]
    rw [hfun, d_mul n z _ _ hE (hf j) j x, hdE j]
    simp only [dTw]
    ring
  show (Real.exp (ψ x) : ℂ) * -((Real.exp (ph x - 2 * ψ x) : ℂ) *
      ∑ j, d n z j (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) x) = _
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have hexp : (Real.exp (ψ x) : ℂ) * (Real.exp (ph x - 2 * ψ x) : ℂ) *
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (-(∑ j, (dTw n z ph j (fun y => f y j) x +
    f x j * d n z j (fun y => (ψ y : ℂ)) x))) * hexp
end ReciprocityTheory.L2DbarEstimates.E
