-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.basicIdentity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:58.704647+00:00
-- url     : https://prove2.me/submissions/b1389358-7ade-4262-bc7d-f991d887c58b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportOfVanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_integral_re_double_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_hasCompactSupport_of_vanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_dTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_half_sum_norm_sub_sq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_hasCompactSupport_dTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_hasCompactSupport_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_norm_sum_sq_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_pair
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integrable_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.E
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    BasicIdentityStatement n M := by
  intro z hz ph f hph hf
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have hE : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph1
  have hEc : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hFc : ∀ j, Continuous (fun y => f y j) := fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hTc : ∀ j, Continuous (dTw n z ph j (fun y => f y j)) :=
    fun j => Ck.continuous n z hz 1 _ (ck_dTw n z 1 ph j _ hph (hf j).1)
  have hDc : ∀ j k, Continuous (db n z k (fun y => f y j)) :=
    fun j k => Ck.continuous n z hz 1 _ (Ck.db n z 1 k _ (hf j).1)
  have hLc : ∀ j k, Continuous (d n z j (db n z k (fun y => (ph y : ℂ)))) :=
    fun j k => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))
  have hcc : ∀ {g : M → ℂ}, Continuous g → Continuous (fun x => conj (g x)) :=
    fun hg => Complex.continuous_conj.comp hg

  set D : Fin n → Fin n → M → ℂ := fun j k x => dTw n z ph j (fun y => f y j) x *
    conj (dTw n z ph k (fun y => f y k) x) * (Real.exp (-ph x) : ℂ) with hD
  set L : Fin n → Fin n → M → ℂ := fun j k x => d n z j (db n z k (fun y => (ph y : ℂ))) x *
    f x j * conj (f x k) * (Real.exp (-ph x) : ℂ) with hL
  set C : Fin n → Fin n → M → ℂ := fun j k x => db n z k (fun y => f y j) x *
    conj (db n z j (fun y => f y k) x) * (Real.exp (-ph x) : ℂ) with hC
  set Q : Fin n → Fin n → M → ℂ := fun j k x => db n z k (fun y => f y j) x *
    conj (db n z k (fun y => f y j) x) * (Real.exp (-ph x) : ℂ) with hQ
  have iD : ∀ j k, Integrable (D j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hTc j).mul (hcc (hTc k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_dTw n z ph j _ (hf j).2) (fun x h0 => by simp [hD, h0])
  have iL : ∀ j k, Integrable (L j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact (((hLc j k).mul (hFc j)).mul (hcc (hFc k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _ (hf j).2 (fun x h0 => by simp [hL, h0])
  have iC : ∀ j k, Integrable (C j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hDc j k).mul (hcc (hDc k j))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_db n z k _ (hf j).2) (fun x h0 => by simp [hC, h0])
  have iQ : ∀ j k, Integrable (Q j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hDc j k).mul (hcc (hDc j k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_db n z k _ (hf j).2) (fun x h0 => by simp [hQ, h0])
  have iQC : ∀ j k, Integrable (fun x => Q j k x - C j k x) (vol n z) :=
    fun j k => (iQ j k).sub (iC j k)

  have pA : ∀ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) =
      (∑ j, ∑ k, D j k x).re := by
    intro x
    rw [norm_sum_sq_eq]
    simp only [hD, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have pL : ∀ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) =
      (∑ j, ∑ k, L j k x).re := by
    intro x
    simp only [Levi, hL, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have hnq : ∀ w : ℂ, ‖w‖ ^ 2 = (w * conj w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have pQ : ∀ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) =
      (∑ j, ∑ k, Q j k x).re := by
    intro x
    simp only [hQ, hnq, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have pS : ∀ x, sq2 n (sbar n z f x) * Real.exp (-ph x) =
      (∑ j, ∑ k, (Q j k x - C j k x)).re := by
    intro x
    have h := half_sum_norm_sub_sq (fun j k => db n z j (fun y => f y k) x)
    simp only at h
    unfold sq2 sbar
    rw [h]
    simp only [hQ, hC, hnq, Complex.re_sum, Complex.sub_re, Complex.re_mul_ofReal,
      Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  have hA := integral_re_double_sum (vol n z) n D iD
  have hLi := integral_re_double_sum (vol n z) n L iL
  have hQi := integral_re_double_sum (vol n z) n Q iQ
  have hSi := integral_re_double_sum (vol n z) n (fun j k x => Q j k x - C j k x) iQC
  have hpair : ∀ j k, ∫ x, D j k x ∂vol n z = (∫ x, L j k x ∂vol n z) + ∫ x, C j k x ∂vol n z :=
    fun j k => pair n z hz ph hph (fun y => f y j) (fun y => f y k) (hf j).1 (hf j).2
      (hf k).1 (hf k).2 j k
  have hsub : ∀ j k, ∫ x, (Q j k x - C j k x) ∂vol n z =
      (∫ x, Q j k x ∂vol n z) - ∫ x, C j k x ∂vol n z :=
    fun j k => integral_sub (iQ j k) (iC j k)
  rw [integral_congr_ae (Filter.Eventually.of_forall pA), integral_congr_ae (Filter.Eventually.of_forall pS),
    integral_congr_ae (Filter.Eventually.of_forall pL), integral_congr_ae (Filter.Eventually.of_forall pQ),
    hA, hLi, hQi, hSi]
  simp only [hpair, hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Complex.add_re,
    Complex.sub_re]
  ring
end ReciprocityTheory.L2DbarEstimates.E
