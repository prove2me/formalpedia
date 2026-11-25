-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.wIbp_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:09:22.238809+00:00
-- url     : https://prove2.me/submissions/ce37c029-bd65-43b3-b203-cd35454a4889

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_WIbpLeft
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_db_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_mul


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
theorem _root_.solution (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (k : Fin n) (a b : M → ℂ) (hph : CkR n z 1 ph) (ha : Ck n z 1 a) (hb : Ck n z 1 b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) :
    (∫ x, db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      -∫ x, a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hw : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph
  have hbc : Ck n z 1 (fun x => conj (b x)) := Ck.conj n z 1 b hb
  set g : M → ℂ := fun x => conj (b x) * (Real.exp (-ph x) : ℂ) with hgdef
  have hg : Ck n z 1 g := Ck.mul n z 1 _ _ hbc hw

  have hdg : ∀ x, a x * db n z k g x =
      a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) := by
    intro x
    have h1 := db_mul n z _ _ hbc hw k x
    beta_reduce at h1
    rw [hgdef, h1, db_conj n z b k x, db_expNeg n z ph hph k x, dTw, db_ofReal n z ph k x]
    simp only [map_sub, map_mul]
    ring
  have hL : (fun x => db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => db n z k a x * g x := by
    funext x
    simp only [hgdef]
    ring
  have hR : (fun x => a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => a x * db n z k g x := by
    funext x
    exact (hdg x).symm
  rw [hL, hR]
  rcases hc with hca | hcb
  · have h := integral_db_mul n z hz k g a hg ha hca
    have e1 : (fun x => db n z k a x * g x) = fun x => g x * db n z k a x := by
      funext x
      ring
    have e2 : (fun x => a x * db n z k g x) = fun x => db n z k g x * a x := by
      funext x
      ring
    rw [e1, e2, h, neg_neg]
  · have hgc : HasCompactSupport g :=
      (hcb.comp_left (map_zero (starRingEnd ℂ))).mul_right
    exact integral_db_mul n z hz k a g ha hg hgc
end ReciprocityTheory.L2DbarEstimates.E
