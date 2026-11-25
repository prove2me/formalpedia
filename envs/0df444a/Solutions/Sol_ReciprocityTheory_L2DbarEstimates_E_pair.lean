-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.E.pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:01.093125+00:00
-- url     : https://prove2.me/submissions/455e9eba-5e13-4360-a866-e2e07abd0733

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_WIbpLeft
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsBis
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_dTw
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_ck_expNeg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_comm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_wIbp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_wIbp_left
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
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
theorem _root_.solution (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : CkR n z 2 ph) (a b : M → ℂ) (ha : Ck n z 2 a) (_hac : HasCompactSupport a)
    (hb : Ck n z 2 b) (hbc : HasCompactSupport b) (j k : Fin n) :
    (∫ x, dTw n z ph j a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      (∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z) +
        ∫ x, db n z k a x * conj (db n z j b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have ha1 : Ck n z 1 a := Ck.mono n z 1 2 (by norm_num) a ha
  have hb1 : Ck n z 1 b := Ck.mono n z 1 2 (by norm_num) b hb
  have hE := ck_expNeg n z 1 ph hph1
  have hdTa : Ck n z 1 (dTw n z ph j a) := ck_dTw n z 1 ph j a hph ha
  have hdba : Ck n z 1 (db n z k a) := Ck.db n z 1 k a ha
  have s1 := wIbp_left n z hz ph k (dTw n z ph j a) b hph1 hdTa hb1 (Or.inr hbc)
  have s3 := ((wIbp n M) z hz ph j (db n z k a) b hph1 hdba hb1 (Or.inr hbc)).2
  have hcomm : ∀ x, db n z k (dTw n z ph j a) x = dTw n z ph j (db n z k a) x -
      d n z j (db n z k (fun y => (ph y : ℂ))) x * a x := by
    intro x
    have := comm n M z hz ph k j a x hph ha
    linear_combination -this
  have hcb : Continuous (fun x => conj (b x)) := Ck.continuous n z hz 1 _ (Ck.conj n z 1 b hb1)
  have hcE : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hint1 : Integrable (fun x => dTw n z ph j (db n z k a) x * conj (b x) *
      (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact ((Ck.continuous n z hz 0 _ (ck_dTw n z 0 ph j (db n z k a) hph1 hdba)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have hint2 : Integrable (fun x => d n z j (db n z k (fun y => (ph y : ℂ))) x * a x *
      conj (b x) * (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact (((Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))).mul
        (Ck.continuous n z hz 1 _ ha1)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have e2 : ∫ x, db n z k (dTw n z ph j a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z =
      (∫ x, dTw n z ph j (db n z k a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) -
        ∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z := by
    rw [← integral_sub hint1 hint2]
    congr 1
    funext x
    rw [hcomm x]
    ring
  rw [e2, s3] at s1
  linear_combination s1
end ReciprocityTheory.L2DbarEstimates.E
