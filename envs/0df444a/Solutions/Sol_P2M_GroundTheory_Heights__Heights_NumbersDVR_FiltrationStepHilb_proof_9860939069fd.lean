-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_proof_9860939069fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:51.930305+00:00
-- url     : https://prove2.me/submissions/be922150-6931-4d9d-a852-e75052359924

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FiltrationStepHilb_finrank_step_0e1c7e28817d

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
namespace FiltrationStepHilb
theorem _root_.solution : FiltrationStepHilb.Statement.{u} := by
  intro F _ K _ _ ι _ L f s hL hf m
  by_cases hm : ∀ k, 0 ≤ m k
  · have key := FiltrationStepHilb.finrank_step L f s hL hf (fun k => (m k).toNat)
    have hms : (∀ k, 0 ≤ (m - fun k => (s k : ℤ)) k) ↔ s ≤ fun k => (m k).toNat := by
      constructor
      · intro h k
        have h1 := h k
        have h2 := hm k
        simp only [Pi.sub_apply] at h1
        show s k ≤ (m k).toNat
        omega
      · intro h k
        have h1 := h k
        have h2 := hm k
        simp only [Pi.sub_apply]
        change s k ≤ (m k).toNat at h1
        omega
    unfold hilbFn
    rw [if_pos hm, if_pos hm]
    by_cases hsn : s ≤ fun k => (m k).toNat
    · have hn : (fun k => ((m - fun k => (s k : ℤ)) k).toNat) = (fun k => (m k).toNat) - s := by
        funext k
        have h1 := hsn k
        have h2 := hm k
        change s k ≤ (m k).toNat at h1
        simp only [Pi.sub_apply]
        omega
      rw [if_pos (hms.mpr hsn), hn, key, if_pos hsn]
      push_cast
      rfl
    · rw [if_neg (fun h => hsn (hms.mp h)), key, if_neg hsn]
      simp
  · have hm' : ¬ ∀ k, 0 ≤ (m - fun k => (s k : ℤ)) k := fun h => hm fun k => by
      have h1 := h k
      simp only [Pi.sub_apply] at h1
      omega
    unfold hilbFn
    simp only [if_neg hm, if_neg hm']
    simp
end FiltrationStepHilb
end GroundTheory.Heights₂.Heights.NumbersDVR
