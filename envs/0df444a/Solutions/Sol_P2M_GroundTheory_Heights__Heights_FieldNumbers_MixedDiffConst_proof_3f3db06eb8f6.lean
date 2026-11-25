-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_proof_3f3db06eb8f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:45.292073+00:00
-- url     : https://prove2.me/submissions/1ea92842-320f-4c7c-b6ae-dff16601d1eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMixedDiffConst
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_eventuallyPoly_foldr_4f93c49a2cee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MixedDiffConst_foldr_polyStep_deg_e83696b637c9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open MixedDiffConst
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace MixedDiffConst
theorem _root_.solution (h1 : HilbDegreeBound.Statement.{u})
    (h2 : HilbEventuallyPoly.Statement.{u}) : MixedDiffConst.Statement.{u} := by
  intro F _ K _ _ ι _ I hI hrel n hn
  obtain ⟨p, hp⟩ := h2 F K ι I hI
  have hdeg : p.totalDegree ≤ n := by
    by_cases hp0 : p = 0
    · simp [hp0]
    · have := (h1 F K ι I hI).1 hrel p hp hp0
      rw [hn] at this
      exact_mod_cast this
  have key : ∀ (r : ℕ) (bs : Fin r → K → ℤ), n ≤ r → ∃ c : ℚ, (n < r → c = 0) ∧
      ∀ᶠ m in atTop, (mixedDiff bs (hilbFn I) m : ℚ) = c := by
    intro r bs hr
    have hE := eventuallyPoly_foldr (List.ofFn bs) hp
    rcases foldr_polyStep_deg (List.ofFn bs) p with h0 | hd
    · refine ⟨0, fun _ => rfl, ?_⟩
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, h0, map_zero]
    · rw [List.length_ofFn] at hd
      have hq0 : ((List.ofFn bs).foldr polyStep p).totalDegree = 0 := by omega
      refine ⟨coeff 0 ((List.ofFn bs).foldr polyStep p), fun hlt => by omega, ?_⟩
      rw [totalDegree_eq_zero_iff_eq_C] at hq0
      filter_upwards [hE] with m hm
      rw [mixedDiff, hm, hq0, eval_C, coeff_C, if_pos rfl]
  constructor
  · intro bs
    obtain ⟨c, -, hc⟩ := key n bs le_rfl
    obtain ⟨m0, hm0⟩ := hc.exists
    have hc' : ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = mixedDiff bs (hilbFn I) m0 :=
      hc.mono fun m hm => by exact_mod_cast hm.trans hm0.symm
    have hex : ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn I) m = c := ⟨_, hc'⟩
    have hval : intNum F I bs = mixedDiff bs (hilbFn I) m0 := by
      unfold intNum eventualValue
      rw [dif_pos hex]
      obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and hc').exists
      rw [← hm1, hm2]
    filter_upwards [hc'] with m hm
    rw [hm, hval]
  · intro r hr bs
    obtain ⟨c, hc0, hc⟩ := key r bs hr.le
    filter_upwards [hc] with m hm
    rw [hc0 hr] at hm
    exact_mod_cast hm
end MixedDiffConst
end GroundTheory.Heights₂.Heights.FieldNumbers
