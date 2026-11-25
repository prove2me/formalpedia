-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:27.294814+00:00
-- url     : https://prove2.me/submissions/451cd9a7-dd33-4cf5-8697-40cc6aabda43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_mem_form_fa180a587675
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_not_mem_6334cbda5c89
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (L : LineBundle S x) (hL : IsVeryAmple L.toSubSystem)
    {pp : Ideal (Poly S N)} {e : ℕ} (hW : IsSubvar x pp e) :
    ∃ s ∈ L.secs, ∃ I, s ∉ (L.twist (idealSys x pp)).sub I := by
  obtain ⟨r, h, hh⟩ := hL
  have := hW.isPrime
  obtain ⟨i, hi⟩ := hW.relevant
  have hxi : x i ≠ 0 := by
    intro h0
    exact hi (hW.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X S i)).mpr (by
      rw [aeval_X]; exact h0)))
  by_contra hcon
  push Not at hcon
  have hle : L.sub (singleChart hxi) ≤ idealMod pp (singleChart hxi) * L.sub (singleChart hxi) := by
    calc L.sub (singleChart hxi) = Submodule.span _ (Set.range h) := (hh.generates _).symm
      _ ≤ _ := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have := hcon (h j) (hh.mem_secs j) (singleChart hxi)
        rw [SubSystem.twist_sub_eq_mul_sub] at this
        exact this
  obtain ⟨P, hP⟩ := L.invertible (singleChart hxi)
  have h1 : (1 : Submodule (chartRing S x (singleChart hxi)) Ω) ≤ idealMod pp (singleChart hxi) := by
    calc (1 : Submodule (chartRing S x (singleChart hxi)) Ω) = L.sub (singleChart hxi) * P := hP.symm
      _ ≤ idealMod pp (singleChart hxi) * L.sub (singleChart hxi) * P := mul_le_mul' hle le_rfl
      _ = idealMod pp (singleChart hxi) := by rw [mul_assoc, hP, mul_one]
  obtain ⟨g, s, d, hg, hs, hgd, hsd, h1g⟩ := idealMod_mem_form pp _ (Submodule.one_le.mp h1)
  have hs0 := eval_ne_zero_of_mem_monos (singleChart hxi) hs
  rw [eq_div_iff hs0, one_mul] at h1g
  have hgs : g - s ∈ pp := hW.le ((mem_primeOf_of_isHomogeneous x (hgd.sub hsd)).mpr (by
    rw [map_sub, h1g, sub_self]))
  have hsp : s ∈ pp := by
    have := pp.sub_mem hg hgs
    rwa [sub_sub_cancel] at this
  refine monos_not_mem (pp := pp) (I := {i}) (fun j hj => ?_) hs hsp
  rw [Finset.mem_singleton.mp hj]
  exact hi
end GroundTheory.Heights₂.Heights.Kleiman
