-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_res_mul_mem_pow_2beb75b9e3f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:07.373993+00:00
-- url     : https://prove2.me/submissions/849cc76c-987e-46cb-abbe-d045e5d7bc54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_mem_chartRing_of_mem_twistMod_zero_6486570dfc64

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
namespace SubSystem
theorem _root_.solution (H : SubSystem S x Ω) (I : Chart x) {m : ℕ} {a : Ω}
    (ha : a ∈ (H.pow m).sub I) (n : ℕ) {b : Ω} (hb : b ∈ (H.pow n).sub I) :
    a * b ∈ (H.pow (m + n)).sub I := by
  induction n generalizing b with
  | zero =>
    have hb' : b ∈ chartRing S x I := res_mem_chartRing_of_mem_twistMod_zero hb
    have := ((H.pow m).sub I).smul_mem ⟨b, hb'⟩ ha
    rw [chartRing_smul_def] at this
    rw [mul_comm]; exact this
  | succ n ih =>
    change b ∈ ((H.pow n).twist H).sub I at hb
    change a * b ∈ ((H.pow (m + n)).twist H).sub I
    refine Submodule.span_induction (p := fun z _ => a * z ∈ ((H.pow (m + n)).twist H).sub I)
      ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨q, hq, z, hz, rfl⟩
      refine Submodule.subset_span ⟨q, hq, a * z, ih hz, ?_⟩
      simp only [smul_eq_mul]; ring
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
    · intro c u _ hu
      rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
      exact Submodule.smul_mem _ c hu
end SubSystem
end GroundTheory.Heights₂.Heights.Kleiman
