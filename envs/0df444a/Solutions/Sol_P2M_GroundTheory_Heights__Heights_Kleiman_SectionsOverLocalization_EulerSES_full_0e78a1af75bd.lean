-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_full_0e78a1af75bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:03:13.608269+00:00
-- url     : https://prove2.me/submissions/8382a43d-5e87-4520-a9b1-824f7ba01dcd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimA_zero_71f121cb2924
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimA_succ_e09aea1c859f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimB_48d5ff25efd3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_IsSES_dimC_0259e9a5d3e7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_alt_sum_e5d5b5b56ff0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open EulerSES
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace EulerSES
theorem _root_.solution : EulerSES.Statement := by
  intro F _ A B C _ _ _ _ _ _ CA CB CC dA dB dC f g N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    hfa hfb hfc hsub
  have H : IsSES CA CB CC dA dB dC f g := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have key := alt_sum (fun n => (Module.finrank F (coh CA dA n) : ℤ))
    (fun n => (Module.finrank F (coh CB dB n) : ℤ)) (fun n => (Module.finrank F (coh CC dC n) : ℤ))
    (fun n => (Module.finrank F (LinearMap.range (H.iA n)) : ℤ))
    (fun n => (Module.finrank F (LinearMap.range (H.pB n)) : ℤ))
    (fun n => (Module.finrank F (LinearMap.range (H.delta n)) : ℤ))
    (by exact_mod_cast H.dimA_zero hfa)
    (fun n => by exact_mod_cast H.dimA_succ hfa n)
    (fun n => by exact_mod_cast H.dimB hfb n)
    (fun n => by exact_mod_cast H.dimC hfc n) N
  have hr : Module.finrank F (LinearMap.range (H.delta N)) = 0 := by
    have := hfa (N + 1)
    have h0 : Module.finrank F (coh CA dA (N + 1)) = 0 := Module.finrank_zero_of_subsingleton
    exact Nat.eq_zero_of_le_zero (h0 ▸ Submodule.finrank_le _)
  simp only [hr, Nat.cast_zero, mul_zero, add_zero] at key
  exact key
end EulerSES
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
