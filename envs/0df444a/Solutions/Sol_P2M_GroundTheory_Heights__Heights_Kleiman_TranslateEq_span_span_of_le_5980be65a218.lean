-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_span_span_of_le_5980be65a218
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:35.045+00:00
-- url     : https://prove2.me/submissions/8e138113-3b54-4a05-887f-25dd25a25f7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable {A B : Subalgebra S Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (hAB : A ≤ B) (T : Set Ω) :
    Submodule.span B (Submodule.span A T : Set Ω) = Submodule.span B T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul a u _ hu => exact Submodule.smul_mem _ (⟨a, hAB a.2⟩ : B) hu
  · exact Submodule.span_mono Submodule.subset_span
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
