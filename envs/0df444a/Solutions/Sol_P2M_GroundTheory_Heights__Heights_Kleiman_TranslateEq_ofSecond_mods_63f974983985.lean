-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_ofSecond_mods_63f974983985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:19:43.943726+00:00
-- url     : https://prove2.me/submissions/7127ecb3-79e0-4a36-a06c-dd257783b1e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisAltAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20


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
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable (Q' : IndefiniteRowSideFullHecke.Kleiman.LineBundle (S := S) x)
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution {i : Fin (N + 1)} (h : x i ≠ 0) : Q'.mods i = toIndefiniteRowSideFullHecke (ofSecond Q').toSubSystem i := by
  rw [chartModule_of_ne_zero _ h]
  ext z
  change z ∈ Submodule.span S (Q'.lat i : Set Ω) ↔ z ∈ subOf Q' (Kleiman.singleChart h)
  rw [subOf_eq Q' (Finset.mem_singleton_self i)]
  constructor
  · intro hz
    have hle : Submodule.span S (Q'.lat i : Set Ω) ≤ (latSub Q' h).restrictScalars S :=
      Submodule.span_le.2 fun e he => he
    exact Submodule.subset_span (hle hz)
  · intro hz
    have hle : Submodule.span (Kleiman.chartRing S x (Kleiman.singleChart h)) (Q'.lat i : Set Ω) ≤
        latSub Q' h := Submodule.span_le.2 fun e he => he
    exact Submodule.subset_span (hle hz)
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
