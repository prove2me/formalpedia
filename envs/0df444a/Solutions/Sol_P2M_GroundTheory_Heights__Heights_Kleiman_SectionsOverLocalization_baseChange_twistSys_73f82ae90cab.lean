-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_baseChange_twistSys_73f82ae90cab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:35.62195+00:00
-- url     : https://prove2.me/submissions/7efe0f11-edfd-4f3e-8eed-f98465c19685

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeObj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_BaseChangeTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_span_baseChange_span_614cec3597f7

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
open MvPolynomial Kleiman
open scoped Pointwise
noncomputable section
variable {S : Type*} [CommRing S] {O : Type*} [CommRing O] [Algebra S O] {Ω : Type*} [Field Ω]
  [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
theorem _root_.solution (c : ℤ) : (twistSys S x c).baseChange O = twistSys O x c := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  change Submodule.span (chartRing O x I) (twistMod S x c I : Set Ω) = twistMod O x c I
  rw [twistMod_eq_span c I hi, twistMod_eq_span c I hi, span_baseChange_span]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
