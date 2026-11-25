-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GraphClosedAlt_chartRing_subset_ampleChart_3b053720cbdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:08:32.648957+00:00
-- url     : https://prove2.me/submissions/b5f311a9-89fa-4f85-8782-f82fb2ef9b8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGraphClosedLocal

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
open GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
theorem _root_.solution (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 h I := by
  refine ⟨0, ?_⟩
  rw [pow_zero, mul_one, mul_zero]
  change a ∈ twistMod S x 0 I
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero]
  have : a = (⟨a, ha⟩ : chartRing S x I) • (1 : Ω) := by rw [chartRing_smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
end GroundTheory.Heights₂.Heights.Kleiman.GraphClosedAlt
