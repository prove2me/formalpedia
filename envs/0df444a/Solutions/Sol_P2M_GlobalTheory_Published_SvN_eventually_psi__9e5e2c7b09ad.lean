-- Prove2me | solution 1 for P2M_GlobalTheory_Published_SvN_eventually_psi__9e5e2c7b09ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:14:03.140852+00:00
-- url     : https://prove2.me/submissions/7345f511-d5a2-45fc-abd0-34c8162dfec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_GlobalTheory_Published_SvN_eventually_psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GlobalTheory.Published.SvN
theorem _root_.solution {ψ : AddChar F ℂ} (hψ : Continuous ψ) : ∀ᶠ z in 𝓝 (0 : F), ψ z = 1 := by
  filter_upwards [eventually_psi hψ] with z hz
  simpa using hz 1 (one_mem _)
end GlobalTheory.Published.SvN
