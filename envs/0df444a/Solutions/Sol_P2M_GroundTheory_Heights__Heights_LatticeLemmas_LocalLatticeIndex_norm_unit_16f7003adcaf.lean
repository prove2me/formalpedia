-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalLatticeIndex_norm_unit_16f7003adcaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:36.217259+00:00
-- url     : https://prove2.me/submissions/d2024dfd-d20a-4065-8f8d-75edbff3cc71

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalLatticeIndex
import Theorems.Thm_GroundTheory_Global_normalizedAbv_apply
import Theorems.Thm_GroundTheory_Global_normalizedAbv_eq_zpow
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace LocalLatticeIndex
theorem _root_.solution (u : (v.adicCompletionIntegers K)ˣ) :
    ‖((u : v.adicCompletionIntegers K) : v.adicCompletion K)‖ = 1 := by
  have h1 := (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1 u.isUnit
  have h0 : ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.ext h)
  rw [← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v h0]
  rw [show Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 from h1]
  simp
end LocalLatticeIndex
end GroundTheory.Heights₂.Heights.LatticeLemmas
