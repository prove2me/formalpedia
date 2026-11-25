-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_seq_isGradedSub_971d8254db49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:44:50.767953+00:00
-- url     : https://prove2.me/submissions/910dd288-f66c-48d5-9d83-091e763ed749

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_bot_92731b6e8486
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_sup_span_587463f0741f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_next_mem_80fce6c3a8f6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 2000] lexDecEq
variable (ι 𝓜)
variable {ι 𝓜}
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution [IsNoetherianRing S] (hgr : IsMGraded S ι 𝓜) (j : ℕ) :
    IsGradedSub 𝓜 (seq ι 𝓜 j) := by
  induction j with
  | zero => exact isGradedSub_bot
  | succ j ih => exact isGradedSub_sup_span hgr ih (next_mem ι 𝓜 _)
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
