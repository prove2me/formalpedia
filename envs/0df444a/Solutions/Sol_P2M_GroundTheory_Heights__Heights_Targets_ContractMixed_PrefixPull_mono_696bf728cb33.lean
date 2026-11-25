-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_mono_696bf728cb33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:20:35.745804+00:00
-- url     : https://prove2.me/submissions/5337e5aa-9f01-4433-bc34-74e331a8bcc2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Targets.ContractMixed
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Targets.ContractMixed
namespace PrefixPull
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p q n : ℕ} {L' : Fin n → HermLine ι'}
    (h : PrefixPull κ v p L') (hqp : q ≤ p) : PrefixPull κ v q L' := by
  obtain ⟨hpn, L, hL, hLL⟩ := h
  exact ⟨hqp.trans hpn, fun j => L (Fin.castLE hqp j), fun j => hL _, fun j => hLL (Fin.castLE hqp j)⟩
end PrefixPull
end GroundTheory.Heights₂.Heights.Targets.ContractMixed
