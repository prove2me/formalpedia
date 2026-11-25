-- Prove2me | solution 1 for PI.GreenLabelMapW.hasCuspLabel_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:28.09524+00:00
-- url     : https://prove2.me/submissions/e69ed3ad-c07b-4b6f-a8ac-35f3b895d6da

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution (Cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ τ' : FDRep ℂ (GL ι K)}
    (h : ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ))
    {P : K[X]} (hP : HasCuspLabel Cv τ P) : HasCuspLabel Cv τ' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  exact ⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => (h γ).trans (h5 x hx γ hγ z hz m hm)⟩
end PI.GreenLabelMapW
