-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_TyFin_reRep___apply_2995d93d3384
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:57.818966+00:00
-- url     : https://prove2.me/submissions/fe13c4ba-9a87-4526-b2b4-94841d48e9fa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
omit [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (e : α ≃ β) (τ : FDRep ℂ (GL α K)) (g : GL β K) :
    (reRep e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := by
  rfl
end GlobalTheory.CompanionTheory.TyFin
