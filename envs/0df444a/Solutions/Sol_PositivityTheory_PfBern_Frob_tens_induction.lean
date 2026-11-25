-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.tens_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:51.491383+00:00
-- url     : https://prove2.me/submissions/30f42a71-0420-44ee-977e-c910e18d259b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction
import Theorems.Thm_PositivityTheory_PfBern_Frob_span_transfer
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_prod_span_tensors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B]
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module ℂ M] (T : SB (A × B) →ₗ[ℂ] M)
    (N : Submodule ℂ M) (f : SB (A × B))
    (h : ∀ (a : SB A) (b : SB B), (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 →
      (f : A × B → ℂ) q ≠ 0) → T (tens a b) ∈ N) : T f ∈ N := by
  refine span_transfer T ?_ N ?_ f (GlobalTheory.T.schwartzBruhat_prod_span_tensors A B f)
  · rintro F ⟨a, b, -, rfl⟩
    exact tens_mem a b
  · rintro F ⟨a, b, hab, rfl⟩
    exact h a b hab
end PositivityTheory.PfBern.Frob
