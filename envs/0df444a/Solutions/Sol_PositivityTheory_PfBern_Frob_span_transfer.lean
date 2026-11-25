-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.span_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:13.256958+00:00
-- url     : https://prove2.me/submissions/d64d8760-324c-4981-950f-ff0ff018c8d9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultipleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PartialIntegralMemSchwartzBruhatStatement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TensInduction

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
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution {A : Type*} [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : SB A →ₗ[ℂ] M) {S : Set (A → ℂ)} (hS : S ⊆ SB A) (N : Submodule ℂ M)
    (hT : ∀ F (hF : F ∈ S), T ⟨F, hS hF⟩ ∈ N) (f : SB A)
    (hf : (f : A → ℂ) ∈ Submodule.span ℂ S) : T f ∈ N := by
  have key : Submodule.span ℂ S ≤ (N.comap T).map (SB A).subtype := by
    rw [Submodule.span_le]
    intro F hF
    exact Submodule.mem_map.2 ⟨⟨F, hS hF⟩, hT F hF, rfl⟩
  obtain ⟨f', hf', e⟩ := Submodule.mem_map.1 (key hf)
  have e' : f' = f := Subtype.ext e
  subst e'
  exact hf'
end PositivityTheory.PfBern.Frob
