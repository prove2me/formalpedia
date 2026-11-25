-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures.finite_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:26.044085+00:00
-- url     : https://prove2.me/submissions/d00a180c-28e0-4491-b053-0d754fe26dd0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSumStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_PeakTraceBoundHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
variable {E : Type*} [CStarAlgebra E]
namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
theorem _root_.solution (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    {κ : Type*} (f : κ → E) (hf : ∀ i, f i ∈ S) (b : E) (hb : b ∈ S) (ε : ℝ)
    (h : ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ε ≤ ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨b, hb⟩)‖ →
        ∃ i, 1 < ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖) :
    ∃ t : Finset κ, ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ε ≤ ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨b, hb⟩)‖ →
        ∃ i ∈ t, 1 < ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖ := by
  classical
  have : CompleteSpace S.topologicalClosure := S.isClosed_topologicalClosure.completeSpace_coe
  have hev : ∀ a : S.topologicalClosure,
      Continuous (fun φ : WeakDual.characterSpace ℂ S.topologicalClosure => φ a) :=
    fun a => (WeakDual.eval_continuous a).comp continuous_subtype_val
  let K : Set (WeakDual.characterSpace ℂ S.topologicalClosure) :=
    {φ | ε ≤ ‖φ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨b, hb⟩)‖}
  have hK : IsClosed K := isClosed_le continuous_const (hev _).norm
  let U : κ → Set (WeakDual.characterSpace ℂ S.topologicalClosure) :=
    fun i => {φ | 1 < ‖φ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖}
  have hU : ∀ i, IsOpen (U i) := fun i => isOpen_lt continuous_const (hev _).norm
  have hcov : K ⊆ ⋃ i, U i := by
    intro φ hφ
    obtain ⟨i, hi⟩ := h (WeakDual.CharacterSpace.equivAlgHom φ)
      (by rw [WeakDual.CharacterSpace.equivAlgHom_coe]; exact hφ)
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rw [WeakDual.CharacterSpace.equivAlgHom_coe] at hi
    exact hi
  obtain ⟨t, ht⟩ := hK.isCompact.elim_finite_subcover U hU hcov
  refine ⟨t, fun ψ hψ => ?_⟩
  have hmem : WeakDual.CharacterSpace.equivAlgHom.symm ψ ∈ K := by
    show ε ≤ ‖(WeakDual.CharacterSpace.equivAlgHom.symm ψ) _‖
    rw [WeakDual.CharacterSpace.equivAlgHom_symm_coe]; exact hψ
  have := ht hmem
  simp only [Set.mem_iUnion] at this
  obtain ⟨i, hi, hi'⟩ := this
  refine ⟨i, hi, ?_⟩
  have hi'' : 1 < ‖(WeakDual.CharacterSpace.equivAlgHom.symm ψ)
      (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖ := hi'
  rwa [WeakDual.CharacterSpace.equivAlgHom_symm_coe] at hi''
end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures
