-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_eq_stopped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/e08ecbc0-c81b-4d21-9d03-36af68146ead

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    (S B N d L m : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource
        S B N d L m width schedule ξ ζ =
      dSVDensityRationalHeterogeneousOriginalStoppedState
        S B N d L m width schedule ξ ζ := by
  classical
  ext ⟨x, y⟩
  obtain ⟨⟨⟨φ, a⟩, i⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective x
  obtain ⟨⟨⟨ψ, b⟩, j⟩, rfl⟩ :=
    (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
      S B N d L m).surjective y
  obtain ⟨φ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective φ
  obtain ⟨ψ', rfl⟩ :=
    (Fintype.equivFin
      (DSVDensityRationalPublicMultiscalePhase S B)).surjective ψ
  rw [dSVDensityRationalHeterogeneousOriginalSameStopSigmaSource_apply]
  change _ =
    dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource
      S B N d L m width schedule ξ ζ
      (dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) φ', a), i),
       dSVDensityRationalPublicMultiscalePhaseTargetFirstIndexEquiv
        S B N d L m
        (((Fintype.equivFin
          (DSVDensityRationalPublicMultiscalePhase S B)) ψ', b), j))
  rw [dSVDensityRationalHeterogeneousTargetFirstSpectralPhysicalSource_apply]
  simp [ePRState]
end QuantumParallelRepetition
