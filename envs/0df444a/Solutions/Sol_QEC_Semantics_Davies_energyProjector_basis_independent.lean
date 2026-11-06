-- Prove2me | solution 1 for QEC.Semantics.Davies.energyProjector_basis_independent
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-05T14:35:54.995947+00:00
-- url     : https://prove2.me/submissions/6f0ced74-7528-4882-b53d-8f7803a8c1bc

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Theorems.Thm_QEC_Semantics_Davies_energyProjector_apply_eigenvector
import Theorems.Thm_QEC_Semantics_Davies_diagonal_apply_basis
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution {ι' : Type} [Fintype ι'] [DecidableEq ι']
    (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : OrthonormalBasis ι' ℂ V) (f : ι' → ℝ)
    (hH : diagonal b e = diagonal c f) (E : ℝ) :
    energyProjector b e E = energyProjector c f E := by
  apply c.toBasis.ext
  intro i
  change energyProjector b e E (c i) = energyProjector c f E (c i)
  have hv : diagonal b e (c i) = (f i : ℂ) • c i := by
    rw [hH]; exact diagonal_apply_basis c f i
  rw [energyProjector_apply_eigenvector b e (c i) (f i) E hv,
    energyProjector_apply_eigenvector c f (c i) (f i) E (diagonal_apply_basis c f i)]
