-- Prove2me | solution 1 for PI.VolStabSW.linIndep_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:15.629521+00:00
-- url     : https://prove2.me/submissions/48788ac8-fce1-45cb-b67b-53204e2a33e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.VolStabSW
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ b, ∑ a, g a * gramR R σ J X b a = 0 := by
    intro b
    have e := congrArg (hLin R σ J (X b)) hg
    rw [map_sum, map_zero] at e
    simp only [map_smul, smul_eq_mul] at e
    exact e
  have hv : Matrix.mulVec (gramR R σ J X) g = 0 := by
    funext b
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← key b]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hg0 : g = 0 := by
    calc g = Matrix.mulVec ((gramR R σ J X)⁻¹ * gramR R σ J X) g := by
          rw [Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  simp [hg0]
end PI.VolStabSW
