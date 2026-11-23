-- Prove2me | solution 1 for PI.VolStabW.linIndep_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:12.740341+00:00
-- url     : https://prove2.me/submissions/5a1a83d6-f9b5-4164-9eeb-de5d3886907e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.VolStabW
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hG : (gramR R σ J X).mulVec c = 0 := by
    funext b
    have h1 := congrArg (hLin R σ J (X b)) hc
    rw [map_sum, map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← h1]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]; rfl
  have hc0 : c = 0 := by
    calc c = ((gramR R σ J X)⁻¹ * gramR R σ J X).mulVec c := by
          rw [Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
      _ = (gramR R σ J X)⁻¹.mulVec ((gramR R σ J X).mulVec c) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hG, Matrix.mulVec_zero]
  intro i
  exact congrFun hc0 i
end PI.VolStabW
