-- Prove2me | solution 1 for PI.VolStabS.linIndep_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:12.576311+00:00
-- url     : https://prove2.me/submissions/a13a7408-19d8-4a67-b6a7-2de00721b2d0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.VolStabS
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (h : IsUnit (gramR R σ J X).det) :
    LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hM : (gramR R σ J X).mulVec g = 0 := by
    funext b
    have hb := congrArg (hLin R σ J (X b)) hg
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hb
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← hb]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_comm]; rfl
  have hg0 : g = 0 := by
    rw [← Matrix.one_mulVec g, ← Matrix.nonsing_inv_mul _ h, ← Matrix.mulVec_mulVec, hM,
      Matrix.mulVec_zero]
  intro i
  rw [hg0]
  rfl
end PI.VolStabS
