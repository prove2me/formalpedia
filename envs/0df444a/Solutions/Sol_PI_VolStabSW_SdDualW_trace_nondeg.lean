-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.trace_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:42.13664+00:00
-- url     : https://prove2.me/submissions/7e47e542-b819-4a00-b792-cbf68ebb3916

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Theorems.Thm_PI_VolStabSW_SdDualW_trace_one_tmul

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
open PI.VolStabSW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
include b
namespace PI.VolStabSW.SdDualW
theorem _root_.solution [Algebra.IsSeparable F E] (z : Fv F v ⊗[F] E)
    (h : ∀ w, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w * z) = 0) : z = 0 := by
  classical
  let B := Algebra.TensorProduct.basis (Fv F v) b
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  let c : Fin d → Fv F v := fun k => B.repr z k
  let G : Matrix (Fin d) (Fin d) (Fv F v) :=
    (Algebra.traceMatrix F b).map (algebraMap F (Fv F v))
  have hc : G.mulVec c = 0 := by
    funext l
    have hz := h (B l)
    rw [← B.sum_repr z, Finset.mul_sum, map_sum] at hz
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [← hz]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, map_smul, hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      trace_one_tmul, smul_eq_mul, mul_comm]
    simp [G, Algebra.traceMatrix_apply, Algebra.traceForm_apply, c]
  have hdet : G.det ≠ 0 := by
    rw [show G.det = algebraMap F (Fv F v) (Algebra.traceMatrix F b).det from
      (RingHom.map_det _ _).symm]
    exact (map_ne_zero _).2 (Algebra.discr_not_zero_of_basis F b)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hc
  rw [← B.sum_repr z]
  refine Finset.sum_eq_zero fun k _ => ?_
  have : B.repr z k = 0 := congrFun hc0 k
  rw [this, zero_smul]
end PI.VolStabSW.SdDualW
