-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.DeltaB.trace_isIntegral_rank2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:38.508279+00:00
-- url     : https://prove2.me/submissions/888e3ace-caa0-406d-82b3-c13d071e6f1d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_GoodRDeltaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.DeltaB
open Polynomial
variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]
namespace PI.UnitaryGroupMassFormula.CntFormula.DeltaB
theorem _root_.solution (b : Module.Basis (Fin 2) K A) {y : A} (hy : IsIntegral R y) :
    IsIntegral R (Algebra.trace K A y) := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  let L := AlgebraicClosure K
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix b y
  let M' : Matrix (Fin 2) (Fin 2) L := M.map (algebraMap K L)
  have hpy : Polynomial.aeval y p = 0 := hp
  have hpM : Polynomial.aeval M p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix b).restrictScalars R) y p
    rw [hpy, map_zero] at h1
    exact h1
  have hpM' : Polynomial.aeval M' p = 0 := by
    have h1 := Polynomial.aeval_algHom_apply
      (((Algebra.ofId K L).mapMatrix : Matrix (Fin 2) (Fin 2) K →ₐ[K] Matrix (Fin 2) (Fin 2) L).restrictScalars R) M p
    rw [hpM, map_zero] at h1
    exact h1
  have hroot : ∀ μ ∈ M'.charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have h1 : μ ∈ spectrum L M' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots'.mp hμ).2
    have h2 := spectrum.subset_polynomial_aeval M' (p.map (algebraMap R L)) ⟨μ, h1, rfl⟩
    rw [Polynomial.aeval_map_algebraMap, hpM', spectrum.zero_eq] at h2
    refine ⟨p, hpm, ?_⟩
    have h3 : Polynomial.eval μ (p.map (algebraMap R L)) = 0 := h2
    rwa [Polynomial.eval_map] at h3
  have htr : algebraMap K L (Algebra.trace K A y) = M'.charpoly.roots.sum := by
    rw [Algebra.trace_eq_matrix_trace b y, ← Matrix.trace_eq_sum_roots_charpoly]
    simp [M', M, Matrix.trace, Matrix.map_apply]
  have hint : IsIntegral R (algebraMap K L (Algebra.trace K A y)) := by
    rw [htr]
    exact IsIntegral.multiset_sum hroot
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).mp hint
end PI.UnitaryGroupMassFormula.CntFormula.DeltaB
