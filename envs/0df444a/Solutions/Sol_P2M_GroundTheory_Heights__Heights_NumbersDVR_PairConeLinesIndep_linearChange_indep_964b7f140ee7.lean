-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:34.999032+00:00
-- url     : https://prove2.me/submissions/fa99bfdf-e2d9-42f5-95ce-8de91d93ec06

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace PairConeLinesIndep
theorem _root_.solution {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {N : ℕ}
    (P : Matrix (Fin N) (Fin N) Ω) (hP : IsUnit P) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (P i j)) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  let f : Fin N → MvPolynomial (Fin N) Ω := fun i => ∑ j, X j * C (P i j)
  let g : Fin N → MvPolynomial (Fin N) Ω := fun j => ∑ k, X k * C (P⁻¹ j k)
  have hgf : (fun i => aeval g (f i)) = X := by
    funext i
    simp only [f, g, map_sum, map_mul, aeval_X, aeval_C, MvPolynomial.algebraMap_eq]
    calc ∑ j, (∑ k, X k * C (P⁻¹ j k)) * C (P i j)
        = ∑ k, X k * C ((P * P⁻¹) i k) := by
          simp_rw [Finset.sum_mul, Matrix.mul_apply, map_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]
          ring
      _ = X i := by
          rw [Matrix.mul_nonsing_inv _ hdet]
          simp [Matrix.one_apply]
  have hf : AlgebraicIndependent Ω f := by
    apply AlgebraicIndependent.of_aeval (x := g)
    rw [hgf]
    exact algebraicIndependent_X _ _
  have h := ht.aeval_of_algebraicIndependent hf
  convert h using 1
  funext i
  simp [f, map_sum, aeval_X]
end PairConeLinesIndep
end GroundTheory.Heights₂.Heights.NumbersDVR
