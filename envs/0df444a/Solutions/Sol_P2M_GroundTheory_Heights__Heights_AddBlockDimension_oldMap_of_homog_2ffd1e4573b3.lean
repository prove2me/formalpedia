-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_of_homog_2ffd1e4573b3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:52.092038+00:00
-- url     : https://prove2.me/submissions/0e59f6e7-75ac-42cc-9187-e44ebf5761bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicNew
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_plusMap_X_old_c1a40a519d86
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockDimension_oldMap_X_e33851c6039e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval__scale_of_isWeightedHomogeneous_6a2760d9d5f2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockDimension
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockDimension
theorem _root_.solution {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    oldMap D f = (∏ k, (X (some k) : MvPolynomial (Option ι) P.FunField) ^ δ k) * C (P.mkF f) := by
  have h1 : oldMap D = eval₂Hom (Int.castRingHom _)
      (fun v : Coord n ↦ (X (some v.1) : MvPolynomial (Option ι) P.FunField) * C (P.mkF (X v))) := by
    refine MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun v ↦ ?_)
    rw [oldMap_X, plusMap_X_old, eval₂Hom_X', mul_comm]
  have h2 : (C : P.FunField →+* MvPolynomial (Option ι) P.FunField).comp P.mkF =
      eval₂Hom (Int.castRingHom _)
        (fun v : Coord n ↦ (C (P.mkF (X v)) : MvPolynomial (Option ι) P.FunField)) :=
    MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun v ↦ by simp)
  rw [h1, coe_eval₂Hom]
  refine (eval₂_scale_of_isWeightedHomogeneous (fun k ↦ (X (some k) : MvPolynomial (Option ι) P.FunField))
    (fun v ↦ C (P.mkF (X v))) hf).trans ?_
  congr 1
  exact (congrArg (fun φ : MvPolynomial (Coord n) ℤ →+* _ ↦ φ f) h2).symm
end GroundTheory.Heights₂.Heights.AddBlockDimension
