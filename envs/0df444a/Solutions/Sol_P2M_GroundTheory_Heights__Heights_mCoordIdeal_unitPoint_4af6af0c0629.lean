-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mCoordIdeal_unitPoint_4af6af0c0629
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:31.264414+00:00
-- url     : https://prove2.me/submissions/1f284e5a-652d-479f-a744-07f1e63193cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_eq_ker_9a86be206417

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (n)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ 0) unitPoint = ⊥ := by
  rw [mCoordIdeal_eq_ker]
  have h : (eval₂Hom (Int.castRingHom (MvPolynomial Unit ℚ)) fun v : Coord (fun _ : Unit ↦ 0) ↦
      C (unitPoint v) * X v.1) =
      (map (Int.castRingHom ℚ)).comp (rename (Sigma.fst : Coord (fun _ : Unit ↦ 0) → Unit)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ by simp [unitPoint])
  rw [h]
  refine (RingHom.injective_iff_ker_eq_bot _).mp ?_
  refine (map_injective _ Int.cast_injective).comp (rename_injective _ ?_)
  rintro ⟨a, i⟩ ⟨b, j⟩ _
  cases a
  cases b
  have hij : i = j := Subsingleton.elim (α := Fin 1) i j
  rw [hij]
end GroundTheory.Heights₂.Heights
