-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_reads_unitPoint_e27e5459dcf4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:12:21.977102+00:00
-- url     : https://prove2.me/submissions/6b72f81d-b697-472e-958f-3a60c6bf614c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_form_eq_zero_of_unitPoint_13babd4cbc4a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_whole_mkF_injective_f0f5f10d0d70


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
    (ArithVariety.whole fun _ : Unit ↦ 0).Reads unitPoint (fun _ ↦ 1) 1
      ((ArithVariety.whole fun _ : Unit ↦ 0).mkF (X ⟨(), 0⟩)) := by
  intro g h δg δh hg hh hd
  have hXh : IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ 0)
      ((X ⟨(), 0⟩ : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) * h) δg := by
    have h1 := (isWeightedHomogeneous_X ℤ (coordDeg fun _ : Unit ↦ 0) ⟨(), 0⟩).mul hh
    have hδ : coordDeg (fun _ : Unit ↦ 0) ⟨(), 0⟩ + δh = δg := by
      funext u
      cases u
      have h2 : (δg () : ℤ) = δh () + 1 := hd ()
      simp only [coordDeg, Pi.add_apply, Pi.single_eq_same]
      change 1 + δh () = δg ()
      omega
    rwa [hδ] at h1
  have hsub := hg.sub hXh
  have hval : aeval unitPoint (X ⟨(), 0⟩ : MvPolynomial (Coord fun _ : Unit ↦ 0) ℤ) = 1 := by
    simp [unitPoint]
  constructor
  · intro e
    have h0 : g - X ⟨(), 0⟩ * h = 0 := form_eq_zero_of_unitPoint hsub (by
      rw [map_sub, map_mul, hval, e, one_mul, sub_self])
    rw [sub_eq_zero.mp h0, map_mul]
  · intro e
    have h0 : g = X ⟨(), 0⟩ * h := ArithVariety.whole_mkF_injective _ (by rw [e, map_mul])
    rw [h0, map_mul, hval, one_mul]
end GroundTheory.Heights₂.Heights
