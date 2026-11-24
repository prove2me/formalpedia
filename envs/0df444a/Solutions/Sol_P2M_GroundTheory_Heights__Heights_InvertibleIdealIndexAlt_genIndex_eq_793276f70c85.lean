-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:43.518805+00:00
-- url     : https://prove2.me/submissions/7b890a8f-f755-46e9-bf2d-bef366923cb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_injective_e116db2bcf37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_genIndex_eq_div_of_le_aa8fc90600a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesLineDegree_genIndex_map_of_injective_818d1ee55c6c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt.mulBy_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
theorem _root_.solution {X J M : AddSubgroup L} {β δ : L} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hJX : J ≤ X)
    (hβX : X.map (mulBy β) ≤ X) (hδX : X.map (mulBy δ) ≤ X) (hβJ : J.map (mulBy β) ≤ J)
    (hM : ∀ x, x ∈ M ↔ ∃ y ∈ J, β * x = δ * y) (hJ : J.relIndex X ≠ 0)
    (hδ' : (X.map (mulBy δ)).relIndex X ≠ 0) :
    genIndex M X = ((X.map (mulBy β)).relIndex X : ℝ) /
      (((X.map (mulBy δ)).relIndex X : ℝ) * (J.relIndex X : ℝ)) := by
  have hMβ : M.map (mulBy β) = J.map (mulBy δ) := by
    ext z
    simp only [AddSubgroup.mem_map, mulBy_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, h⟩ := (hM x).1 hx
      exact ⟨y, hy, h.symm⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨δ * y / β, (hM _).2 ⟨y, hy, by field_simp⟩, by field_simp⟩
  set C := (J.map (mulBy β)).map (mulBy δ) with hC
  have hC' : C = (J.map (mulBy δ)).map (mulBy β) := by
    rw [hC, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext x
    simp [mul_left_comm]
  have hCA : C ≤ J.map (mulBy δ) := AddSubgroup.map_mono hβJ
  have hCB : C ≤ X.map (mulBy β) := by
    rw [hC']
    exact AddSubgroup.map_mono (le_trans (AddSubgroup.map_mono hJX) hδX)
  have e1 : C.relIndex (J.map (mulBy δ)) = (J.map (mulBy β)).relIndex J :=
    AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective hδ)
  have e2 : C.relIndex (X.map (mulBy β)) = (J.map (mulBy δ)).relIndex X := by
    rw [hC']
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective hβ)
  have e3 : (J.map (mulBy β)).relIndex J * J.relIndex X =
      (X.map (mulBy β)).relIndex X * J.relIndex X := by
    rw [AddSubgroup.relIndex_mul_relIndex _ _ _ hβJ hJX,
      ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hβX,
      AddSubgroup.relIndex_map_map_of_injective (f := mulBy β) _ _ (mulBy_injective hβ)]
    exact Nat.mul_comm _ _
  have e4 : (J.map (mulBy δ)).relIndex X = J.relIndex X * (X.map (mulBy δ)).relIndex X := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hJX) hδX,
      AddSubgroup.relIndex_map_map_of_injective (f := mulBy δ) _ _ (mulBy_injective hδ)]
  have e3' : (J.map (mulBy β)).relIndex J = (X.map (mulBy β)).relIndex X :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hJ) e3
  have hCne : C.relIndex (X.map (mulBy β)) ≠ 0 := by
    rw [e2, e4]
    exact mul_ne_zero hJ hδ'
  rw [← KLinesLineDegree.genIndex_map_of_injective (mulBy β) (mulBy_injective hβ), hMβ,
    IndefiniteRowSideFullHecke.Kernels.genIndex_eq_div_of_le hCA hCB hCne, e1, e2, e3', e4]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
