-- Prove2me | solution 1 for QEC.Coding.FiniteSymplectic.form_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:50:27.092192+00:00
-- url     : https://prove2.me/submissions/27668f3f-6e37-4513-a007-a29be0a89212

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u v
open QEC.Coding.FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteSymplectic
theorem _root_.solution : (form (F := F) (ι := ι)).Nondegenerate := by
  let B := form (F := F) (ι := ι)
  have hleft : B.SeparatingLeft := by
    intro v hv
    have hx : v.xPart = 0 :=
      (wordPairing_nondegenerate (F := F) (ι := ι)).1 v.xPart (fun z => by
        simpa [B, form, symplecticForm, wordPairing_apply, dotProduct] using
          hv ({ xPart := 0, zPart := z } : SymplecticVector F ι))
    have hz : v.zPart = 0 :=
      (wordPairing_nondegenerate (F := F) (ι := ι)).1 v.zPart (fun x => by
        have hneg : -wordPairing (F := F) (ι := ι) v.zPart x = 0 := by
          simpa [B, form, symplecticForm, wordPairing_apply, dotProduct] using
            hv ({ xPart := x, zPart := 0 } : SymplecticVector F ι)
        exact neg_eq_zero.mp hneg)
    rcases v with ⟨x, z⟩
    simp only at hx hz
    subst x
    subst z
    rfl
  refine ⟨hleft, ?_⟩
  intro v hv
  apply hleft v
  intro w
  exact form_isAlt.isRefl w v (hv w)
end QEC.Coding.FiniteSymplectic
