-- Prove2me | solution 1 for PIW.AdelClassFin.hform_exists_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:30.641491+00:00
-- url     : https://prove2.me/submissions/feb8cbc1-ba7d-4366-a2e3-48030034132b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSmulRight
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_add_right__73a64fb2bbe8
import Theorems.Thm_P2M_PIW_AdelClassFin_hform_smul_right__f0caf7c17a43
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
namespace PIW.AdelClassFin
theorem _root_.solution (hdet : J.det ≠ 0) (S : Set (Fin m → E)) (hS : Submodule.span E S = ⊤)
    {x : Fin m → E} (hx : x ≠ 0) : ∃ z ∈ S, hform (starRingEnd E) J x z ≠ 0 := by
  by_contra h
  push_neg at h
  let f : (Fin m → E) →ₗ[E] E :=
    { toFun := fun y => hform (starRingEnd E) J x y
      map_add' := fun y y' => hform_add_right' J x y y'
      map_smul' := fun c y => by simpa using hform_smul_right' J c x y }
  have hle : Submodule.span E S ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro z hz
    exact LinearMap.mem_ker.mpr (h z hz)
  have hall : ∀ y, hform (starRingEnd E) J x y = 0 := by
    intro y
    have hy : y ∈ Submodule.span E S := by
      rw [hS]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hle hy)
  have hv : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have hj := hall (Pi.single j 1)
    simpa [hform, Matrix.vecMul, dotProduct, Pi.single_apply] using hj
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  apply hx
  funext i
  have hi := congrFun hv0 i
  simpa using hi
end PIW.AdelClassFin
