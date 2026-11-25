-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagPull_cross_mem_0576bce22251
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:20.992395+00:00
-- url     : https://prove2.me/submissions/f65638e2-9c71-429b-ac41-6812525f4759

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_eval__mul_blk_9a6df9c2595d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_prod_YBlk_228ddc3d6696
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_rename_469732d254e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line0_c454c5ab19c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagPull_multiConeMap_X_line1_6473e0d79e46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_prod_YBlk_e84c3fe06e16


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Inter.DiagPull
variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)
namespace GroundTheory.Heights₂.Heights.Inter.DiagPull
theorem _root_.solution (s : MRing (T.yyIdx ι ν κ)) (d : T.YBlk → ℕ) (hs : IsMultiHomog s d) (k : κ) :
    rename (T.yyEmb 0) s * X ⟨.line1, k⟩ ^ d .line - rename (T.yyEmb 1) s * X ⟨.line0, k⟩ ^ d .line ∈
      T.wwIdeal x δ e φ a₀ a₀ := by
  rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, multiConeMap_X_line0,
    multiConeMap_X_line1, multiConeMap_rename, multiConeMap_rename,
    eval₂_mul_blk hs (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q)) (fun b => X (blk 0 b)),
    eval₂_mul_blk hs (Int.castRingHom _) (fun q => C (T.yyCoord x δ e φ a₀ q)) (fun b => X (blk 1 b)),
    prod_YBlk, prod_YBlk]
  simp only [blk]
  simp only [Fin.isValue, if_true, one_ne_zero, if_false]
  ring
end GroundTheory.Heights₂.Heights.Inter.DiagPull
