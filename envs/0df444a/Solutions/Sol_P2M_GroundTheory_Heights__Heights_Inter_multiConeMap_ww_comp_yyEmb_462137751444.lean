-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_multiConeMap_ww_comp_yyEmb_462137751444
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:59.629215+00:00
-- url     : https://prove2.me/submissions/5ee8c43d-8144-477f-8336-1cc0dc271137

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreProduct
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFibreProduct

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {Ω : Type} [Field Ω] {ι ν κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a : Fin 2 → Φ) (j : Fin 2) :
    (T.multiConeMap (T.wwCoord x δ e φ (a 0) (a 1))).comp
        (rename (T.yyEmb j) : MRing (T.yyIdx ι ν κ) →ₐ[ℤ] MRing (T.wwIdx ι ν κ)).toRingHom =
      (rename (diagonalBlockIndex j) : MvPolynomial T.YBlk Φ →ₐ[Φ] MvPolynomial T.WBlk Φ).toRingHom.comp
        (T.multiConeMap (T.yyCoord x δ e φ (a j))) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap]
  · rcases p with ⟨_ | _ | _, i⟩
    · simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
    · simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
    · fin_cases j <;> simp [T.multiConeMap, T.yyEmb, T.wwCoord, T.yyCoord, diagonalBlockIndex]
end GroundTheory.Heights₂.Heights.Inter
