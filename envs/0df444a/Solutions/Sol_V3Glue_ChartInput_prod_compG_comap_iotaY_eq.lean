-- Prove2me | solution 1 for V3Glue.ChartInput.prod_compG_comap_iotaY_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/76c9774b-0bb9-5bf1-8359-7c2ba94a31ae

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Glue_ChartInput_prod_compG_comap_iotaY_eq

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_V3Glue_ChartInput_prod_compG_comap_iotaY_eq.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.comap_comp Scheme Scheme.IdealSheafData.comap_top Scheme.IdealSheafData.comap Scheme.IdealSheafData.ofIdealTop Scheme.IdealSheafData Scheme.IdealSheafData.comap_mul" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.one_eq_top IdealSheafData.comap_comp Γ empty IdealSheafData.comap_top IdealSheafData.comap IdealSheafData.ofIdealTop restrict IdealSheafData IdealSheafData.comap_mul" namespace IdealSheafData p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "one_eq_top comap_comp comap_top ideal comap ofIdealTop comap_mul" end AlgebraicGeometry.Scheme.IdealSheafData
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData" in

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_finsetProd {X Y : Scheme.{0}} {ι : Type} (s : Finset ι)
    (G : ι → Y.IdealSheafData) (f : X ⟶ Y) :
    (∏ v ∈ s, G v).comap f = ∏ v ∈ s, (G v).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
    rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.comap_mul, ih]

theorem solution {X : Scheme.{0}} {N : Type} [Fintype N] (C : V3Glue.ChartInput X N)
    (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
    (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
    (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0) (n : N) (ϖ : Γ(C.B, ⊤))
    (F : C.Comps → (C.Res n).IdealSheafData)
    (hF : ∀ v, (C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) = (F v).comap (C.g n))
    (hprod : ∏ v, F v = (Scheme.IdealSheafData.ofIdealTop (Ideal.span {ϖ})).comap (C.ρ n ≫ C.σ n)) :
    (∏ v, C.compG hRF gRes hgRes ξ hξ v).comap (C.toGlueInput.ιY n) =
      (Scheme.IdealSheafData.ofIdealTop (Ideal.span {ϖ})).comap (C.toB n) := by
  classical
  have h2 := congrArg (fun I => Scheme.IdealSheafData.comap I (C.g n)) hprod
  beta_reduce at h2
  rw [Scheme.IdealSheafData.comap_finsetProd, ← Scheme.IdealSheafData.comap_comp] at h2
  rw [Scheme.IdealSheafData.comap_finsetProd, Finset.prod_congr rfl (fun v _ => hF v)]
  convert h2 using 2 <;> try rfl

end S_V3Glue_ChartInput_prod_compG_comap_iotaY_eq
end P2MW
export P2MW.S_V3Glue_ChartInput_prod_compG_comap_iotaY_eq (solution)
