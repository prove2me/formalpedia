-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.isDrinfeldBasis_iff_isDrinfeldBasisOver_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4f97cdc8-9197-59e2-a563-8cfd2c3f14a4

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id.WeierstrassCurve.DrinfeldGlobal"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Projective"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "Section basisDivisor toPullbackId torsionIdeal IsDrinfeldBasis"
namespace IdBridge
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

theorem ker_comp_iso_hom {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (e : X ≅ Y) :
    (i ≫ e.hom).ker = i.ker.comap e.inv := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : pullback.fst e.inv i = pullback.snd e.inv i ≫ i ≫ e.hom := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, e.inv_hom_id, Category.comp_id]
  rw [h]
  exact (Scheme.Hom.ker_comp_of_isIso _ _).symm

end WeierstrassCurve.DrinfeldGlobal.IdBridge

open WeierstrassCurve.DrinfeldGlobal.IdBridge in
theorem solution
    {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T} (G : RelativeGroupLaw T (projModelStrCR W))
    (q : ℕ) (P Q : Section W) :
    IsDrinfeldBasis G q P Q ↔ G.IsDrinfeldBasisOver q (𝟙 _) P Q := by
  have hsep : IsSeparated (projModelStrCR W) := by unfold projModelStrCR; infer_instance
  haveI : IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of T)))).1 := by
    have : IsClosedImmersion ((G.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ projModelStrCR W) := by
      rw [(G.one (𝟙 _)).2]; infer_instance
    exact .of_comp _ (projModelStrCR W)
  have hb : basisDivisor G q P Q = G.basisDivisorOver q (𝟙 _) P Q := rfl
  have ht : torsionIdeal G q = G.torsionIdealOver q (𝟙 _) := by
    let e : projModelCR W ≅ pullback (projModelStrCR W) (𝟙 (Spec (CommRingCat.of T))) :=
      { hom := toPullbackId
        inv := pullback.fst _ _
        hom_inv_id := pullback.lift_fst _ _ _
        inv_hom_id := by
          apply pullback.hom_ext
          · rw [Category.assoc, toPullbackId, pullback.lift_fst, Category.comp_id, Category.id_comp]
          · rw [Category.assoc, toPullbackId, pullback.lift_snd, Category.id_comp, pullback.condition,
              Category.comp_id] }
    change (pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 ≫ e.hom).ker = _
    rw [ker_comp_iso_hom]
    rfl
  unfold IsDrinfeldBasis WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver
  rw [hb, ht]

end S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_isDrinfeldBasis_iff_isDrinfeldBasisOver_id (solution)
