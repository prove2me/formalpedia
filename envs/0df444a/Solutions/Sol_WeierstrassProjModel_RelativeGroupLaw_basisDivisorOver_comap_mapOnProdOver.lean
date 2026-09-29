-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.basisDivisorOver_comap_mapOnProdOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e724df08-f34b-5678-a187-37ee71610036

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

theorem solution
    {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (P Q : SchemeHomOver t (projModelStrCR V)) :
    (G.basisDivisorOver q t P Q).comap (mapOnProdOver (projModelStrCR V) ψ hψ) =
        G.basisDivisorOver q t' (schemeHomOverComp ψ hψ P) (schemeHomOverComp ψ hψ Q) ∧
      (G.torsionIdealOver q t).comap (mapOnProdOver (projModelStrCR V) ψ hψ) = G.torsionIdealOver q t' := by
  have hsep : IsSeparated (projModelStrCR V) := by
    delta projModelStrCR; infer_instance
  constructor
  ·
    unfold RelativeGroupLaw.basisDivisorOver
    rw [AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver]
    have key : ∀ i : Fin (q * q), ψ ≫ G.basisTupleOver q t P Q i =
        G.basisTupleOver q t' (schemeHomOverComp ψ hψ P) (schemeHomOverComp ψ hψ Q) i := by
      intro i
      unfold RelativeGroupLaw.basisTupleOver RelativeGroupLaw.linCombOver
      rw [← schemeHomOverComp_coe ψ hψ, G.mul_natural, G.nsmul_natural, G.nsmul_natural]
    simp_rw [prodKerGraph_eq_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2; exact key i
  · unfold RelativeGroupLaw.torsionIdealOver
    rw [← Scheme.IdealSheafData.comap_comp, mapOnProdOver_fst]

end S_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_basisDivisorOver_comap_mapOnProdOver (solution)
