-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/e3d9094d-dc5c-59e8-8c4e-b884fcb7ed78

import Mathlib
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace K7eAux

theorem prodKerGraph_le {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) (i : Fin r) :
    prodKerGraph f a ha ≤ (graphOver f (a i) (ha i)).ker := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [ideal_prodKerGraph]
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))

theorem exists_comp_eq_of_comap_le_ker_graphOver {𝒞 S Z : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}
    (k : Z ⟶ 𝒞) [IsClosedImmersion k] (a : T ⟶ 𝒞) (ha : a ≫ f = g)
    (h : k.ker.comap (pullback.fst f g) ≤ (graphOver f a ha).ker) :
    ∃ p : T ⟶ Z, p ≫ k = a := by
  have H : k.ker ≤ a.ker := by
    have h' := Scheme.IdealSheafData.le_map_iff_comap_le.mpr h
    rwa [Scheme.IdealSheafData.map_ker, graphOver_fst] at h'
  exact ⟨IsClosedImmersion.lift k a H, IsClosedImmersion.lift_fac k a H⟩

end K7eAux

open K7eAux in

theorem solution
    {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : RelativeGroupLaw R (projModelStrCR V)) {q : ℕ} (hq : 2 ≤ q)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {P Q : SchemeHomOver t (projModelStrCR V)}
    (h : G.IsDrinfeldBasisOver q t P Q) :
    (∃ p : T ⟶ G.schemeKer q, p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = P.1) ∧
      ∃ p : T ⟶ G.schemeKer q, p ≫ pullback.fst (G.schemeNsmul q) (G.one (𝟙 _)).1 = Q.1 := by

  haveI : IsSeparated (projModelStrCR V) := (WeierstrassProjModel.projModelStrCR_isProper V).toIsSeparated
  haveI : IsClosedImmersion (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    have : IsClosedImmersion ((G.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ projModelStrCR V) := by
      rw [(G.one (𝟙 _)).2]; infer_instance
    exact IsClosedImmersion.of_comp _ (projModelStrCR V)
  have hq0 : 0 < q := by omega
  have hq1 : 1 < q := by omega
  have hqq : q < q * q := by nlinarith
  have h1q : 1 < q * q := lt_trans hq1 hqq

  let iP : Fin (q * q) := ⟨q, hqq⟩
  let iQ : Fin (q * q) := ⟨1, h1q⟩
  have hP : G.basisTupleOver q t P Q iP = P.1 := by
    show (G.linCombOver t P Q (q / q) (q % q)).1 = P.1
    rw [Nat.div_self hq0, Nat.mod_self]
    show (G.mul t (G.nsmul t 1 P) (G.nsmul t 0 Q)).1 = P.1
    rw [G.nsmul_one_apply, G.nsmul_zero, G.mul_one]
  have hQ : G.basisTupleOver q t P Q iQ = Q.1 := by
    show (G.linCombOver t P Q (1 / q) (1 % q)).1 = Q.1
    rw [Nat.div_eq_of_lt hq1, Nat.mod_eq_of_lt hq1]
    show (G.mul t (G.nsmul t 0 P) (G.nsmul t 1 Q)).1 = Q.1
    rw [G.nsmul_one_apply, G.nsmul_zero, G.one_mul]

  have hle : ∀ i : Fin (q * q),
      (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (Spec (CommRingCat.of R)))).1).ker.comap
          (pullback.fst (projModelStrCR V) t) ≤
        (graphOver (projModelStrCR V) (G.basisTupleOver q t P Q i) (G.basisTupleOver_over q t P Q i)).ker := by
    intro i
    have : G.torsionIdealOver q t = G.basisDivisorOver q t P Q := h.symm
    exact (le_of_eq this).trans (prodKerGraph_le _ _ _ i)
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hp⟩ := exists_comp_eq_of_comap_le_ker_graphOver (projModelStrCR V) _ _ _ (hle iP)
    exact ⟨p, hp.trans hP⟩
  · obtain ⟨p, hp⟩ := exists_comp_eq_of_comap_le_ker_graphOver (projModelStrCR V) _ _ _ (hle iQ)
    exact ⟨p, hp.trans hQ⟩

end S_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq (solution)
