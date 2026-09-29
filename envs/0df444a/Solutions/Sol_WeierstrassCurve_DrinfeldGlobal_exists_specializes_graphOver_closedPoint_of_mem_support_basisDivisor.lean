-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6c6c74b4-ed8f-5939-860b-7b6aa12aedb8

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_WeierstrassProjModel_projModelStrCR_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

attribute [local instance] MvPolynomial.gradedAlgebra

namespace G4aAux

theorem exists_mem_support_of_mem_support_prod {X : Scheme} {ι : Type} (s : Finset ι)
    (I : ι → X.IdealSheafData) {x : X} (hx : x ∈ (∏ i ∈ s, I i).support) : ∃ i ∈ s, x ∈ (I i).support := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty] at hx
      exact absurd hx (show x ∉ (⊤ : X.IdealSheafData).support by
        rw [Scheme.IdealSheafData.support_top]; exact id)
  | cons a s ha ih =>
      rw [Finset.prod_cons, Scheme.IdealSheafData.support_mul] at hx
      rcases hx with h | h
      · exact ⟨a, Finset.mem_cons_self a s, h⟩
      · obtain ⟨i, hi, hxi⟩ := ih h
        exact ⟨i, Finset.mem_cons_of_mem hi, hxi⟩

theorem support_ker_subset_range {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] {y : Y}
    (hy : y ∈ f.ker.support) : y ∈ Set.range f := by
  have h := f.support_ker
  rw [f.isClosedEmbedding.isClosed_range.closure_eq] at h
  have : y ∈ (f.ker.support : Set Y) := hy
  rwa [h] at this

scoped instance {T : Type} [CommRing T] (W : WeierstrassCurve T) : IsSeparated (projModelStrCR W) :=
  (WeierstrassProjModel.projModelStrCR_isProper W).toIsSeparated

end G4aAux
p2m_reactivate "P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor.G4aAux"

open G4aAux in

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T)
    (G : RelativeGroupLaw T (projModelStrCR W)) (q : ℕ) (P Q : Section W)
    (x : ↥(pullback (projModelStrCR W) (𝟙 (base (T := T)))))
    (hx : x ∈ ((basisDivisor G q P Q).support : Set ↥(pullback (projModelStrCR W) (𝟙 (base (T := T)))))) :
    ∃ a b : ℕ, a < q ∧ b < q ∧
      x ⤳ (graphOver (projModelStrCR W) (linComb G P Q a b).1 (linComb G P Q a b).2).base
        (IsLocalRing.closedPoint T) := by
  classical

  change x ∈ (prodKerGraph (projModelStrCR W) (basisTuple G q P Q) (basisTuple_over G q P Q)).support at hx
  rw [prodKerGraph_eq_prod] at hx
  obtain ⟨i, -, hxi⟩ := exists_mem_support_of_mem_support_prod _ _ hx

  obtain ⟨t, rfl⟩ := support_ker_subset_range _ hxi
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; exact absurd i.isLt (by simp)
    · exact h
  refine ⟨i.val / q, i.val % q, Nat.div_lt_of_lt_mul i.isLt, Nat.mod_lt _ hq, ?_⟩

  exact (IsLocalRing.specializes_closedPoint t).map
    (graphOver (projModelStrCR W) (basisTuple G q P Q i) (basisTuple_over G q P Q i)).base.hom.continuous

end S_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_specializes_graphOver_closedPoint_of_mem_support_basisDivisor (solution)
