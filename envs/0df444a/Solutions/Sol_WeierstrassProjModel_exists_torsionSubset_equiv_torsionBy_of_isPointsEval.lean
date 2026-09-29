-- Prove2me | solution 1 for WeierstrassProjModel.exists_torsionSubset_equiv_torsionBy_of_isPointsEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/858fedf3-5ce8-5941-b0ce-3c7532c3fc08

import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.Algebra.Module.Torsion.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel

universe u

section IsPointsEvalEngine

variable {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}
  {G : RelativeGroupLaw R (projModelStrCR V)}
  {ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
      (V.baseChange F).toAffine.Point}
  (h : IsPointsEval V G ev)
  (F : Type u) [Field F] [DecidableEq F] [Algebra R F]

include h in
private theorem map_one' : ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap R F)))) = 0 := by
  have h1 := h.1 F (G.one _) (G.one _)
  rw [G.one_mul] at h1
  have h2 : ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap R F)))) +
      ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap R F)))) =
      ev F (G.one (Spec.map (CommRingCat.ofHom (algebraMap R F)))) + 0 := by
    rw [add_zero]; exact h1.symm
  exact add_left_cancel h2

include h in
private theorem map_nsmul' (d : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V)) :
    ev F (G.nsmul (Spec.map (CommRingCat.ofHom (algebraMap R F))) d x) = d • ev F x := by
  induction d with
  | zero => rw [RelativeGroupLaw.nsmul_zero, map_one' h F, zero_nsmul]
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, h.1 F, ih, succ_nsmul]

include h in
private theorem mem_torsionSubset_iff' (d : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V)) :
    x ∈ G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d ↔
      ev F x ∈ Submodule.torsionBy ℤ (V.baseChange F).toAffine.Point (d : ℤ) := by
  rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul, ← map_nsmul' h F, ← map_one' h F]
  exact (ev F).injective.eq_iff.symm

include h in
private def torsionEquiv' (d : ℕ) :
    ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d) ≃
      ↥(Submodule.torsionBy ℤ (V.baseChange F).toAffine.Point (d : ℤ)) :=
  Equiv.subtypeEquiv (ev F) (mem_torsionSubset_iff' h F d)

end IsPointsEvalEngine

theorem solution
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R)
    (G : RelativeGroupLaw R (projModelStrCR V))
    (ev : ∀ (F : Type u) [Field F] [DecidableEq F] [Algebra R F],
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R F))) (projModelStrCR V) ≃
        (V.baseChange F).toAffine.Point)
    (hev : IsPointsEval V G ev)
    (F : Type u) [Field F] [DecidableEq F] [Algebra R F] (d : ℕ) :
    ∃ e : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d) ≃
        ↥(Submodule.torsionBy ℤ (V.baseChange F).toAffine.Point (d : ℤ)),
      (∀ x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          (e x : (V.baseChange F).toAffine.Point) = ev F x.1) ∧
      (∀ (x y : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d))
          (hxy : G.mul (Spec.map (CommRingCat.ofHom (algebraMap R F))) x.1 y.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          e ⟨_, hxy⟩ = e x + e y) ∧
      (∀ (σ : F ≃ₐ[R] F)
          (x : ↥(G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d))
          (hσx : galTwist σ x.1 ∈
            G.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R F))) d),
          (e ⟨_, hσx⟩ : (V.baseChange F).toAffine.Point) =
            WeierstrassCurve.Affine.Point.map (σ : F →ₐ[R] F)
              (e x : (V.baseChange F).toAffine.Point)) := by
  refine ⟨torsionEquiv' hev F d, fun x => rfl, fun x y hxy => ?_, fun σ x hσx => ?_⟩
  · exact Subtype.ext (hev.1 F x.1 y.1)
  · exact hev.2 F σ x.1

end

end S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval
end P2MW
export P2MW.S_WeierstrassProjModel_exists_torsionSubset_equiv_torsionBy_of_isPointsEval (solution)
