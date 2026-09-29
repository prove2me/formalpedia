-- Prove2me | solution 1 for WeierstrassProjModel.RelativeGroupLaw.exists_goodReductionJacobian_mul_eq_and_nsmul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/28363a11-afcb-59b4-805a-30c4d1ee5cb2

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory NeronModelInfra

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "RelativeGroupLaw RelativeGroupLaw.nsmul_succ"
namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul nsmul_succ mul_one inv_mul_cancel mul_assoc one_mul inv mul mul_natural one"
p2m_open "WeierstrassProjModel.RelativeGroupLaw WeierstrassProjModel"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

private def _root_.WeierstrassProjModel.RelativeGroupLaw.toGRJ (G : RelativeGroupLaw R f) : GoodReductionJacobian.RelativeGroupLaw R f where
  mul := G.mul
  one := G.one
  inv := G.inv
  mul_assoc := G.mul_assoc
  one_mul := G.one_mul
  mul_one := G.mul_one
  inv_mul_cancel := G.inv_mul_cancel
  mul_natural := fun t t' ψ hψ x y => G.mul_natural t t' ψ hψ x y

p2m_export "WeierstrassProjModel.RelativeGroupLaw" "toGRJ"
theorem toGRJ_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : G.toGRJ.nsmul t n x = G.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, nsmul_succ, ih]
    rfl

end WeierstrassProjModel.RelativeGroupLaw

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : WeierstrassProjModel.RelativeGroupLaw R f) :
    ∃ G' : GoodReductionJacobian.RelativeGroupLaw R f,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), G'.mul t x y = G.mul t x y) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), G'.one t = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f), G'.inv t x = G.inv t x) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f),
        G'.nsmul t n x = G.nsmul t n x) := by
  exact ⟨G.toGRJ, fun t x y => rfl, fun t => rfl, fun t x => rfl,
    fun t n x => WeierstrassProjModel.RelativeGroupLaw.toGRJ_nsmul G t n x⟩

end S_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq
end P2MW
export P2MW.S_WeierstrassProjModel_RelativeGroupLaw_exists_goodReductionJacobian_mul_eq_and_nsmul_eq (solution)
