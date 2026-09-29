-- Prove2me | solution 1 for Rep.finrank_hom_eq_add_of_shortExact_of_card_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6b6af724-9bb6-538b-87c6-d5af1102ffda

import Mathlib
import Theorems.Thm_Representation_finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module"
open scoped Classical

theorem solution
    {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H] (hH : (Nat.card H).Coprime p)
    (T : Rep.{0} (ZMod p) H) [FiniteDimensional (ZMod p) T]
    (X : ShortComplex (Rep.{0} (ZMod p) H)) (hX : X.ShortExact) [FiniteDimensional (ZMod p) X.X₂] :
    Module.finrank (ZMod p) (T ⟶ X.X₂) =
      Module.finrank (ZMod p) (T ⟶ X.X₁) + Module.finrank (ZMod p) (T ⟶ X.X₃) := by
  haveI : Fintype H := Fintype.ofFinite H
  have hunit : IsUnit ((Fintype.card H : ZMod p)) := by
    rw [ZMod.isUnit_iff_coprime, Fintype.card_eq_nat_card]; exact hH
  have hinj : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  have hsurj : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hrk : LinearMap.range X.f.hom.toLinearMap = LinearMap.ker X.g.hom.toLinearMap :=
    (hX.map_of_exact (forget₂ (Rep (ZMod p) H) (ModuleCat (ZMod p)))).exact.moduleCat_range_eq_ker
  have hexact : Function.Exact X.f.hom.toLinearMap X.g.hom.toLinearMap := LinearMap.exact_iff.2 hrk.symm
  have key := Representation.finrank_invariants_linHom_eq_add_of_exact_of_isUnit_card hunit
    T.ρ X.X₁.ρ X.X₂.ρ X.X₃.ρ X.f.hom.toLinearMap X.g.hom.toLinearMap
    (fun d => LinearMap.ext fun a => Rep.hom_comm_apply X.f d a)
    (fun d => LinearMap.ext fun b => Rep.hom_comm_apply X.g d b) hinj hsurj hexact
  rw [← (Representation.linHom.invariantsEquivRepHom T X.X₂).finrank_eq,
    ← (Representation.linHom.invariantsEquivRepHom T X.X₁).finrank_eq,
    ← (Representation.linHom.invariantsEquivRepHom T X.X₃).finrank_eq]
  exact key

end S_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime
end P2MW
export P2MW.S_Rep_finrank_hom_eq_add_of_shortExact_of_card_coprime (solution)
