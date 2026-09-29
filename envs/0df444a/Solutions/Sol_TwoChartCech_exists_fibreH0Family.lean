-- Prove2me | solution 1 for TwoChartCech.exists_fibreH0Family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/41546044-cc14-5e09-ae94-8edf2bae77e2

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_CoherentBaseChangeFamily
import Theorems.Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
import Theorems.Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension
import Theorems.Thm_TwoChartCech_nonempty_kerBaseChangeTowerEquiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_exists_fibreH0Family

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace TwoChartCech
p2m_export "TwoChartCech" "exists_twoTermComplex_kerMapBaseChange_bijective finrank_ker_baseChange_eq_of_field_extension nonempty_kerBaseChangeTowerEquiv"
p2m_open "TwoChartCech"
namespace Family

def baseChangeTTC {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, u} R)
    (S : Type u) [CommRing S] [Algebra R S] : CoherentBaseChange.TwoTermComplex.{u, u} S :=
  haveI : Module.Finite S (S ⊗[R] G.C0) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R G.C0))
  haveI : Module.Finite S (S ⊗[R] G.C1) :=
    Module.Finite.of_basis (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R G.C1))
  { C0 := S ⊗[R] G.C0, C1 := S ⊗[R] G.C1, d := G.d.baseChange S }

@[reducible] def algebraOfHom' {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U : T.Opens) :
    Algebra R Γ(T, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

theorem specMap_algebraMap_eq {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U : T.Opens)
    (hU : IsAffineOpen U) :
    letI := algebraOfHom' f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, U))) = hU.fromSpec ≫ f := by
  letI := algebraOfHom' f U
  have halg : (algebraMap R Γ(T, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ f ⁻¹ᵁ ⊤)]

theorem base_eq_comap {R : Type u} [CommRing R] {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) (U : T.Opens)
    (hU : IsAffineOpen U) (x : U) :
    letI := algebraOfHom' f U
    f.base x.1 = PrimeSpectrum.comap (algebraMap R Γ(T, U)) (hU.primeIdealOf x) := by
  letI := algebraOfHom' f U
  have h1 : f.base x.1 = (hU.fromSpec ≫ f).base (hU.primeIdealOf x) := by
    rw [Scheme.Hom.comp_base, TopCat.comp_app, hU.fromSpec_primeIdealOf x]
  rw [h1, ← specMap_algebraMap_eq f U hU]
  rfl

end Family

open Family

theorem exists_fibreH0Family'
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) := by
  obtain ⟨G, ι0, ι1, comm, hG⟩ := exists_twoTermComplex_kerMapBaseChange_bijective d
  refine ⟨{ G := fun U hU => letI := algebraOfHom' f U; baseChangeTTC G Γ(T, U)
            h0 := fun x => Module.finrank (f.base x).asIdeal.ResidueField
              (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField))
            hglue := ?_ }, fun x => rfl⟩
  intro U hU x
  letI := algebraOfHom' f U

  let 𝔮 : PrimeSpectrum Γ(T, U) := hU.primeIdealOf x
  let 𝔭 : PrimeSpectrum R := f.base x.1
  have hpq : 𝔭.asIdeal = Ideal.comap (algebraMap R Γ(T, U)) 𝔮.asIdeal := by
    show (f.base x.1).asIdeal = _
    rw [base_eq_comap f U hU x]; rfl

  let φ : 𝔭.asIdeal.ResidueField →ₐ[R] 𝔮.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ 𝔭.asIdeal 𝔮.asIdeal (Algebra.ofId R Γ(T, U)) hpq
  letI : Algebra 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm

  rw [finrank_ker_baseChange_eq_of_field_extension d 𝔭.asIdeal.ResidueField 𝔮.asIdeal.ResidueField]

  rw [← (LinearEquiv.ofBijective _ (hG 𝔮.asIdeal.ResidueField)).finrank_eq]

  obtain ⟨e, -⟩ := nonempty_kerBaseChangeTowerEquiv G.d Γ(T, U) 𝔮.asIdeal.ResidueField
  rw [← e.finrank_eq]
  rfl

end TwoChartCech

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of R)) :
    ∃ F : CoherentBaseChange.FibreH0Family T,
      ∀ x : T, F.h0 x = Module.finrank (f.base x).asIdeal.ResidueField
        (LinearMap.ker (d.baseChange (f.base x).asIdeal.ResidueField)) :=
  TwoChartCech.exists_fibreH0Family' d f

end

end S_TwoChartCech_exists_fibreH0Family
end P2MW
export P2MW.S_TwoChartCech_exists_fibreH0Family (solution)
