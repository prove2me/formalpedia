-- Prove2me | solution 1 for Representation.exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ad2877bc-d829-5a02-8a38-a8c76f0b6178

import Mathlib
import Theorems.Thm_Representation_exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
import Theorems.Thm_Module_exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation
import Theorems.Thm_LinearMap_baseChange_free_finrank_two_and_span_eq_top_and_trace_eq
import Theorems.Thm_LinearMap_exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped TensorProduct

set_option autoImplicit false

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    {R : Type} [CommRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R] [IsReduced R]
    {G : Type} [Group G]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (hV : Module.finrank R V = 2)
    (ρV : G →* Module.End R V) (hspan : Submodule.span R (Set.range ⇑ρV) = ⊤)
    {Y : Type} [AddCommGroup Y] [Module R Y] [Module 𝒪 Y] [IsScalarTower 𝒪 R Y]
    [Module.Finite 𝒪 Y] [Module.IsTorsionFree 𝒪 Y]
    (hfaith : ∀ x : R, (∀ y : Y, x • y = 0) → x = 0)
    (ρY : G →* Module.End R Y)
    {Δ : Type} [CommGroup Δ] [Finite Δ] (D : Δ →* Module.End R Y)
    (hD : ∀ (d : Δ) (g : G), D d * ρY g = ρY g * D d)
    (δ : G →* Δ) (c : G →* Rˣ)
    (hrel : ∀ g : G,
      ρY g * ρY g - (LinearMap.trace R V (ρV g)) • ρY g + ((c g : Rˣ) : R) • D (δ g) = 0) :
    ∃ j : V →ₗ[R] Y, Function.Injective j ∧ ∀ (g : G) (v : V), j (ρV g v) = ρY g (j v) := by
  classical
  obtain ⟨k, _, _, _, _, _, _, _, hinj, hunit, M, _, _, _, _, _, _, _, _, hfaithM, ρM, dM, hrelM, ι, hι, hιeq, hloc⟩ :=
    Module.exists_isArtinianRing_isReduced_faithful_baseChange_of_quadraticRelation (𝒪 := 𝒪) hfaith ρY D hD δ c
      (fun g => LinearMap.trace R V (ρV g)) hrel

  haveI : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exfalso
      have : Module.finrank R V = 1 := by simp [Module.finrank]
      omega
    · exact h
  haveI : Nontrivial k := Function.Injective.nontrivial hinj

  obtain ⟨hVk, hspank, htrk, hintk, hinjk⟩ :=
    LinearMap.baseChange_free_finrank_two_and_span_eq_top_and_trace_eq (k := k) hV ρV hspan
  let ρVk : G →* Module.End k (k ⊗[R] V) :=
    { toFun := fun g => (ρV g).baseChange k
      map_one' := by rw [map_one]; exact LinearMap.baseChange_one R V
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.baseChange_mul _ _ }
  have hρVk : ∀ g, ρVk g = (ρV g).baseChange k := fun g => rfl
  have hspank' : Submodule.span k (Set.range ⇑ρVk) = ⊤ := hspank
  have hrelM' : ∀ g : G, ρM g * ρM g - (LinearMap.trace k (k ⊗[R] V) (ρVk g)) • ρM g +
      ((dM g : kˣ) : k) • (1 : Module.End k M) = 0 := by
    intro g
    rw [hρVk, htrk]
    exact hrelM g
  obtain ⟨Jk, hJk, hJkeq⟩ :=
    Representation.exists_injective_equivariant_of_quadraticRelation_of_isArtinianRing_of_isReduced
      hVk ρVk hspank' hfaithM ρM dM hrelM'

  let J : V →ₗ[R] M := (Jk.restrictScalars R).comp (TensorProduct.mk R k V 1)
  have hJapply : ∀ v : V, J v = Jk ((1 : k) ⊗ₜ[R] v) := fun v => rfl
  have hJ : Function.Injective J := by
    intro v w hvw
    rw [hJapply, hJapply] at hvw
    exact hinjk hinj (hJk hvw)
  have hJeq : ∀ (g : G) (v : V), J (ρV g v) = ρM g (J v) := by
    intro g v
    rw [hJapply, hJapply, ← hintk, ← hρVk, hJkeq]

  letI : Module 𝒪 V := Module.compHom V (algebraMap 𝒪 R)
  haveI : IsScalarTower 𝒪 R V := ⟨fun a r v => by
    show (a • r) • v = (algebraMap 𝒪 R a) • (r • v)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : Module.Finite 𝒪 V := Module.Finite.trans R V
  have htf : ∀ (a : 𝒪) (m : M), a ≠ 0 → a • m = 0 → m = 0 := by
    intro a m ha h
    obtain ⟨u, hu⟩ := hunit a ha
    rw [← algebraMap_smul k a m, ← hu] at h
    simpa using congrArg (fun x => (↑u⁻¹ : k) • x) h
  obtain ⟨a, ha, j, hj, hjι⟩ :=
    LinearMap.exists_injective_comp_eq_smul_of_forall_exists_smul_mem_range htf ι hι hloc J hJ
  refine ⟨j, hj, fun g v => hι ?_⟩
  rw [hιeq, hjι, hjι, hJeq, ← algebraMap_smul k a (J v), ← algebraMap_smul k a (ρM g (J v)), map_smul]

end S_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced
end P2MW
export P2MW.S_Representation_exists_injective_equivariant_of_quadraticRelation_of_faithful_of_isReduced (solution)
