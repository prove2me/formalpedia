-- Prove2me | solution 1 for PDivisibleGroup.specialFibre_tower_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/729b3f55-5504-504a-a40c-39a7c828412d

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_specialFibre_tower_of_isLocalRing

set_option autoImplicit false

open scoped TensorProduct
open Function

universe u v

namespace BCTowerBody

open PDivisibleGroup.Hopf

section Fibre

variable {𝓞 : Type*} [CommRing 𝓞] {κ : Type*} [CommRing κ] [Algebra 𝓞 κ]
variable {A : Type*} [CommRing A]

theorem includeRight_surjective [Algebra 𝓞 A] (hκ : Surjective (algebraMap 𝓞 κ)) :
    Surjective (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul c a =>
    obtain ⟨o, rfl⟩ := hκ c
    refine ⟨o • a, ?_⟩
    rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, map_add _ _ _⟩

theorem ker_map_id (B : Type*) [CommRing B] [Algebra 𝓞 A] [Algebra 𝓞 B] (t : A →ₐ[𝓞] B)
    (ht : Surjective t) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id κ κ) t) =
      (RingHom.ker t).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  rw [← Algebra.TensorProduct.lTensor_ker t ht]
  ext x
  exact Iff.rfl

variable [Bialgebra 𝓞 A]

theorem counit_tmul' (c : κ) (a : A) :
    Coalgebra.counit (R := κ) (c ⊗ₜ[𝓞] a) = algebraMap 𝓞 κ (Coalgebra.counit (R := 𝓞) a) * c := by
  rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def]

theorem counit_eq_rid_map (x : κ ⊗[𝓞] A) :
    Coalgebra.counit (R := κ) x =
      Algebra.TensorProduct.rid 𝓞 𝓞 κ
        (Algebra.TensorProduct.map (AlgHom.id 𝓞 κ) (Bialgebra.counitAlgHom 𝓞 A) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    rw [counit_tmul', Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul,
      Bialgebra.counitAlgHom_apply, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem counitAlgHom_surjective : Surjective (Bialgebra.counitAlgHom 𝓞 A) := fun r =>
  ⟨algebraMap 𝓞 A r, by rw [Bialgebra.counitAlgHom_apply, Bialgebra.counit_algebraMap]⟩

theorem augIdeal_baseChange :
    augIdeal κ (κ ⊗[𝓞] A) = (augIdeal 𝓞 A).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  have hker : (augIdeal 𝓞 A).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id 𝓞 κ) (Bialgebra.counitAlgHom 𝓞 A)) :=
    (Algebra.TensorProduct.lTensor_ker _ counitAlgHom_surjective).symm
  ext x
  rw [mem_augIdeal_iff, hker, RingHom.mem_ker, counit_eq_rid_map,
    map_eq_zero_iff _ (Algebra.TensorProduct.rid 𝓞 𝓞 κ).injective]

theorem nsmulAlgHom_comp_includeRight (n : ℕ) :
    ((nsmulAlgHom κ (κ ⊗[𝓞] A) n : κ ⊗[𝓞] A →+* κ ⊗[𝓞] A)).comp
        (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) =
      ((Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) : A →+* κ ⊗[𝓞] A).comp
        (nsmulAlgHom 𝓞 A n : A →+* A) := by
  refine RingHom.ext fun a => ?_
  change nsmulAlgHom κ (κ ⊗[𝓞] A) n ((1 : κ) ⊗ₜ[𝓞] a) = (1 : κ) ⊗ₜ[𝓞] nsmulAlgHom 𝓞 A n a
  rw [← PDivisibleGroup.Hopf.map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange 𝓞 κ A n,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem torsionIdeal_baseChange (n : ℕ) :
    torsionIdeal κ (κ ⊗[𝓞] A) n =
      (torsionIdeal 𝓞 A n).map (Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) := by
  rw [torsionIdeal, torsionIdeal, augIdeal_baseChange]
  change ((augIdeal 𝓞 A).map
      ((Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) : A →+* κ ⊗[𝓞] A)).map
      (nsmulAlgHom κ (κ ⊗[𝓞] A) n : κ ⊗[𝓞] A →+* κ ⊗[𝓞] A) =
    ((augIdeal 𝓞 A).map (nsmulAlgHom 𝓞 A n : A →+* A)).map
      ((Algebra.TensorProduct.includeRight : A →ₐ[𝓞] κ ⊗[𝓞] A) : A →+* κ ⊗[𝓞] A)
  rw [Ideal.map_map, Ideal.map_map, nsmulAlgHom_comp_includeRight]

theorem ker_map_eq_torsionIdeal {B : Type*} [CommRing B] [Bialgebra 𝓞 B] (t : A →ₐc[𝓞] B)
    (ht : Surjective t) (n : ℕ) (hker : RingHom.ker t = torsionIdeal 𝓞 A n) :
    RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id κ κ) t) =
      torsionIdeal κ (κ ⊗[𝓞] A) n := by
  have h1 : RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id κ κ) t) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id κ κ) (t : A →ₐ[𝓞] B)) := by
    ext x
    exact Iff.rfl
  rw [h1, ker_map_id B (t : A →ₐ[𝓞] B) ht, torsionIdeal_baseChange]
  congr 1

end Fibre

end BCTowerBody

open BCTowerBody in
theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v)) :
    (∀ v, Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v))) ∧
    (∀ v, Module.finrank (ZMod p) (ZMod p ⊗[𝓞] R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t₀ v)) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (ZMod p ⊗[𝓞] R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, IsLocalRing (ZMod p ⊗[𝓞] R₀ v)) := by
  have hk : Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  haveI : Nontrivial 𝓞 := by
    haveI := hconn 0
    exact Module.nontrivial 𝓞 (R₀ 0)
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  ·
    exact Algebra.TensorProduct.map_surjective (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v)
      surjective_id (ht₀ v)
  ·
    rw [Module.finrank_baseChange, hrank₀]
  ·
    exact ker_map_eq_torsionIdeal (t₀ v) (ht₀ v) (p ^ v) (hker₀ v)
  ·
    haveI := hconn v
    haveI : Module.FaithfullyFlat 𝓞 (R₀ v) := inferInstance
    haveI : Nontrivial ((ZMod p) ⊗[𝓞] R₀ v) := inferInstance
    exact IsLocalRing.of_surjective'
      (Algebra.TensorProduct.includeRight : R₀ v →ₐ[𝓞] (ZMod p) ⊗[𝓞] R₀ v).toRingHom
      (includeRight_surjective hk)

end S_PDivisibleGroup_specialFibre_tower_of_isLocalRing
end P2MW
export P2MW.S_PDivisibleGroup_specialFibre_tower_of_isLocalRing (solution)
