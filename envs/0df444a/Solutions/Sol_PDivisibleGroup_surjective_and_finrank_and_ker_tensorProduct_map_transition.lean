-- Prove2me | solution 1 for PDivisibleGroup.surjective_and_finrank_and_ker_tensorProduct_map_transition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2065b662-7c82-55cb-82bb-fdb0e42f8f76

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Theorems.Thm_PDivisibleGroup_Hopf_map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u v w

open scoped TensorProduct

open scoped TensorProduct

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.torsionIdeal transition_surjective transition finrank_level ker_transition level"
namespace Hopf
p2m_export "PDivisibleGroup.Hopf" "nsmulAlgHom augIdeal mem_augIdeal_iff torsionIdeal map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange"
namespace BaseChangeZp
p2m_open "PDivisibleGroup.Hopf PDivisibleGroup"

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (A : Type*) [CommRing A] [Bialgebra R A]

theorem counitAlgHom_surjective : Function.Surjective (Bialgebra.counitAlgHom R A) := fun r =>
  ⟨algebraMap R A r, by rw [Bialgebra.counitAlgHom_apply]; exact Bialgebra.counit_algebraMap r⟩

theorem counit_eq_rid_map (z : S ⊗[R] A) :
    Coalgebra.counit (R := S) z =
      Algebra.TensorProduct.rid R S S (Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.counitAlgHom R A) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s a =>
    rw [TensorProduct.counit_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul, AlgHom.id_apply,
      Bialgebra.counitAlgHom_apply, CommSemiring.counit_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem augIdeal_baseChange :
    augIdeal S (S ⊗[R] A) = (augIdeal R A).map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) := by
  have hker := Algebra.TensorProduct.lTensor_ker (A := S) (Bialgebra.counitAlgHom R A) (counitAlgHom_surjective R A)
  ext z
  rw [mem_augIdeal_iff, counit_eq_rid_map, EmbeddingLike.map_eq_zero_iff, ← RingHom.mem_ker,
    show augIdeal R A = RingHom.ker (Bialgebra.counitAlgHom R A) from rfl, ← hker]

  rfl

theorem torsionIdeal_baseChange (n : ℕ) :
    torsionIdeal S (S ⊗[R] A) n =
      (torsionIdeal R A n).map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) := by
  have hcomm : ∀ a : A, nsmulAlgHom S (S ⊗[R] A) n ((1 : S) ⊗ₜ[R] a) = (1 : S) ⊗ₜ[R] nsmulAlgHom R A n a := fun a => by
    rw [← map_id_nsmulAlgHom_eq_nsmulAlgHom_baseChange, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [torsionIdeal, torsionIdeal, augIdeal_baseChange]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, hcomm]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Algebra.TensorProduct.includeRight_apply, ← hcomm]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)

theorem ker_map_id (B : Type*) [CommRing B] [Bialgebra R B] (t : A →ₐc[R] B) (ht : Function.Surjective t) :
    RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id S S) t) =
      (RingHom.ker t).map (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) := by
  exact Algebra.TensorProduct.lTensor_ker (A := S) (t : A →ₐ[R] B) ht

theorem map_id_surjective (B : Type*) [CommRing B] [Bialgebra R B] (t : A →ₐc[R] B) (ht : Function.Surjective t) :
    Function.Surjective (Bialgebra.TensorProduct.map (BialgHom.id S S) t) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s b =>
    obtain ⟨a, rfl⟩ := ht b
    exact ⟨s ⊗ₜ a, by rw [Bialgebra.TensorProduct.map_tmul]; rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end PDivisibleGroup.Hopf.BaseChangeZp

theorem solution
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] {h : ℕ} (H : PDivisibleGroup O p h)
    (k : Type) [CommRing k] [Nontrivial k] [Algebra O k] :
    (∀ v : ℕ, Function.Surjective
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (H.transition v))) ∧
    (∀ v : ℕ, Module.finrank k (k ⊗[O] H.level v) = p ^ (v * h)) ∧
    (∀ v : ℕ, RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id k k) (H.transition v)) =
      PDivisibleGroup.Hopf.torsionIdeal k (k ⊗[O] H.level (v + 1)) (p ^ v)) := by
  classical
  haveI : Nontrivial O := (algebraMap O k).domain_nontrivial
  refine ⟨fun v => PDivisibleGroup.Hopf.BaseChangeZp.map_id_surjective O k _ _ (H.transition v)
    (H.transition_surjective v), fun v => ?_, fun v => ?_⟩
  · rw [Module.finrank_baseChange, H.finrank_level]
  · rw [PDivisibleGroup.Hopf.BaseChangeZp.ker_map_id O k _ _ (H.transition v) (H.transition_surjective v),
      PDivisibleGroup.Hopf.BaseChangeZp.torsionIdeal_baseChange]
    exact congrArg _ (H.ker_transition v)

end S_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition
end P2MW
export P2MW.S_PDivisibleGroup_surjective_and_finrank_and_ker_tensorProduct_map_transition (solution)
