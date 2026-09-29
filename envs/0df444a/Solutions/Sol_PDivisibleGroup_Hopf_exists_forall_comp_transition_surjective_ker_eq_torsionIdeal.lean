-- Prove2me | solution 1 for PDivisibleGroup.Hopf.exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dd763f78-773c-50d4-a581-cf97a54d3188

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

namespace K5preTower

universe u v w

structure Tower (R : Type u) [CommRing R] (p h : ℕ) where
  level : ℕ → Type v
  [instCommRing : ∀ v, CommRing (level v)]
  [instHopfAlgebra : ∀ v, HopfAlgebra R (level v)]
  [instIsCocomm : ∀ v, Coalgebra.IsCocomm R (level v)]
  [instModuleFinite : ∀ v, Module.Finite R (level v)]
  [instModuleFree : ∀ v, Module.Free R (level v)]
  transition : ∀ v, level (v + 1) →ₐc[R] level v
  transition_surjective : ∀ v, Function.Surjective (transition v)
  finrank_level : ∀ v, Module.finrank R (level v) = p ^ (v * h)
  ker_transition : ∀ v,
    RingHom.ker (transition v) = PDivisibleGroup.Hopf.torsionIdeal R (level (v + 1)) (p ^ v)

attribute [scoped instance] Tower.instCommRing Tower.instHopfAlgebra Tower.instIsCocomm
  Tower.instModuleFinite Tower.instModuleFree

namespace Tower

open PDivisibleGroup

variable {R : Type u} [CommRing R] {p h : ℕ} (G : Tower R p h)

def height (_G : Tower R p h) : ℕ := h

@[scoped simp] theorem height_eq : G.height = h := rfl

scoped instance instModuleFlat (v : ℕ) : Module.Flat R (G.level v) := inferInstance

abbrev transitionAlgHom (v : ℕ) : G.level (v + 1) →ₐ[R] G.level v :=
  (G.transition v : G.level (v + 1) →ₐ[R] G.level v)

theorem transitionAlgHom_apply (v : ℕ) (a : G.level (v + 1)) :
    G.transitionAlgHom v a = G.transition v a := rfl

theorem transitionAlgHom_surjective (v : ℕ) : Function.Surjective (G.transitionAlgHom v) :=
  G.transition_surjective v

@[scoped simp] theorem counit_transition (v : ℕ) (a : G.level (v + 1)) :
    counit (R := R) (G.transition v a) = counit (R := R) a :=
  CoalgHomClass.counit_comp_apply _ a

theorem finrank_level_zero : Module.finrank R (G.level 0) = 1 := by
  rw [G.finrank_level 0, zero_mul, pow_zero]

theorem mem_ker_transition_iff (v : ℕ) (a : G.level (v + 1)) :
    G.transition v a = 0 ↔ a ∈ Hopf.torsionIdeal R (G.level (v + 1)) (p ^ v) := by
  rw [← G.ker_transition v, RingHom.mem_ker]

theorem transition_nsmulAlgHom_eq_zero (v : ℕ) {a : G.level (v + 1)}
    (ha : a ∈ Hopf.augIdeal R (G.level (v + 1))) :
    G.transition v (Hopf.nsmulAlgHom R (G.level (v + 1)) (p ^ v) a) = 0 :=
  (G.mem_ker_transition_iff v _).2 (Hopf.nsmulAlgHom_mem_torsionIdeal R _ ha _)

theorem nsmulAlgHom_transition (v n : ℕ) (a : G.level (v + 1)) :
    Hopf.nsmulAlgHom R (G.level v) n (G.transition v a) =
      G.transition v (Hopf.nsmulAlgHom R (G.level (v + 1)) n a) :=
  Hopf.nsmulAlgHom_bialgHom_apply (G.transition v) n a

theorem nsmulAlgHom_pow_level (v : ℕ) :
    Hopf.nsmulAlgHom R (G.level v) (p ^ v) =
      (Algebra.ofId R (G.level v)).comp (counitAlgHom R (G.level v)) := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := G.transition_surjective v b
  have hdec : a = algebraMap R _ (counit (R := R) a) + (a - algebraMap R _ (counit (R := R) a)) := by
    abel
  rw [G.nsmulAlgHom_transition]
  conv_lhs => rw [hdec]
  rw [map_add, map_add, Hopf.nsmulAlgHom_algebraMap,
    G.transition_nsmulAlgHom_eq_zero v (Hopf.sub_algebraMap_counit_mem_augIdeal R _ a),
    add_zero, AlgHom.comp_apply, Algebra.ofId_apply, Bialgebra.counitAlgHom_apply, G.counit_transition]
  exact (G.transitionAlgHom v).commutes _

theorem nsmulAlgHom_pow_level_apply (v : ℕ) (b : G.level v) :
    Hopf.nsmulAlgHom R (G.level v) (p ^ v) b = algebraMap R (G.level v) (counit (R := R) b) := by
  rw [G.nsmulAlgHom_pow_level v]
  rfl

theorem toConv_linearMapId_pow_level (v : ℕ) :
    (toConv (LinearMap.id : G.level v →ₗ[R] G.level v)) ^ (p ^ v) = 1 := by
  rw [← Hopf.toConv_toLinearMap_nsmulAlgHom, G.nsmulAlgHom_pow_level v]
  rfl

theorem point_pow_eq_one (v : ℕ) {L : Type w} [CommRing L] [Algebra R L]
    (f : WithConv (G.level v →ₐ[R] L)) : f ^ (p ^ v) = 1 := by
  have h := Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom f.ofConv (p ^ v)
  rw [toConv_ofConv] at h
  rw [h, G.nsmulAlgHom_pow_level v, AlgHom.convOne_def, ← AlgHom.comp_assoc, Algebra.comp_ofId]

theorem comp_transition_injective (v : ℕ) {L : Type w} [CommRing L] [Algebra R L] :
    Function.Injective fun g : G.level v →ₐ[R] L => g.comp (G.transitionAlgHom v) := by
  intro g g' hgg'
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := G.transition_surjective v b
  exact DFunLike.congr_fun hgg' a

theorem exists_comp_transition_eq (v : ℕ) {L : Type w} [CommRing L] [Algebra R L]
    (f : WithConv (G.level (v + 1) →ₐ[R] L)) (hf : f ^ (p ^ v) = 1) :
    ∃ g : G.level v →ₐ[R] L, g.comp (G.transitionAlgHom v) = f.ofConv := by
  have hle : RingHom.ker (G.transitionAlgHom v).toRingHom ≤ RingHom.ker f.ofConv.toRingHom := by
    intro a ha
    have ha' : a ∈ Hopf.torsionIdeal R (G.level (v + 1)) (p ^ v) := by
      rw [← G.ker_transition v]
      exact ha
    exact Hopf.apply_eq_zero_of_mem_torsionIdeal_of_pow_eq_one R _ f (p ^ v) hf ha'
  exact ⟨AlgHom.liftOfSurjective (G.transitionAlgHom v) (G.transition_surjective v) f.ofConv hle,
    AlgHom.liftOfSurjective_comp _ _ _ _⟩

theorem exists_comp_transition_eq_iff (v : ℕ) {L : Type w} [CommRing L] [Algebra R L]
    (f : WithConv (G.level (v + 1) →ₐ[R] L)) :
    (∃ g : G.level v →ₐ[R] L, g.comp (G.transitionAlgHom v) = f.ofConv) ↔ f ^ (p ^ v) = 1 := by
  refine ⟨?_, G.exists_comp_transition_eq v f⟩
  rintro ⟨g, hg⟩
  have hf : f = toConv (g.comp (G.transitionAlgHom v)) := by rw [hg, toConv_ofConv]
  rw [hf, ← WithConv.ofConv_injective.eq_iff]
  rw [show toConv (g.comp (G.transitionAlgHom v)) = toConv ((toConv g).ofConv.comp (G.transitionAlgHom v))
      from rfl, ← Hopf.convPow_comp_bialgHom, G.point_pow_eq_one v (toConv g)]
  rw [AlgHom.convOne_def, AlgHom.convOne_def]
  change ((Algebra.ofId R L).comp (counitAlgHom R (G.level v))).comp (G.transitionAlgHom v) = _
  refine AlgHom.ext fun a => ?_
  change algebraMap R L (counit (R := R) (G.transition v a)) = algebraMap R L (counit (R := R) a)
  rw [G.counit_transition]

end Tower
p2m_reactivate "P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.K5preTower.Tower"

namespace Tower

open PDivisibleGroup

variable {R : Type u} [CommRing R] {p h : ℕ} (G : Tower R p h)

def T (v : ℕ) : (w : ℕ) → G.level (v + w) →ₐc[R] G.level v
  | 0 => BialgHom.id R (G.level v)
  | w + 1 => (T v w).comp (G.transition (v + w))

@[scoped simp] theorem T_zero (v : ℕ) : G.T v 0 = BialgHom.id R (G.level v) := rfl

theorem T_succ (v w : ℕ) : G.T v (w + 1) = (G.T v w).comp (G.transition (v + w)) := rfl

theorem T_surjective (v : ℕ) : ∀ w, Function.Surjective (G.T v w)
  | 0 => Function.surjective_id
  | w + 1 => by
    rw [T_succ, BialgHom.coe_comp]
    exact (T_surjective v w).comp (G.transition_surjective (v + w))

theorem nsmulAlgHom_comp_nsmulAlgHom {A : Type w} [CommRing A] [Bialgebra R A] (m n : ℕ) :
    (Hopf.nsmulAlgHom R A m).comp (Hopf.nsmulAlgHom R A n) = Hopf.nsmulAlgHom R A (m * n) := by
  rw [Hopf.nsmulAlgHom_mul]
  apply WithConv.toConv_injective
  rw [toConv_ofConv]
  exact (Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom (Hopf.nsmulAlgHom R A m) n).symm

theorem torsionIdeal_mul_le {A : Type w} [CommRing A] [Bialgebra R A] (m n : ℕ) :
    Hopf.torsionIdeal R A (m * n) ≤ Hopf.torsionIdeal R A m := by
  rw [Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change Hopf.nsmulAlgHom R A (m * n) a ∈ Hopf.torsionIdeal R A m
  rw [← nsmulAlgHom_comp_nsmulAlgHom, AlgHom.comp_apply]
  exact Hopf.nsmulAlgHom_mem_torsionIdeal R A (Hopf.nsmulAlgHom_mem_augIdeal R A ha n) m

theorem map_augIdeal_eq {A : Type v} {B : Type w} [CommRing A] [Bialgebra R A] [CommRing B]
    [Bialgebra R B] (f : A →ₐc[R] B) (hf : Function.Surjective f) :
    Ideal.map f (Hopf.augIdeal R A) = Hopf.augIdeal R B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ Hopf.augIdeal R B
    rw [Hopf.mem_augIdeal_iff, CoalgHomClass.counit_comp_apply]
    exact (Hopf.mem_augIdeal_iff R A a).1 ha
  · intro b hb
    obtain ⟨a, rfl⟩ := hf b
    have ha : a ∈ Hopf.augIdeal R A := by
      rw [Hopf.mem_augIdeal_iff, ← CoalgHomClass.counit_comp_apply f a]
      exact (Hopf.mem_augIdeal_iff R B _).1 hb
    exact Ideal.mem_map_of_mem _ ha

theorem map_torsionIdeal_eq {A : Type v} {B : Type w} [CommRing A] [Bialgebra R A] [CommRing B]
    [Bialgebra R B] (f : A →ₐc[R] B) (hf : Function.Surjective f) (n : ℕ) :
    Ideal.map f (Hopf.torsionIdeal R A n) = Hopf.torsionIdeal R B n := by
  rw [Hopf.torsionIdeal, Hopf.torsionIdeal, ← map_augIdeal_eq f hf]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, ← Hopf.nsmulAlgHom_bialgHom_apply f n a]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Hopf.nsmulAlgHom_bialgHom_apply f n a]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)

theorem ker_T (v : ℕ) : ∀ w,
    RingHom.ker (G.T v w) = Hopf.torsionIdeal R (G.level (v + w)) (p ^ v)
  | 0 => by
    change RingHom.ker (BialgHom.id R (G.level v)) = Hopf.torsionIdeal R (G.level v) (p ^ v)
    have h0 : Hopf.torsionIdeal R (G.level v) (p ^ v) = ⊥ := by
      rw [eq_bot_iff, Hopf.torsionIdeal, Ideal.map_le_iff_le_comap]
      intro a ha
      change Hopf.nsmulAlgHom R (G.level v) (p ^ v) a ∈ (⊥ : Ideal (G.level v))
      rw [G.nsmulAlgHom_pow_level_apply, (Hopf.mem_augIdeal_iff R _ a).1 ha, map_zero]
      exact Ideal.zero_mem _
    rw [h0]
    ext a
    simp [RingHom.mem_ker]
  | w + 1 => by
    rw [T_succ]
    have hcomp : RingHom.ker ((G.T v w).comp (G.transition (v + w))) =
        Ideal.comap (G.transition (v + w)) (RingHom.ker (G.T v w)) := by
      ext a
      simp only [RingHom.mem_ker, Ideal.mem_comap, BialgHom.coe_comp, Function.comp_apply]
    rw [hcomp, ker_T v w, ← map_torsionIdeal_eq (G.transition (v + w)) (G.transition_surjective _),
      Ideal.comap_map_of_surjective _ (G.transition_surjective (v + w))]
    apply le_antisymm
    · refine sup_le le_rfl ?_
      intro a ha
      have ha' : a ∈ RingHom.ker (G.transition (v + w)) := ha
      rw [G.ker_transition (v + w), pow_add] at ha'
      exact torsionIdeal_mul_le _ _ ha'
    · exact le_sup_left

theorem free_and_finrank_quotient (v w : ℕ) :
    Module.Free R (G.level (v + w) ⧸ Hopf.torsionIdeal R (G.level (v + w)) (p ^ w)) ∧
      Module.finrank R (G.level (v + w) ⧸ Hopf.torsionIdeal R (G.level (v + w)) (p ^ w)) =
        p ^ (w * h) := by
  have key : ∀ n : ℕ, n = w + v →
      Module.Free R (G.level n ⧸ Hopf.torsionIdeal R (G.level n) (p ^ w)) ∧
        Module.finrank R (G.level n ⧸ Hopf.torsionIdeal R (G.level n) (p ^ w)) = p ^ (w * h) := by
    rintro n rfl
    let f : G.level (w + v) →ₐ[R] G.level w := (G.T w v : G.level (w + v) →ₐ[R] G.level w)
    have hf : Function.Surjective f := G.T_surjective w v
    have hker : RingHom.ker f = Hopf.torsionIdeal R (G.level (w + v)) (p ^ w) := G.ker_T w v
    let e : (G.level (w + v) ⧸ Hopf.torsionIdeal R (G.level (w + v)) (p ^ w)) ≃ₐ[R] G.level w :=
      (Ideal.quotientEquivAlgOfEq R hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
    exact ⟨Module.Free.of_equiv e.symm.toLinearEquiv,
      by rw [e.toLinearEquiv.finrank_eq, G.finrank_level]⟩
  exact key (v + w) (Nat.add_comm v w)

end Tower
p2m_reactivate "P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.K5preTower.Tower"

end K5preTower
p2m_reactivate "P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.K5preTower.Tower P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.K5preTower"

end
p2m_reactivate "P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.K5preTower.Tower P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal.K5preTower"

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v)) :
    ∃ T : ∀ v w : ℕ, L (v + w) →ₐc[𝓞] L v,
      (∀ v, T v 0 = BialgHom.id 𝓞 (L v)) ∧
      (∀ v w, T v (w + 1) = (T v w).comp (t (v + w))) ∧
      (∀ v w, Function.Surjective (T v w)) ∧
      (∀ v w, RingHom.ker (T v w) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ v)) ∧
      (∀ v, PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (L v) (p ^ v) =
        (Algebra.ofId 𝓞 (L v)).comp (Bialgebra.counitAlgHom 𝓞 (L v))) ∧
      (∀ v w, Module.Free 𝓞 (L (v + w) ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ w)) ∧
        Module.finrank 𝓞 (L (v + w) ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + w)) (p ^ w)) =
          p ^ (w * h)) := by
  let G : K5preTower.Tower 𝓞 p h :=
    { level := L, transition := t, transition_surjective := ht, finrank_level := hrankL,
      ker_transition := hkerL }
  exact ⟨G.T, G.T_zero, G.T_succ, G.T_surjective, G.ker_T, G.nsmulAlgHom_pow_level,
    G.free_and_finrank_quotient⟩

end S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal
end P2MW
export P2MW.S_PDivisibleGroup_Hopf_exists_forall_comp_transition_surjective_ker_eq_torsionIdeal (solution)
