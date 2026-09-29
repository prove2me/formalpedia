-- Prove2me | solution 1 for PDivisibleGroup.exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6c582254-49b3-585c-8a7b-8fd41e99965f

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp

open scoped TensorProduct

universe u v

namespace Deformation
p2m_export "Deformation" "TruncWitt.map TruncWitt.coeff_map wittHom counit_coeff_of_mem_wittHom coe_wittHomMap TruncWitt.shiftLE TruncWitt.coeff_shiftLE coe_wittHomShiftLE DieudonneModule DieudonneModule.of DieudonneModule.exists_of DieudonneModule.of_eq_of_iff DieudonneModule.map DieudonneModule.map_of"
p2m_open "Deformation"

namespace StarLift

open Function

namespace CovectorComponents

section EndCoeff

variable {p : ℕ} {n m : ℕ} {R : Type*} {S : Type*} [CommRing R] [CommRing S]

def endCoeff (k : ℕ) (x : TruncatedWittVector p n R) : R :=
  if hk : k < n then x.coeff ⟨n - 1 - k, by omega⟩ else 0

theorem endCoeff_of_lt (k : ℕ) (x : TruncatedWittVector p n R) (hk : k < n) :
    endCoeff k x = x.coeff ⟨n - 1 - k, by omega⟩ := dif_pos hk

theorem endCoeff_of_le (k : ℕ) (x : TruncatedWittVector p n R) (hk : n ≤ k) :
    endCoeff k x = 0 := dif_neg (by omega)

variable [hp : Fact p.Prime]

theorem endCoeff_shiftLE (h : n ≤ m) (k : ℕ) (x : TruncatedWittVector p n R) :
    endCoeff k (TruncWitt.shiftLE h x) = endCoeff k x := by
  unfold endCoeff
  by_cases hk : k < n
  · have hkm : k < m := by omega
    rw [dif_pos hkm, dif_pos hk, TruncWitt.coeff_shiftLE,
      dif_pos (show m - n ≤ m - 1 - k by omega)]
    congr 1
    exact Fin.ext (by simp only []; omega)
  · rw [dif_neg hk]
    by_cases hkm : k < m
    · rw [dif_pos hkm, TruncWitt.coeff_shiftLE, dif_neg (show ¬ (m - n ≤ m - 1 - k) by omega)]
    · rw [dif_neg hkm]

theorem endCoeff_map (f : R →+* S) (k : ℕ) (x : TruncatedWittVector p n R) :
    endCoeff k (TruncWitt.map f x) = f (endCoeff k x) := by
  unfold endCoeff
  split_ifs
  · exact TruncWitt.coeff_map f x _
  · exact (map_zero f).symm

end EndCoeff

section Comp

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]
variable {A : Type*} [CommRing A] [Bialgebra R A] {B : Type*} [CommRing B] [Bialgebra R B]

theorem endCoeff_eq_of_of_eq_of {n n' : ℕ} (u : wittHom R p n A) (u' : wittHom R p n' A)
    (h : DieudonneModule.of R p A n u = DieudonneModule.of R p A n' u') (k : ℕ) :
    endCoeff k (u : TruncatedWittVector p n A) = endCoeff k (u' : TruncatedWittVector p n' A) := by
  rw [DieudonneModule.of_eq_of_iff] at h
  have h' := congrArg
    (fun w : wittHom R p (max n n') A => endCoeff k (w : TruncatedWittVector p (max n n') A)) h
  simpa only [coe_wittHomShiftLE, endCoeff_shiftLE] using h'

noncomputable def component (z : DieudonneModule R p A) (k : ℕ) : A :=
  endCoeff k (Subtype.val (DieudonneModule.exists_of z).choose_spec.choose)

theorem component_of {n : ℕ} (u : wittHom R p n A) (k : ℕ) :
    component (DieudonneModule.of R p A n u) k = endCoeff k (u : TruncatedWittVector p n A) := by
  unfold component
  exact endCoeff_eq_of_of_eq_of _ _
    (DieudonneModule.exists_of (DieudonneModule.of R p A n u)).choose_spec.choose_spec k

theorem component_map (φ : A →ₐc[R] B) (z : DieudonneModule R p A) (k : ℕ) :
    component (DieudonneModule.map R p φ z) k = φ (component z k) := by
  obtain ⟨n, u, rfl⟩ := DieudonneModule.exists_of z
  rw [DieudonneModule.map_of, component_of, component_of, coe_wittHomMap, endCoeff_map]
  rfl

theorem counit_component (z : DieudonneModule R p A) (k : ℕ) :
    Coalgebra.counit (R := R) (component z k) = 0 := by
  obtain ⟨n, u, rfl⟩ := DieudonneModule.exists_of z
  rw [component_of]
  unfold endCoeff
  split_ifs with hk
  · exact counit_coeff_of_mem_wittHom u.2 _
  · exact map_zero _

theorem component_of_eq_zero_of_le {n : ℕ} (u : wittHom R p n A) (k : ℕ) (hk : n ≤ k) :
    component (DieudonneModule.of R p A n u) k = 0 := by
  rw [component_of, endCoeff_of_le _ _ hk]

end Comp

end CovectorComponents

section BaseChange

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [Algebra 𝓞 (ZMod p)]
variable {M : Type*} [AddCommGroup M] [Module 𝓞 M]

theorem exists_one_tmul_eq (w : ZMod p ⊗[𝓞] M) : ∃ e : M, (1 : ZMod p) ⊗ₜ[𝓞] e = w := by
  have hsurj : Function.Surjective ((Algebra.linearMap 𝓞 (ZMod p)).rTensor M) :=
    LinearMap.rTensor_surjective M (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p)))
  obtain ⟨y, rfl⟩ := hsurj w
  refine ⟨TensorProduct.lid 𝓞 M y, ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o e =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.linearMap_apply, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  | add a b ha hb => rw [map_add, TensorProduct.tmul_add, ha, hb, map_add]

theorem exists_eq_smul_of_one_tmul_eq_zero
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {e : M} (he : ((1 : ZMod p) ⊗ₜ[𝓞] e : ZMod p ⊗[𝓞] M) = 0) : ∃ t : M, e = (p : 𝓞) • t := by
  have hfg : Function.Exact ((p : 𝓞) • (LinearMap.id : 𝓞 →ₗ[𝓞] 𝓞)) (Algebra.linearMap 𝓞 (ZMod p)) := by
    intro y
    rw [Algebra.linearMap_apply, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton', Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_comm]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, by rw [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_comm]⟩
  have hex := rTensor_exact M hfg (ZMod.ringHom_surjective (algebraMap 𝓞 (ZMod p)))
  have h0 : ((Algebra.linearMap 𝓞 (ZMod p)).rTensor M) ((1 : 𝓞) ⊗ₜ[𝓞] e) = 0 := by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, he]
  obtain ⟨y, hy⟩ := (hex _).1 h0
  refine ⟨TensorProduct.lid 𝓞 M y, ?_⟩
  have := congrArg (TensorProduct.lid 𝓞 M) hy
  rw [TensorProduct.lid_tmul, one_smul, LinearMap.rTensor_smul, LinearMap.smul_apply, map_smul,
    LinearMap.rTensor_id, LinearMap.id_apply] at this
  exact this.symm

end BaseChange

theorem exists_compatible_seq {E G : ℕ → Type*} (ρ : ∀ v, E v → G v) (st : ∀ v, E (v + 1) → E v)
    (z : ∀ v, G v) (P₀ : E 0 → Prop)
    (hbase : ∃ e : E 0, ρ 0 e = z 0 ∧ P₀ e)
    (hstep : ∀ (v : ℕ) (e : E v), ρ v e = z v → ∃ e' : E (v + 1), ρ (v + 1) e' = z (v + 1) ∧ st v e' = e) :
    ∃ c : ∀ v, E v, (∀ v, ρ v (c v) = z v) ∧ (∀ v, st v (c (v + 1)) = c v) ∧ P₀ (c 0) := by
  classical
  let seq : ∀ v, {e : E v // ρ v e = z v} := fun v =>
    Nat.rec (motive := fun v => {e : E v // ρ v e = z v})
      ⟨Classical.choose hbase, (Classical.choose_spec hbase).1⟩
      (fun v ih => ⟨Classical.choose (hstep v ih.1 ih.2), (Classical.choose_spec (hstep v ih.1 ih.2)).1⟩) v
  refine ⟨fun v => (seq v).1, fun v => (seq v).2, fun v => ?_, (Classical.choose_spec hbase).2⟩
  exact (Classical.choose_spec (hstep v (seq v).1 (seq v).2)).2

theorem main
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
    (Et : ℕ → Type u) [∀ v, CommRing (Et v)] [∀ v, HopfAlgebra 𝓞 (Et v)] [∀ v, Module.Free 𝓞 (Et v)] [∀ v, Module.Finite 𝓞 (Et v)]
    (st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v) (hst : ∀ v, Function.Surjective (st v))
    (θe : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] Ge v) (hθe : ∀ v, Function.Bijective (θe v))
    (hθe_comp : ∀ v, (θe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (st v)) = (se v).comp (θe (v + 1)))
    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (Ge v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (se v) (m (v + 1)) = m v) :
    ∃ ĉ : ℕ → ∀ v, Et v,
      (∀ k v, st v (ĉ k (v + 1)) = ĉ k v) ∧
      (∀ k v, Coalgebra.counit (R := 𝓞) (ĉ k v) = 0) ∧
      (∀ v, ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (Ge v)),
        Deformation.DieudonneModule.of (ZMod p) p (Ge v) n u = m v ∧
        (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (Ge v)).coeff ⟨n - 1 - k, by omega⟩ =
           θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v)) ∧
        (∀ k, n ≤ k → θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v) = 0)) := by
  classical

  let z : ℕ → ∀ v, Ge v := fun k v => CovectorComponents.component (m v) k
  let ρ : ∀ v, Et v →+ Ge v := fun v =>
    (θe v : ZMod p ⊗[𝓞] Et v →ₐ[ZMod p] Ge v).toRingHom.toAddMonoidHom.comp
      (TensorProduct.mk 𝓞 (ZMod p) (Et v) 1).toAddMonoidHom
  have hρ : ∀ v e, ρ v e = θe v ((1 : ZMod p) ⊗ₜ[𝓞] e) := fun v e => rfl
  have hρ_surj : ∀ v, Function.Surjective (ρ v) := fun v y => by
    obtain ⟨w, rfl⟩ := (hθe v).2 y
    obtain ⟨e, rfl⟩ := exists_one_tmul_eq p w
    exact ⟨e, rfl⟩
  have hρ_ker : ∀ v (e : Et v), ρ v e = 0 → ∃ t : Et v, e = (p : 𝓞) • t := fun v e he =>
    exists_eq_smul_of_one_tmul_eq_zero p hker ((hθe v).1 (he.trans (map_zero (θe v)).symm))
  have hρ_p : ∀ v (t : Et v), ρ v ((p : 𝓞) • t) = 0 := fun v t => by
    rw [hρ, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, map_natCast,
      ZMod.natCast_self, TensorProduct.zero_tmul, map_zero]
  have hρ_st : ∀ v (e : Et (v + 1)), ρ v (st v e) = se v (ρ (v + 1) e) := fun v e => by
    have := DFunLike.congr_fun (hθe_comp v) ((1 : ZMod p) ⊗ₜ[𝓞] e)
    rw [BialgHom.comp_apply, BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul] at this
    rw [hρ, hρ]
    exact this
  have hρ_counit : ∀ v (e : Et v), Coalgebra.counit (R := ZMod p) (ρ v e) =
      algebraMap 𝓞 (ZMod p) (Coalgebra.counit (R := 𝓞) e) := fun v e => by
    rw [hρ, CoalgHomClass.counit_comp_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, mul_one]
  have hz_se : ∀ k v, se v (z k (v + 1)) = z k v := fun k v => by
    show se v (CovectorComponents.component (m (v + 1)) k) = CovectorComponents.component (m v) k
    rw [← CovectorComponents.component_map, hm]

  have key : ∀ k, ∃ c : ∀ v, Et v, (∀ v, ρ v (c v) = z k v) ∧ (∀ v, st v (c (v + 1)) = c v) ∧
      Coalgebra.counit (R := 𝓞) (c 0) = 0 := by
    intro k
    refine exists_compatible_seq (fun v e => ρ v e) (fun v e => st v e) (z k)
      (fun e => Coalgebra.counit (R := 𝓞) e = 0) ?_ ?_
    ·
      beta_reduce
      obtain ⟨e₁, he₁⟩ := hρ_surj 0 (z k 0)
      have hc : algebraMap 𝓞 (ZMod p) (Coalgebra.counit (R := 𝓞) e₁) = 0 := by
        rw [← hρ_counit, he₁]
        exact CovectorComponents.counit_component (m 0) k
      rw [← RingHom.mem_ker, hker] at hc
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hc
      refine ⟨e₁ - (p : 𝓞) • (a • (1 : Et 0)), ?_, ?_⟩
      · rw [map_sub, he₁, hρ_p, sub_zero]
      · rw [map_sub, map_smul, map_smul, Bialgebra.counit_one, smul_eq_mul, smul_eq_mul, mul_one, ← ha,
          mul_comm, sub_self]
    ·
      intro v e he
      beta_reduce at he ⊢
      obtain ⟨e₁, he₁⟩ := hρ_surj (v + 1) (z k (v + 1))
      have h0 : ρ v (st v e₁ - e) = 0 := by rw [map_sub, hρ_st, he₁, hz_se, he, sub_self]
      obtain ⟨t, ht⟩ := hρ_ker v _ h0
      obtain ⟨t₁, rfl⟩ := hst v t
      refine ⟨e₁ - (p : 𝓞) • t₁, ?_, ?_⟩
      · rw [map_sub, he₁, hρ_p, sub_zero]
      · rw [map_sub, map_smul, ← ht, sub_sub_cancel]
  choose c hcρ hcst hc0 using key
  refine ⟨c, hcst, ?_, fun v => ?_⟩
  ·
    intro k v
    induction v with
    | zero => exact hc0 k
    | succ v ih => rw [← hcst k v, CoalgHomClass.counit_comp_apply] at ih; exact ih
  · obtain ⟨n, u, hu⟩ := DieudonneModule.exists_of (m v)
    refine ⟨n, u, hu, fun k hk => ?_, fun k hk => ?_⟩
    · rw [← hρ, hcρ, ← CovectorComponents.endCoeff_of_lt k _ hk]
      show _ = CovectorComponents.component (m v) k
      rw [← hu, CovectorComponents.component_of]
    · rw [← hρ, hcρ]
      show CovectorComponents.component (m v) k = 0
      rw [← hu, CovectorComponents.component_of_eq_zero_of_le u k hk]

end StarLift

end Deformation

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]

    (Ge : ℕ → Type v) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
    (Et : ℕ → Type u) [∀ v, CommRing (Et v)] [∀ v, HopfAlgebra 𝓞 (Et v)] [∀ v, Module.Free 𝓞 (Et v)] [∀ v, Module.Finite 𝓞 (Et v)]
    (st : ∀ v, Et (v + 1) →ₐc[𝓞] Et v) (hst : ∀ v, Function.Surjective (st v))
    (θe : ∀ v, ZMod p ⊗[𝓞] Et v →ₐc[ZMod p] Ge v) (hθe : ∀ v, Function.Bijective (θe v))
    (hθe_comp : ∀ v, (θe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (st v)) = (se v).comp (θe (v + 1)))

    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (Ge v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (se v) (m (v + 1)) = m v) :
    ∃ ĉ : ℕ → ∀ v, Et v,
      (∀ k v, st v (ĉ k (v + 1)) = ĉ k v) ∧
      (∀ k v, Coalgebra.counit (R := 𝓞) (ĉ k v) = 0) ∧
      (∀ v, ∃ (n : ℕ) (u : Deformation.wittHom (ZMod p) p n (Ge v)),
        Deformation.DieudonneModule.of (ZMod p) p (Ge v) n u = m v ∧
        (∀ (k : ℕ) (hk : k < n), (u : TruncatedWittVector p n (Ge v)).coeff ⟨n - 1 - k, by omega⟩ =
           θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v)) ∧
        (∀ k, n ≤ k → θe v ((1 : ZMod p) ⊗ₜ[𝓞] ĉ k v) = 0)) :=
  Deformation.StarLift.main p hp hker Ge se Et st hst θe hθe hθe_comp m hm

end S_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_exists_compatible_lift_coeff_eq_of_surjective_tower_zmodp (solution)
