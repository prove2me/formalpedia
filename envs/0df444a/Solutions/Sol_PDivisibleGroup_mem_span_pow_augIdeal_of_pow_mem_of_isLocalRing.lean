-- Prove2me | solution 1 for PDivisibleGroup.mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/524170d9-a8e1-5662-a202-3a9afe0bdb5f

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_PDivisibleGroup_Hopf_exists_verschiebung_algHom_zmodp
import Theorems.Thm_PDivisibleGroup_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

universe v

namespace PDivisibleGroup
p2m_export "PDivisibleGroup" "Hopf.augIdeal Hopf.torsionIdeal level Hopf.exists_verschiebung_algHom_zmodp exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal"
namespace FrobInjC12
p2m_open "PDivisibleGroup"

open PDivisibleGroup.Hopf

private theorem nsmulAlgHom_mul_apply {p : ℕ} [Fact p.Prime] {A : Type v} [CommRing A]
    [HopfAlgebra (ZMod p) A] (m n : ℕ) (a : A) :
    nsmulAlgHom (ZMod p) A (m * n) a = nsmulAlgHom (ZMod p) A m (nsmulAlgHom (ZMod p) A n a) := by
  rw [nsmulAlgHom_mul, toConv_pow_eq_toConv_comp_nsmulAlgHom]
  rfl

private theorem nsmulAlgHom_prime_pow_apply {p : ℕ} [Fact p.Prime] {A : Type v} [CommRing A]
    [HopfAlgebra (ZMod p) A] (V : A →ₐc[ZMod p] A)
    (hV : ∀ a, (V a) ^ p = nsmulAlgHom (ZMod p) A p a) (k : ℕ) (y : A) :
    nsmulAlgHom (ZMod p) A (p ^ k) y = ((⇑V)^[k] y) ^ (p ^ k) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Function.iterate_succ_apply, pow_mul, nsmulAlgHom_mul_apply, ← ih, ← map_pow, hV]

private theorem iterate_mem_augIdeal {p : ℕ} [Fact p.Prime] {A : Type v} [CommRing A]
    [HopfAlgebra (ZMod p) A] (V : A →ₐc[ZMod p] A) (k : ℕ) {y : A}
    (hy : y ∈ augIdeal (ZMod p) A) : (⇑V)^[k] y ∈ augIdeal (ZMod p) A := by
  induction k generalizing y with
  | zero => simpa using hy
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    refine ih ?_
    rw [mem_augIdeal_iff] at hy ⊢
    rw [CoalgHomClass.counit_comp_apply, hy]

private theorem mem_of_coe_mem_map_algebraMap {R : Type*} [CommRing R] {B : Type*} [CommRing B]
    [Algebra R B] (C : Subalgebra R B) (r : B →ₗ[C] C) (hr : ∀ c : C, r (c : B) = c)
    (K : Ideal C) (x : C) (hx : (x : B) ∈ K.map (algebraMap C B)) : x ∈ K := by
  have hx' : (x : B) ∈ (K • ⊤ : Submodule C B) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  have h2 : r (x : B) ∈ (K • ⊤ : Submodule C B).map r := Submodule.mem_map_of_mem hx'
  rw [Submodule.map_smul'', hr] at h2
  exact (Submodule.smul_le.2 fun k hk c _ => K.mul_mem_right c hk) h2

private def J (p : ℕ) (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A] (m : ℕ) : Ideal A :=
  Ideal.span ((fun a : A => a ^ p ^ m) '' (augIdeal (ZMod p) A : Set A))

private theorem J_def (p : ℕ) (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A] (m : ℕ) :
    J p A m = Ideal.span ((fun a : A => a ^ p ^ m) '' (augIdeal (ZMod p) A : Set A)) := rfl

private theorem main
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (n w : ℕ) (hn : n ≤ w) (a : H (w + 1)) (ha : a ^ p ∈ J p (H (w + 1)) (n + 1)) :
    a ∈ J p (H (w + 1)) n := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨V, hV, -, -⟩ := PDivisibleGroup.Hopf.exists_verschiebung_algHom_zmodp p (H (w + 1))

  have h1 : nsmulAlgHom (ZMod p) (H (w + 1)) p a ∈
      (J p (H (w + 1)) n).map (nsmulAlgHom (ZMod p) (H (w + 1)) p) := by
    have hVa : nsmulAlgHom (ZMod p) (H (w + 1)) p a = V (a ^ p) := by rw [map_pow, hV]
    rw [hVa]
    have hle : (J p (H (w + 1)) (n + 1)).map V ≤
        (J p (H (w + 1)) n).map (nsmulAlgHom (ZMod p) (H (w + 1)) p) := by
      rw [Ideal.map_le_iff_le_comap, J_def]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, pow_succ', pow_mul, hV, ← map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨y, hy, rfl⟩)
    exact hle (Ideal.mem_map_of_mem _ ha)

  obtain ⟨⟨e, he⟩, -, -, ⟨r, hr⟩, -⟩ :=
    PDivisibleGroup.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk_of_ker_eq_torsionIdeal
      (ZMod p) p h₀ H s hs hrankH hkerH w

  have h2 : nsmulAlgHom (ZMod p) (H (w + 1)) p a ∈
      (((J p (H (w + 1)) n).map (s w)).map e).map
        (algebraMap ↥(nsmulAlgHom (ZMod p) (H (w + 1)) p).range (H (w + 1))) := by
    refine (show (J p (H (w + 1)) n).map (nsmulAlgHom (ZMod p) (H (w + 1)) p) ≤ _ from ?_) h1
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← he x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx))
  rw [← he a] at h2

  have h3 : e (s w a) ∈ ((J p (H (w + 1)) n).map (s w)).map e :=
    mem_of_coe_mem_map_algebraMap _ r hr _ _ h2

  have h4 : s w a ∈ (J p (H (w + 1)) n).map (s w) := by
    have hle : (((J p (H (w + 1)) n).map (s w)).map e).map e.symm ≤ (J p (H (w + 1)) n).map (s w) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.symm_apply_apply]
      exact hx
    have := hle (Ideal.mem_map_of_mem e.symm h3)
    rwa [AlgEquiv.symm_apply_apply] at this

  obtain ⟨x, hx, hxa⟩ := (Ideal.mem_map_iff_of_surjective (s w) (hs w)).1 h4
  have hker : a - x ∈ RingHom.ker (s w) := by
    rw [RingHom.mem_ker, map_sub, hxa, sub_self]
  have hkerle : RingHom.ker (s w) ≤ J p (H (w + 1)) n := by
    rw [hkerH w, torsionIdeal_eq_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, nsmulAlgHom_prime_pow_apply V hV w y]
    have hpw : p ^ w = p ^ (w - n) * p ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    rw [hpw, pow_mul]
    refine Ideal.subset_span ⟨((⇑V)^[w] y) ^ p ^ (w - n), ?_, rfl⟩
    exact Ideal.pow_mem_of_mem _ (iterate_mem_augIdeal V w hy) _ (pow_pos hp.pos _)
  have hax : a = x + (a - x) := by ring
  rw [hax]
  exact Ideal.add_mem _ hx (hkerle hker)

end PDivisibleGroup.FrobInjC12

theorem solution
    (p : ℕ) [Fact p.Prime] (h₀ : ℕ)
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, HopfAlgebra (ZMod p) (H v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (H v)] [∀ v, Module.Finite (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v) (hs : ∀ v, Function.Surjective (s v))
    (hrankH : ∀ v, Module.finrank (ZMod p) (H v) = p ^ (v * h₀))
    (hkerH : ∀ v, RingHom.ker (s v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (H (v + 1)) (p ^ v))
    (hlocH : ∀ v, IsLocalRing (H v))
    (n w : ℕ) (hnw : n + 1 ≤ w) (a : H w)
    (ha : a ^ p ∈ Ideal.span ((fun a : H w => a ^ p ^ (n + 1)) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w)))) :
    a ∈ Ideal.span ((fun a : H w => a ^ p ^ n) ''
          (PDivisibleGroup.Hopf.augIdeal (ZMod p) (H w) : Set (H w))) := by
  match w, hnw, a, ha with
  | w' + 1, hnw', a', ha' =>
    exact PDivisibleGroup.FrobInjC12.main p h₀ H s hs hrankH hkerH n w' (by omega) a' ha'

end S_PDivisibleGroup_mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing
end P2MW
export P2MW.S_PDivisibleGroup_mem_span_pow_augIdeal_of_pow_mem_of_isLocalRing (solution)
