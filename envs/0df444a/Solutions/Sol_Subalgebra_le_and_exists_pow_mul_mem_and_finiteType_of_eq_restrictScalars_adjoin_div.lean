-- Prove2me | solution 1 for Subalgebra.le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/ae8bf186-b9a7-5c80-b558-f244512dbd99

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div

set_option autoImplicit false

namespace BlowupChartBasic

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]

def genSet (C : Subalgebra A K) (J : Ideal ↥C) (t : A) : Set K :=
  {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}

theorem mem_genSet {C : Subalgebra A K} {J : Ideal ↥C} {t : A} {x : K} :
    x ∈ genSet C J t ↔ ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K) := Iff.rfl

theorem coe_mem_adjoin (C : Subalgebra A K) (S : Set K) (c : ↥C) :
    (c : K) ∈ Algebra.adjoin (↥C) S :=
  Subalgebra.algebraMap_mem (Algebra.adjoin (↥C) S) c

theorem exists_pow_mul_mem (C : Subalgebra A K) (J : Ideal ↥C) (t : A) {b : K}
    (hb : b ∈ Algebra.adjoin (↥C) (genSet C J t)) :
    ∃ n : ℕ, algebraMap A K t ^ n * b ∈ C := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, -, hi⟩ := hx
    exact ⟨1, by rw [pow_one, mul_comm, hi]; exact i.2⟩
  | algebraMap c => exact ⟨0, by rw [pow_zero, one_mul]; exact c.2⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have : algebraMap A K t ^ (m + n) * (x + y) =
        algebraMap A K t ^ n * (algebraMap A K t ^ m * x) +
          algebraMap A K t ^ m * (algebraMap A K t ^ n * y) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem (C.algebraMap_mem t) n) hm)
      (mul_mem (pow_mem (C.algebraMap_mem t) m) hn)
  | mul x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have : algebraMap A K t ^ (m + n) * (x * y) =
        (algebraMap A K t ^ m * x) * (algebraMap A K t ^ n * y) := by ring
    rw [this]
    exact mul_mem hm hn

theorem div_mem_genSet {C : Subalgebra A K} {J : Ideal ↥C} {t : A}
    (ht0 : algebraMap A K t ≠ 0) {i : ↥C} (hi : i ∈ J) :
    ((i : ↥C) : K) * (algebraMap A K t)⁻¹ ∈ genSet C J t :=
  ⟨i, hi, by rw [mul_assoc, inv_mul_cancel₀ ht0, mul_one]⟩

theorem adjoin_genSet_eq_adjoin_image {C : Subalgebra A K} {J : Ideal ↥C} {t : A}
    (ht0 : algebraMap A K t ≠ 0) (s : Set ↥C) (hs : Ideal.span s = J) :
    Algebra.adjoin (↥C) (genSet C J t) =
      Algebra.adjoin (↥C) ((fun i : ↥C => ((i : ↥C) : K) * (algebraMap A K t)⁻¹) '' s) := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro x ⟨i, hi, hx⟩
    have hx' : x = ((i : ↥C) : K) * (algebraMap A K t)⁻¹ := by
      rw [← hx, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [hx']
    rw [← hs] at hi
    clear hx hx'

    induction hi using Submodule.span_induction with
    | mem y hy => exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    | zero => rw [ZeroMemClass.coe_zero, zero_mul]; exact zero_mem _
    | add y z _ _ hy hz =>
      rw [Subalgebra.coe_add, add_mul]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]
      have : (c : K) * (((y : ↥C) : K) * (algebraMap A K t)⁻¹) =
          c • (((y : ↥C) : K) * (algebraMap A K t)⁻¹) := rfl
      rw [this]
      exact Subalgebra.smul_mem _ hy c
  · refine Algebra.adjoin_le ?_
    rintro x ⟨i, hi, rfl⟩
    exact Algebra.subset_adjoin (div_mem_genSet ht0 (hs ▸ Ideal.subset_span hi))

theorem finiteType_adjoin_genSet {C : Subalgebra A K} {J : Ideal ↥C} {t : A}
    (ht0 : algebraMap A K t ≠ 0) (hJ : J.FG) :
    Algebra.FiniteType (↥C) ↥(Algebra.adjoin (↥C) (genSet C J t)) := by
  classical
  obtain ⟨s, hs⟩ := hJ
  rw [adjoin_genSet_eq_adjoin_image ht0 (s : Set ↥C) hs, ← Finset.coe_image]
  exact (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)

end BlowupChartBasic

open BlowupChartBasic in

theorem solution
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (J : Ideal ↥C) (t : A)
    (ht0 : algebraMap A K t ≠ 0)
    (B : Subalgebra A K)
    (hB : B = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * algebraMap A K t = ((i : ↥C) : K)}).restrictScalars A) :

    C ≤ B ∧

    (∀ b : K, b ∈ B → ∃ n : ℕ, algebraMap A K t ^ n * b ∈ C) ∧

    ((∀ f : K, ∃ g h : ↥C, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) →
      ∀ f : K, ∃ g h : ↥B, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) ∧

    (J.FG → Algebra.FiniteType A ↥C → Algebra.FiniteType A ↥B) ∧

    (∀ i : ↥C, i ∈ J → ∃ b : K, b ∈ B ∧ ((i : ↥C) : K) = algebraMap A K t * b) ∧

    (∀ Q : Ideal ↥B, algebraMap A ↥B t ∈ Q →
      ∀ i : ↥C, i ∈ J → ∀ hiB : ((i : ↥C) : K) ∈ B, (⟨((i : ↥C) : K), hiB⟩ : ↥B) ∈ Q) := by
  have hmem : ∀ b : K, b ∈ B ↔ b ∈ Algebra.adjoin (↥C) (genSet C J t) := by
    intro b; rw [hB]; rfl
  have h1 : C ≤ B := fun c hc => (hmem c).mpr (coe_mem_adjoin C _ ⟨c, hc⟩)
  have h5 : ∀ i : ↥C, i ∈ J → ∃ b : K, b ∈ B ∧ ((i : ↥C) : K) = algebraMap A K t * b := by
    intro i hi
    refine ⟨((i : ↥C) : K) * (algebraMap A K t)⁻¹, (hmem _).mpr (Algebra.subset_adjoin (div_mem_genSet ht0 hi)), ?_⟩
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
  refine ⟨h1, ?_, ?_, ?_, h5, ?_⟩
  · intro b hb
    exact exists_pow_mul_mem C J t ((hmem b).mp hb)
  · intro hfrac f
    obtain ⟨g, h, hh, hf⟩ := hfrac f
    exact ⟨⟨(g : K), h1 g.2⟩, ⟨(h : K), h1 h.2⟩, hh, hf⟩
  · intro hJ hC
    haveI := hC
    haveI : Algebra.FiniteType (↥C) ↥(Algebra.adjoin (↥C) (genSet C J t)) := finiteType_adjoin_genSet ht0 hJ
    have hAB' : Algebra.FiniteType A ↥(Algebra.adjoin (↥C) (genSet C J t)) :=
      Algebra.FiniteType.trans (S := ↥C) hC inferInstance

    subst hB
    let e : ↥(Algebra.adjoin (↥C) (genSet C J t)) →ₐ[A]
        ↥((Algebra.adjoin (↥C) (genSet C J t)).restrictScalars A) :=
      { toFun := fun x => ⟨x.1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    exact hAB'.of_surjective e (fun y => ⟨⟨y.1, y.2⟩, rfl⟩)
  · intro Q htQ i hi hiB
    obtain ⟨b, hbB, hib⟩ := h5 i hi
    have : (⟨((i : ↥C) : K), hiB⟩ : ↥B) = algebraMap A ↥B t * ⟨b, hbB⟩ := by
      apply Subtype.ext
      rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
      exact hib
    rw [this]
    exact Ideal.mul_mem_right _ _ htQ

end S_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div
end P2MW
export P2MW.S_Subalgebra_le_and_exists_pow_mul_mem_and_finiteType_of_eq_restrictScalars_adjoin_div (solution)
