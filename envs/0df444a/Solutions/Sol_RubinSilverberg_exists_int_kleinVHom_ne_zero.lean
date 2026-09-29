-- Prove2me | solution 1 for RubinSilverberg.exists_int_kleinVHom_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/40d11875-713e-58f7-a7dd-76eae0e3b4f3

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Pigeonhole
import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RubinSilverberg_exists_int_kleinVHom_ne_zero

open Polynomial RubinSilverberg

namespace Slope

variable {K : Type*} [Field K] [CharZero K]

theorem map_kleinVHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n d : R) :
    f (kleinVHom n d) = kleinVHom (f n) (f d) := by
  simp [kleinVHom, map_sub, map_add, map_mul, map_pow, map_ofNat]

theorem kleinVHom_smul_row {R : Type*} [CommRing R] (c n d : R) : kleinVHom (c * n) (c * d) = c ^ 12 * kleinVHom n d := by
  unfold kleinVHom; ring

theorem exists_int_kleinVHom_ne_zero (β γ u₀ : K) (hV : kleinV u₀ ≠ 0) :
    ∃ l : ℤ, kleinVHom (β + l * u₀) (γ + l) ≠ 0 := by
  classical

  set r : K[X] := kleinVHom (C u₀ + C β * X) (1 + C γ * X) with hr
  have hr0 : r.eval 0 = kleinV u₀ := by
    rw [hr, ← coe_evalRingHom, map_kleinVHom]
    simp [kleinVHom, kleinV]
  have hrne : r ≠ 0 := fun h ↦ hV (by rw [← hr0, h, eval_zero])

  have hinj : Function.Injective (fun n : ℕ ↦ ((n + 1 : ℕ) : K)⁻¹) := by
    intro m n hmn
    have := inv_injective hmn
    exact_mod_cast (Nat.succ_injective (Nat.cast_injective this) : m = n)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((n + 1 : ℕ) : K)⁻¹ ∉ r.roots.toFinset := by
    by_contra h
    push Not at h
    exact not_injective_infinite_finite (fun n : ℕ ↦ (⟨_, h n⟩ : r.roots.toFinset))
      (fun m n hmn ↦ hinj (congrArg Subtype.val hmn))
  rw [Multiset.mem_toFinset, mem_roots hrne, IsRoot.def] at hn
  refine ⟨(n + 1 : ℕ), ?_⟩
  set L : K := ((n + 1 : ℕ) : K) with hL
  have hL0 : L ≠ 0 := by rw [hL]; exact_mod_cast Nat.succ_ne_zero n
  have e : kleinVHom (β + ((n + 1 : ℕ) : ℤ) * u₀) (γ + ((n + 1 : ℕ) : ℤ)) = L ^ 12 * r.eval L⁻¹ := by
    rw [hr, ← coe_evalRingHom, map_kleinVHom, coe_evalRingHom]
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_one]
    rw [← kleinVHom_smul_row]
    have hc : (((n + 1 : ℕ) : ℤ) : K) = L := by rw [hL]; push_cast; ring
    rw [hc]
    congr 1 <;> field_simp <;> ring
  rw [e]
  exact mul_ne_zero (pow_ne_zero 12 hL0) hn

end Slope

open RubinSilverberg in

theorem solution {K : Type*} [Field K] [CharZero K] (β γ u₀ : K) (hV : kleinV u₀ ≠ 0) : ∃ l : ℤ, kleinVHom (β + l * u₀) (γ + l) ≠ 0 :=
  Slope.exists_int_kleinVHom_ne_zero β γ u₀ hV

#print axioms solution

end S_RubinSilverberg_exists_int_kleinVHom_ne_zero
end P2MW
export P2MW.S_RubinSilverberg_exists_int_kleinVHom_ne_zero (solution)
