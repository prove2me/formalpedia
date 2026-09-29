-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/602d1bd9-e6ce-5e1f-94fc-389af4fb2da1

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd

set_option autoImplicit false

open scoped Quaternion
open Polynomial

namespace IntChi

variable {a b : ℚ}

def subalg {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) : Subalgebra ℤ ℍ[ℚ, a, b] where
  carrier := Λ
  mul_mem' hx hy := hΛ.mul_mem hx hy
  one_mem' := hΛ.one_mem
  add_mem' hx hy := Λ.add_mem hx hy
  zero_mem' := Λ.zero_mem
  algebraMap_mem' n := by
    rw [show algebraMap ℤ ℍ[ℚ, a, b] n = (n : ℤ) • (1 : ℍ[ℚ, a, b]) by rw [zsmul_one]; rfl]
    exact Λ.smul_mem n hΛ.one_mem

theorem aeval_charQuad (x : ℍ[ℚ, a, b]) :
    aeval x (X ^ 2 - C (QuaternionAlgebra.trd x) * X + C (QuaternionAlgebra.nrd x) : ℚ[X]) = 0 := by
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow]
  rw [sq, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul]
  have h1 := QuaternionAlgebra.add_star_eq_coe_trd x
  have h2 := QuaternionAlgebra.star_mul_eq_coe_nrd x
  have hc : ∀ s : ℚ, s • (1 : ℍ[ℚ, a, b]) = ((s : ℚ) : ℍ[ℚ, a, b]) := fun s => by
    rw [← QuaternionAlgebra.coe_one, QuaternionAlgebra.smul_coe, mul_one]
  have hc' : ∀ s : ℚ, s • x = ((s : ℚ) : ℍ[ℚ, a, b]) * x := fun s => (QuaternionAlgebra.coe_mul_eq_smul s x).symm
  rw [hc, hc', ← h1, ← h2, add_mul]
  abel

theorem main {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd x) ∧ ∃ t : ℤ, (t : ℚ) = QuaternionAlgebra.trd x := by
  set t := QuaternionAlgebra.trd x
  set n := QuaternionAlgebra.nrd x

  have hint : IsIntegral ℤ x := IsIntegral.of_mem_of_fg (subalg hΛ) hΛ.fg x hx
  obtain ⟨f, hfm, hfx⟩ := hint

  set g : ℚ[X] := X ^ 2 - C t * X + C n with hg
  have hgm : g.Monic := by
    rw [hg]; nontriviality ℚ
    refine Monic.add_of_left (Monic.sub_of_left (monic_X_pow 2) ?_) ?_
    · exact (degree_C_mul_X_le _).trans_lt (by rw [degree_X_pow]; norm_num)
    · exact (degree_C_le).trans_lt (by
        rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow] <;> [norm_num; exact (degree_C_mul_X_le _).trans_lt (by norm_num)])
  have hgdeg : g.natDegree = 2 := by
    rw [hg]; compute_degree!
  have hgx : aeval x g = 0 := aeval_charQuad x
  have hintQ : IsIntegral ℚ x := ⟨g, hgm, by rw [← aeval_def]; exact hgx⟩
  have hfx' : aeval x f = 0 := by rw [aeval_def]; exact hfx
  set μ := minpoly ℚ x with hμ
  have hμg : μ ∣ g := minpoly.dvd ℚ x hgx
  have hμf : μ ∣ f.map (algebraMap ℤ ℚ) := by
    refine minpoly.dvd ℚ x ?_
    rw [aeval_map_algebraMap]; exact hfx'
  have hμm : μ.Monic := minpoly.monic hintQ

  obtain ⟨μZ, hμZ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hfm hμf
  rw [hμm.leadingCoeff, C_1, mul_one] at hμZ

  have hμpos : 0 < μ.natDegree := minpoly.natDegree_pos hintQ
  have hμle : μ.natDegree ≤ 2 := by
    rw [← hgdeg]; exact natDegree_le_of_dvd hμg hgm.ne_zero
  have hcoeffZ : ∀ i, ∃ z : ℤ, (z : ℚ) = μ.coeff i := fun i => ⟨μZ.coeff i, by rw [← hμZ, coeff_map]; rfl⟩
  rcases Nat.lt_or_ge μ.natDegree 2 with h1 | h2
  ·
    have hd1 : μ.natDegree = 1 := by omega
    have hμeq := hμm.eq_X_add_C hd1
    obtain ⟨c, hc⟩ := hcoeffZ 0
    have hxc : x = (((-c : ℤ) : ℚ) : ℍ[ℚ, a, b]) := by
      have := minpoly.aeval ℚ x
      rw [← hμ, hμeq] at this
      simp only [map_add, aeval_X, aeval_C] at this
      rw [Algebra.algebraMap_eq_smul_one, ← hc] at this
      have : x = -((c : ℚ) • (1 : ℍ[ℚ, a, b])) := eq_neg_of_add_eq_zero_left this
      rw [this, ← QuaternionAlgebra.coe_one, QuaternionAlgebra.smul_coe, mul_one, ← QuaternionAlgebra.coe_neg]
      push_cast; ring_nf
    refine ⟨⟨(-c) ^ 2, ?_⟩, ⟨2 * (-c), ?_⟩⟩
    · show ((((-c) ^ 2 : ℤ)) : ℚ) = QuaternionAlgebra.nrd x
      rw [hxc, QuaternionAlgebra.nrd_coe]; push_cast; ring
    · show (((2 * (-c) : ℤ)) : ℚ) = QuaternionAlgebra.trd x
      rw [hxc]; simp [QuaternionAlgebra.trd]
  ·
    have hd2 : μ.natDegree = 2 := le_antisymm hμle h2
    have hμg' : μ = g := by
      refine eq_of_monic_of_associated hμm hgm ?_
      exact associated_of_dvd_of_natDegree_le hμg hgm.ne_zero (by rw [hd2, hgdeg])
    obtain ⟨z0, hz0⟩ := hcoeffZ 0
    obtain ⟨z1, hz1⟩ := hcoeffZ 1
    have hg0 : g.coeff 0 = n := by rw [hg]; simp
    have hg1 : g.coeff 1 = -t := by rw [hg]; simp [coeff_X_pow, coeff_C_mul, coeff_X]
    refine ⟨⟨z0, ?_⟩, ⟨-z1, ?_⟩⟩
    · rw [hz0, hμg', hg0]
    · push_cast; rw [hz1, hμg', hg1, neg_neg]

end IntChi

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) :
    (∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd x) ∧ ∃ t : ℤ, (t : ℚ) = QuaternionAlgebra.trd x :=
  IntChi.main hΛ hx

end S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd (solution)
