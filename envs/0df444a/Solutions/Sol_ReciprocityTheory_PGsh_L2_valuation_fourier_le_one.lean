-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.valuation_fourier_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:44:55.60956+00:00
-- url     : https://prove2.me/submissions/f77413c5-29d3-443d-8629-1025edd7953e

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde
import Theorems.Thm_ReciprocityTheory_PGsh_L2_cpow_mem
import Theorems.Thm_ReciprocityTheory_PGsh_L2_fourier_cpow
import Theorems.Thm_ReciprocityTheory_PGsh_L2_mem_dualLat_spanCols_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
private theorem nnreal_le_one_of_forall_pow_le {x M : NNReal} (h : ∀ k : ℕ, x ^ k ≤ M) : x ≤ 1 := by
  by_contra hx
  rw [not_le] at hx
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hx
  exact (not_lt.2 (h k)) hk
private theorem le_sum_sum {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ → NNReal) (i : ι)
    (j : κ) : f i j ≤ ∑ i, ∑ j, f i j :=
  (Finset.single_le_sum (f := fun j => f i j) (fun _ _ => zero_le) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, f i j) (fun _ _ => zero_le) (Finset.mem_univ i))
private theorem hopfOrder_exists_valuation_apply_le (v : Valuation C NNReal) (hv : v.Integers R)
    (AA : HopfOrder (C := C) R N) :
    ∃ M : NNReal, ∀ u ∈ dualLat AA.carrier, ∀ a, v (u a) ≤ M := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  refine ⟨∑ j, ∑ x, v (B⁻¹ j x), fun u hu a => ?_⟩
  rw [hA, mem_dualLat_spanCols_iff] at hu
  have hu' : u = (u ᵥ* B) ᵥ* B⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]
  rw [hu']
  change v (∑ j, (u ᵥ* B) j * B⁻¹ j a) ≤ _
  apply v.map_sum_le
  intro j _
  obtain ⟨r, hr⟩ := hu j
  rw [map_mul, ← hr]
  exact (mul_le_of_le_one_left (zero_le) (hv.map_le_one r)).trans
    (le_sum_sum (fun j x => v (B⁻¹ j x)) j a)
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (v : Valuation C NNReal) (hv : v.Integers R) {H : Type}
    (χ : H → AddChar N C) (AA : HopfOrder (C := C) R N) {u : N → C}
    (hu : u ∈ dualLat AA.carrier) (h : H) :
    v (fourier (R := R) (fun h a => χ h a) u h) ≤ 1 := by
  obtain ⟨M, hM⟩ := hopfOrder_exists_valuation_apply_le v hv AA
  have hχ : ∀ a, v (χ h a) ≤ 1 := fun a =>
    nnreal_le_one_of_forall_pow_le (M := ∑ b, v (χ h b)) fun k => by
      rw [← map_pow, ← AddChar.map_nsmul_eq_pow]
      exact Finset.single_le_sum (f := fun b => v (χ h b)) (fun _ _ => zero_le)
        (Finset.mem_univ _)
  apply nnreal_le_one_of_forall_pow_le (M := M)
  intro k
  rw [← map_pow, ← fourier_cpow (R := R) χ u h k, fourier_apply' (R := R)]
  apply v.map_sum_le
  intro a _
  rw [map_mul]
  exact (mul_le_of_le_one_right (zero_le) (hχ a)).trans
    (hM _ (cpow_mem AA hu k) a)
end ReciprocityTheory.PGsh.L2
