-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:56:46.182403+00:00
-- url     : https://prove2.me/submissions/2eb84663-7b62-45a7-a9aa-e029a80dc24f

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_SumLambdaWeight
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_IsTeich_lam_omega
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_lam_sum
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_lam_omega_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
variable (hv : v.Integers R)
include hv
variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution (AA : HopfOrder (C := C) R (ZMod p)) [CharZero C] :
    ∃ x1 : C, x1 ≠ 0 ∧ (fun t => x1 * ω t) ∈ AA.carrier ∧
      ∀ f ∈ AA.carrier, ∃ r : R, lam ω f = x1 * algebraMap R C r := by
  obtain ⟨B, hB, hA⟩ := AA.lat
  set b : ZMod p → ZMod p → C := fun j x => B x j with hb
  have hbA : ∀ j, b j ∈ AA.carrier := fun j => by
    rw [hA]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨j0, -, hj0⟩ :=
    Finset.exists_max_image Finset.univ (fun j => v (lam ω (b j))) Finset.univ_nonempty
  have hx1 : lam ω (b j0) ≠ 0 := by
    intro h0
    have hall : ∀ j, lam ω (b j) = 0 := fun j => by
      have h := hj0 j (Finset.mem_univ _)
      rw [h0, map_zero] at h
      exact (Valuation.zero_iff v).mp (le_antisymm h (zero_le))
    have hω' : ω = fun a => ∑ j, (B⁻¹ *ᵥ ω) j * b j a := by
      funext a
      have h := congrFun (show B *ᵥ (B⁻¹ *ᵥ ω) = ω by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]) a
      rw [← h]
      simp [Matrix.mulVec, dotProduct, hb, mul_comm]
    have hl : lam ω ω = 0 :=
      calc lam ω ω = lam ω (fun a => ∑ j, (B⁻¹ *ᵥ ω) j * b j a) := congrArg (lam ω) hω'
        _ = ∑ j, (B⁻¹ *ᵥ ω) j * lam ω (b j) := lam_sum ω _ b
        _ = 0 := by simp [hall]
    rw [hω.lam_omega] at hl
    exact sub_ne_zero.mpr (Nat.cast_ne_one.mpr hp.out.one_lt.ne') hl
  have hr : ∀ j, ∃ r : R, lam ω (b j) = lam ω (b j0) * algebraMap R C r := fun j => by
    obtain ⟨r, hr⟩ := hv.exists_of_le_one (r := lam ω (b j) / lam ω (b j0)) (by
      rw [map_div₀]
      exact div_le_one_of_le₀ (hj0 j (Finset.mem_univ _)) (zero_le))
    exact ⟨r, by rw [hr]; field_simp⟩
  choose r hr using hr
  refine ⟨lam ω (b j0), hx1, lam_omega_mem hv hω AA (hbA j0), ?_⟩
  intro f hf
  rw [hA] at hf
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨∑ j, c j * r j, ?_⟩
  have e : (∑ i, c i • b i) = fun a => ∑ j, algebraMap R C (c j) * b j a := by
    funext a
    simp [Finset.sum_apply, Algebra.smul_def]
  rw [e, lam_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hr j, map_mul]
  ring
end ReciprocityTheory.PGsh.Up.U3
