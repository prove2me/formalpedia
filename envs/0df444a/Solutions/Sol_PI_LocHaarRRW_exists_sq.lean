-- Prove2me | solution 1 for PI.LocHaarRRW.exists_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:08.844988+00:00
-- url     : https://prove2.me/submissions/9d8dc176-5b91-4455-b7f6-b93944831255

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
import Theorems.Thm_PI_LocHaarRRW_inv_mem_integer
import Theorems.Thm_PI_LocHaarRRW_pair_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
open PI PI.LocHaarRRW
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]
namespace PI.LocHaarRRW
theorem _root_.solution [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V] :
    ∃ θ : V, ∃ d : K, θ ∉ (algebraMap K V).range ∧ θ * θ = algebraMap K V d ∧ d ≠ 0 ∧
      d ∈ 𝒪[K] := by
  have hpos : 0 < Module.finrank K V := by rw [hr]; norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  haveI : Module.Finite K V := Module.finite_of_finrank_pos hpos
  set ι := algebraMap K V with hι
  obtain ⟨θ0, hθ0⟩ : ∃ θ0 : V, θ0 ∉ ι.range := by
    by_contra hall
    push Not at hall
    have htop : (⊤ : Submodule K V) = Submodule.span K {1} := by
      ext x
      simp only [Submodule.mem_top, true_iff, Submodule.mem_span_singleton]
      obtain ⟨c, rfl⟩ := hall x
      exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩
    have h1 := finrank_span_singleton (K := K) (one_ne_zero : (1 : V) ≠ 0)
    rw [← htop, finrank_top, hr] at h1
    norm_num at h1
  have hli : LinearIndependent K ![(1 : V), θ0] :=
    LinearIndependent.pair_iff.mpr (pair_indep hθ0)
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ0 := by simp [b]
  have hb := b.sum_repr (θ0 * θ0)
  rw [Fin.sum_univ_two, hb0, hb1] at hb
  set α := b.repr (θ0 * θ0) 0
  set β := b.repr (θ0 * θ0) 1
  have hsq : θ0 * θ0 = ι α + ι β * θ0 := by
    rw [← hb, Algebra.smul_def, Algebra.smul_def, mul_one]
  have h2 : ι β = 2 * ι (β / 2) := by
    rw [← map_ofNat ι 2, ← map_mul]; congr 1; field_simp
  set θ1 := θ0 - ι (β / 2) with hθ1def
  have hθ1 : θ1 * θ1 = ι (α + (β / 2) ^ 2) := by
    rw [hθ1def, map_add, map_pow]
    linear_combination hsq + θ0 * h2
  have hθ1r : θ1 ∉ ι.range := by
    rintro ⟨c, hc⟩
    apply hθ0
    refine ⟨c + β / 2, ?_⟩
    rw [map_add, hc, hθ1def]; ring
  have hd1 : α + (β / 2) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hθ1
    have hn : IsNilpotent θ1 := ⟨2, by rw [pow_two]; exact hθ1⟩
    apply hθ1r
    exact ⟨0, by rw [map_zero, IsReduced.eq_zero θ1 hn]⟩
  set d1 := α + (β / 2) ^ 2
  by_cases hdO : d1 ∈ 𝒪[K]
  · exact ⟨θ1, d1, hθ1r, hθ1, hd1, hdO⟩
  · refine ⟨ι d1⁻¹ * θ1, d1⁻¹, ?_, ?_, inv_ne_zero hd1, inv_mem_integer hdO⟩
    · rintro ⟨c, hc⟩
      apply hθ1r
      refine ⟨d1 * c, ?_⟩
      rw [map_mul, hc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd1, map_one, one_mul]
    · calc ι d1⁻¹ * θ1 * (ι d1⁻¹ * θ1) = ι d1⁻¹ * ι d1⁻¹ * (θ1 * θ1) := by ring
        _ = ι d1⁻¹ := by
          rw [hθ1, ← map_mul, ← map_mul]; congr 1; field_simp
end PI.LocHaarRRW
