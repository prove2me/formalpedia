-- Prove2me | solution 1 for ValuationSubring.tameCharacter_eq_of_div_mem_of_div_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/364ac75e-2950-56aa-b457-19d63fc3aad9

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem

namespace DichTameRows

open ValuationSubring
open scoped Pointwise

variable (P : ValuationSubring (AlgebraicClosure ℚ))

private theorem tameCharacter_of_mem (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : σ π / π ∈ P) : P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  exact dif_pos h

private theorem apply_mem_of_mem_decompositionSubgroup {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.decompositionSubgroup ℚ) {x : AlgebraicClosure ℚ} (hx : x ∈ P) : σ x ∈ P := by
  have h : σ • P = P := MulAction.mem_stabilizer_iff.mp hσ
  have hmem : σ • x ∈ ((σ • P : ValuationSubring (AlgebraicClosure ℚ)) : Set (AlgebraicClosure ℚ)) := by
    rw [coe_pointwise_smul]
    exact Set.smul_mem_smul_set hx
  rw [h] at hmem
  exact hmem

private theorem mem_decompositionSubgroup_of_mem_inertiaSubgroupIn {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) : σ ∈ P.decompositionSubgroup ℚ := by
  obtain ⟨σ', _, rfl⟩ := Subgroup.mem_map.mp hσ
  exact σ'.2

private theorem residue_apply_eq_of_mem_inertiaSubgroupIn {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) {x : AlgebraicClosure ℚ} (hx : x ∈ P)
    (hσx : σ x ∈ P) :
    IsLocalRing.residue P ⟨σ x, hσx⟩ = IsLocalRing.residue P ⟨x, hx⟩ := by
  obtain ⟨σ', hσ', rfl⟩ := Subgroup.mem_map.mp hσ
  have hker : MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (IsLocalRing.ResidueField P) σ' = 1 :=
    (MonoidHom.mem_ker).mp hσ'
  have h1 : (MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (IsLocalRing.ResidueField P) σ')
      (IsLocalRing.residue P ⟨x, hx⟩) = IsLocalRing.residue P ⟨x, hx⟩ := by
    rw [hker]
    rfl

  have h2 : IsLocalRing.residue P (σ' • (⟨x, hx⟩ : P)) = IsLocalRing.residue P ⟨x, hx⟩ := h1
  have hact : (σ' • (⟨x, hx⟩ : P) : P) = ⟨(P.decompositionSubgroup ℚ).subtype σ' x, hσx⟩ := Subtype.ext rfl
  rw [hact] at h2
  exact h2

private theorem apply_div_mem_of_mem_decompositionSubgroup {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.decompositionSubgroup ℚ) {x : AlgebraicClosure ℚ} (hx : x ≠ 0) :
    σ x / x ∈ P ∧ x / σ x ∈ P := by
  have hv := ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup P hσ x
  have hx' : P.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  refine ⟨(P.valuation_le_one_iff _).mp (le_of_eq ?_), (P.valuation_le_one_iff _).mp (le_of_eq ?_)⟩
  · rw [map_div₀, hv, div_self hx']
  · rw [map_div₀, hv, div_self hx']

private theorem tameCharacter_eq_of_div_mem_of_div_mem (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0) (hπ' : π' ≠ 0)
    (hu : π' / π ∈ P) (hu' : π / π' ∈ P) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ := by
  have hσD : σ ∈ P.decompositionSubgroup ℚ := mem_decompositionSubgroup_of_mem_inertiaSubgroupIn P hσ
  have hσπ : σ π / π ∈ P := (apply_div_mem_of_mem_decompositionSubgroup P hσD hπ).1
  have hσu : σ (π' / π) ∈ P := apply_mem_of_mem_decompositionSubgroup P hσD hu
  have hσπ0 : σ π ≠ 0 := (map_ne_zero σ).mpr hπ
  have hcoc : σ π' / π' = (σ (π' / π) * (π / π')) * (σ π / π) := by
    rw [map_div₀]
    field_simp
  have hmem : σ π' / π' ∈ P := by
    rw [hcoc]
    exact mul_mem (mul_mem hσu hu') hσπ
  rw [tameCharacter_of_mem P π' σ hmem, tameCharacter_of_mem P π σ hσπ]
  have hprod : (⟨σ π' / π', hmem⟩ : P) = (⟨σ (π' / π), hσu⟩ * ⟨π / π', hu'⟩) * ⟨σ π / π, hσπ⟩ :=
    Subtype.ext (by simpa only [MulMemClass.coe_mul] using hcoc)
  rw [hprod, map_mul, map_mul, residue_apply_eq_of_mem_inertiaSubgroupIn P hσ hu hσu, ← map_mul]
  have hone : (⟨π' / π, hu⟩ : P) * ⟨π / π', hu'⟩ = 1 := Subtype.ext (by
    change π' / π * (π / π') = 1
    rw [div_mul_div_comm, mul_comm π' π, div_self (mul_ne_zero hπ hπ')])
  rw [hone, map_one, one_mul]

end DichTameRows

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π π' : AlgebraicClosure ℚ) (hπ : π ≠ 0) (hπ' : π' ≠ 0)
    (hu : π' / π ∈ P) (hu' : π / π' ∈ P) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π' σ = P.tameCharacter π σ :=
  DichTameRows.tameCharacter_eq_of_div_mem_of_div_mem P π π' hπ hπ' hu hu' hσ

end S_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem
end P2MW
export P2MW.S_ValuationSubring_tameCharacter_eq_of_div_mem_of_div_mem (solution)
