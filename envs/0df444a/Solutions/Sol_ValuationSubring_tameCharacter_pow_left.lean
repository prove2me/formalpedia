-- Prove2me | solution 1 for ValuationSubring.tameCharacter_pow_left
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/bc0963ce-13a3-5735-9528-5d288d3c21b8

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
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

namespace P2MW.S_ValuationSubring_tameCharacter_pow_left

namespace DichTameRows

open ValuationSubring
open scoped Pointwise

variable (P : ValuationSubring (AlgebraicClosure ℚ))

private theorem tameCharacter_of_mem (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : σ π / π ∈ P) : P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  exact dif_pos h

private theorem tameCharacter_of_not_mem (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : σ π / π ∉ P) : P.tameCharacter π σ = 0 := by
  unfold ValuationSubring.tameCharacter
  exact dif_neg h

private theorem tameCharacter_pow_left_of_mem (π : AlgebraicClosure ℚ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσπ : σ π / π ∈ P) (m : ℕ) :
    P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m := by
  have hq : σ (π ^ m) / π ^ m = (σ π / π) ^ m := by rw [map_pow, div_pow]
  have hmem : σ (π ^ m) / π ^ m ∈ P := by
    rw [hq]
    exact pow_mem hσπ m
  rw [tameCharacter_of_mem P _ _ hmem, tameCharacter_of_mem P _ _ hσπ, ← map_pow]
  congr 1
  exact Subtype.ext (by simp only [SubmonoidClass.coe_pow]; exact hq)

private theorem pow_not_mem {u : AlgebraicClosure ℚ} (hu : u ∉ P) {m : ℕ} (hm : 0 < m) : u ^ m ∉ P := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (ValuationSubring.zero_mem P)
  have hinv : u⁻¹ ∈ P := (P.mem_or_inv_mem u).resolve_left hu
  have hmax : (⟨u⁻¹, hinv⟩ : P) ∈ IsLocalRing.maximalIdeal P :=
    coe_mem_nonunits_iff.mp ((mem_nonunits_iff_or P).mpr (Or.inr (by rwa [inv_inv])))
  have hpow : (⟨u⁻¹, hinv⟩ : P) ^ m ∈ IsLocalRing.maximalIdeal P :=
    Ideal.pow_mem_of_mem _ hmax m hm
  have hnu : ((⟨u⁻¹, hinv⟩ : P) ^ m : P).1 ∈ P.nonunits := coe_mem_nonunits_iff.mpr hpow
  rw [SubmonoidClass.coe_pow] at hnu
  change (u⁻¹) ^ m ∈ P.nonunits at hnu
  rcases (mem_nonunits_iff_or P).mp hnu with h | h
  · exact absurd h (pow_ne_zero m (inv_ne_zero hu0))
  · rwa [inv_pow, inv_inv] at h

private theorem tameCharacter_pow_left (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : ℕ) : P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m := by
  by_cases hσπ : σ π / π ∈ P
  · exact tameCharacter_pow_left_of_mem P π hσπ m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : σ (π ^ 0) / π ^ 0 ∈ P := by
      rw [pow_zero, map_one, div_one]
      exact ValuationSubring.one_mem P
    rw [tameCharacter_of_mem P _ _ h1, pow_zero (P.tameCharacter π σ), ← map_one (IsLocalRing.residue P)]
    congr 1
    exact Subtype.ext (by change σ (π ^ 0) / π ^ 0 = 1; rw [pow_zero, map_one, div_one])
  · have hq : σ (π ^ m) / π ^ m = (σ π / π) ^ m := by rw [map_pow, div_pow]
    have hnot : σ (π ^ m) / π ^ m ∉ P := by
      rw [hq]
      exact pow_not_mem P hσπ hm
    rw [tameCharacter_of_not_mem P _ _ hnot, tameCharacter_of_not_mem P _ _ hσπ, zero_pow hm.ne']

end DichTameRows

theorem solution
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : ℕ) : P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m :=
  DichTameRows.tameCharacter_pow_left P π σ m

end S_ValuationSubring_tameCharacter_pow_left
end P2MW
export P2MW.S_ValuationSubring_tameCharacter_pow_left (solution)
