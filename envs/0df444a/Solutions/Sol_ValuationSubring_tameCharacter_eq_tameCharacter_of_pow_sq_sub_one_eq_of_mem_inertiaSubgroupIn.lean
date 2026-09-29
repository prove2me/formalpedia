-- Prove2me | solution 1 for ValuationSubring.tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/74a06bc5-c517-558d-91e1-8be36e881a35

import Mathlib
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn

set_option autoImplicit false

namespace KCharAux

open IsLocalRing

variable {L : Type*} [Field L]

theorem mem_of_pow_eq_one (A : ValuationSubring L) {x : L} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n = 1) :
    x ∈ A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact h
  · have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hx
      exact zero_ne_one hx
    have h1 : x * x ^ (n - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn), hx]
    have key : (x⁻¹) ^ (n - 1) = x := by
      rw [inv_pow]
      exact (eq_inv_of_mul_eq_one_left h1).symm
    rw [← key]
    exact pow_mem h _

theorem eq_one_of_pow_eq_one_of_residue_eq_one {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {μ : A} {n : ℕ} (hμ : μ ^ n = 1) (hres : residue A μ = 1) (hn : (n : ResidueField A) ≠ 0) :
    μ = 1 := by
  have hgeom : (∑ i ∈ Finset.range n, μ ^ i) * (μ - 1) = 0 := by
    rw [geom_sum_mul, hμ, sub_self]
  rcases mul_eq_zero.mp hgeom with h | h
  · exfalso
    apply hn
    have := congrArg (residue A) h
    rw [map_sum, map_zero] at this
    simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    exact this
  · exact sub_eq_zero.mp h

end KCharAux

open KCharAux IsLocalRing in
theorem solution
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π π' : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (hπ' : π' ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    P.tameCharacter π τ = P.tameCharacter π' τ := by
  classical
  have hq : q.Prime := Fact.out
  set n : ℕ := q ^ 2 - 1 with hndef
  have hn0 : n ≠ 0 := by
    have : 2 ≤ q := hq.two_le
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  have hqL : (q : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hπ
    exact hqL hπ.symm
  have hπ'0 : π' ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hπ'
    exact hqL hπ'.symm

  set ζ : AlgebraicClosure ℚ := π' / π with hζdef
  have hζn : ζ ^ n = 1 := by
    rw [hζdef, div_pow, hπ, hπ', div_self hqL]
  have hζ0 : ζ ≠ 0 := div_ne_zero hπ'0 hπ0
  have hζP : ζ ∈ P := mem_of_pow_eq_one P hn0 hζn

  obtain ⟨g, hg, hgτ⟩ := Subgroup.mem_map.mp hτ
  have hgτ' : ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) = τ := hgτ

  set z : P := ⟨ζ, hζP⟩ with hzdef
  have hzn : z ^ n = 1 := by
    apply Subtype.ext
    show ((z ^ n : P) : AlgebraicClosure ℚ) = 1
    exact hζn
  set w : P := g • z with hwdef
  have hw_coe : (w : AlgebraicClosure ℚ) = τ ζ := by
    rw [← hgτ']
    rfl
  have hwn : w ^ n = 1 := by
    rw [hwdef, ← smul_pow', hzn, smul_one]

  have hres : residue P w = residue P z := by
    rw [hwdef, ResidueField.residue_smul]
    have hker : MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (ResidueField P) g = 1 :=
      (MonoidHom.mem_ker).mp hg
    have := RingEquiv.congr_fun (congrArg (fun e : ResidueField P ≃+* ResidueField P => e) hker) (residue P z)
    simpa [MulSemiringAction.toRingAut_apply] using this

  have hqP : residue P (q : P) = 0 := by
    rw [residue_eq_zero_iff]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    simp at hP ⊢
    exact hP
  have hnres : (n : ResidueField P) ≠ 0 := by
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    have : (n : ResidueField P) = -1 := by
      rw [hndef, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
      have : ((q : ℕ) : ResidueField P) = 0 := by
        rw [← map_natCast (residue P) q]
        exact hqP
      rw [this, zero_pow two_ne_zero, zero_sub]
    rw [this]
    exact neg_ne_zero.mpr one_ne_zero

  set μ : P := w * z ^ (n - 1) with hμdef
  have hzz : z * z ^ (n - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0), hzn]
  have hμn : μ ^ n = 1 := by
    rw [hμdef, mul_pow, hwn, one_mul, ← pow_mul, mul_comm, pow_mul, hzn, one_pow]
  have hμres : residue P μ = 1 := by
    rw [hμdef, map_mul, hres, ← map_mul, hzz, map_one]
  have hμ1 : μ = 1 := eq_one_of_pow_eq_one_of_residue_eq_one hμn hμres hnres
  have hwz : w = z := by
    calc w = w * (z * z ^ (n - 1)) := by rw [hzz, mul_one]
      _ = z * μ := by rw [hμdef]; ring
      _ = z := by rw [hμ1, mul_one]
  have hτζ : τ ζ = ζ := by
    rw [← hw_coe, hwz]

  have hquot : τ π / π = τ π' / π' := by
    have hπ'eq : π' = ζ * π := by rw [hζdef, div_mul_cancel₀ _ hπ0]
    rw [hπ'eq, map_mul, hτζ, mul_div_mul_left _ _ hζ0]
  unfold ValuationSubring.tameCharacter
  exact hquot ▸ rfl

end S_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn
end P2MW
export P2MW.S_ValuationSubring_tameCharacter_eq_tameCharacter_of_pow_sq_sub_one_eq_of_mem_inertiaSubgroupIn (solution)
