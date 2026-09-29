-- Prove2me | solution 1 for ValuationSubring.isOfFinOrder_units_residueField_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5778b646-d730-5d5d-ad16-ba1441bd265d

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime
set_option autoImplicit false

namespace FinOrdResidue

open Polynomial

def wt (g : ℤ[X]) : ℕ := g.support.sum fun i => (g.coeff i).natAbs

lemma wt_C_mul_lt {p : ℕ} (hp : 1 < p) {g : ℤ[X]} (hg : g ≠ 0) : wt g < wt (C (p : ℤ) * g) := by
  have hsupp : (C (p : ℤ) * g).support = g.support := by
    ext i
    simp only [mem_support_iff, coeff_C_mul, ne_eq, mul_eq_zero, Int.natCast_eq_zero, not_or]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  unfold wt
  rw [hsupp]
  apply Finset.sum_lt_sum
  · intro i _
    rw [coeff_C_mul, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · obtain ⟨i, hi⟩ : g.support.Nonempty := Polynomial.support_nonempty.mpr hg
    refine ⟨i, hi, ?_⟩
    rw [coeff_C_mul, Int.natAbs_mul, Int.natAbs_natCast]
    have : (g.coeff i).natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using mem_support_iff.mp hi
    calc (g.coeff i).natAbs = 1 * (g.coeff i).natAbs := (one_mul _).symm
      _ < p * (g.coeff i).natAbs := Nat.mul_lt_mul_of_pos_right hp (Nat.pos_of_ne_zero this)

theorem exists_intPoly_map_ne_zero (p : ℕ) [Fact p.Prime] (a : AlgebraicClosure ℚ) :
    ∃ q : ℤ[X], aeval a q = 0 ∧ q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  have hp := (Fact.out : p.Prime)

  have halg : IsAlgebraic ℚ a := by
    convert (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a
    rfl
    rfl
  obtain ⟨f, hf0, hfa⟩ := halg
  let g : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f
  have hga : aeval a g = 0 := IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) f hfa
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    have := IsLocalization.integerNormalization_eq_zero_iff (M := nonZeroDivisors ℤ) (p := f) le_rfl
    exact this.mp h

  classical
  have hex : ∃ n, ∃ q : ℤ[X], q ≠ 0 ∧ aeval a q = 0 ∧ wt q = n := ⟨_, g, hg0, hga, rfl⟩
  obtain ⟨q, hq0, hqa, hqw⟩ := Nat.find_spec hex
  refine ⟨q, hqa, ?_⟩
  intro hmap

  have hdvd : (C (p : ℤ)) ∣ q := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have : (q.map (Int.castRingHom (ZMod p))).coeff i = 0 := by rw [hmap, coeff_zero]
    rw [coeff_map, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact this
  obtain ⟨q', hq'⟩ := hdvd
  have hq'0 : q' ≠ 0 := by rintro rfl; exact hq0 (by rw [hq', mul_zero])
  have hq'a : aeval a q' = 0 := by
    have : aeval a q = (p : AlgebraicClosure ℚ) * aeval a q' := by
      rw [hq', map_mul, aeval_C]; simp
    rw [hqa] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (by exact_mod_cast hp.ne_zero)
  have hlt : wt q' < wt q := by rw [hq']; exact wt_C_mul_lt hp.one_lt hq'0
  have hmin := Nat.find_min hex (hqw ▸ hlt)
  exact hmin ⟨q', hq'0, hq'a, rfl⟩

end FinOrdResidue

open FinOrdResidue Polynomial in
theorem solution (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (u : (IsLocalRing.ResidueField ↥A)ˣ) : IsOfFinOrder u := by
  classical
  have hp := (Fact.out : p.Prime)
  set k := IsLocalRing.ResidueField ↥A

  have hpA : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hval : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
    have h1 : A.valuation (((p : ℕ) : ↥A) : AlgebraicClosure ℚ) = 1 := (A.valuation_eq_one_iff _).mp hu
    simp only [SubringClass.coe_natCast] at h1
    exact (lt_irrefl _) (h1 ▸ hval)
  have hpk : (p : k) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥A), IsLocalRing.residue_eq_zero_iff]; exact hpA
  have hc : ringChar k = p := by
    have hdvd := ringChar.dvd hpk
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  haveI : CharP k p := ringChar.of_eq hc
  letI : Algebra (ZMod p) k := ZMod.algebra k p

  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (u : k)
  obtain ⟨q, hqa, hqmap⟩ := exists_intPoly_map_ne_zero p (a : AlgebraicClosure ℚ)

  have hqA : aeval a q = 0 := by
    have hinj : Function.Injective ((A.subtype).toIntAlgHom) := Subtype.val_injective
    apply hinj
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact hqa

  have hqk : aeval (u : k) (q.map (Int.castRingHom (ZMod p))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap (ZMod p) k).comp (Int.castRingHom (ZMod p)) = Int.castRingHom k :=
      RingHom.ext_int _ _
    rw [hcomp, ← ha]
    have h2 : Polynomial.eval₂ (Int.castRingHom k) (IsLocalRing.residue ↥A a) q =
        ((IsLocalRing.residue ↥A : ↥A →+* k).toIntAlgHom) (aeval a q) := by
      rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def]
      congr 1
      try exact (RingHom.ext_int _ _)
    rw [h2, hqA, map_zero]

  have halgu : IsAlgebraic (ZMod p) (u : k) := ⟨_, hqmap, hqk⟩
  have hint : IsIntegral (ZMod p) (u : k) := halgu.isIntegral
  let S := Algebra.adjoin (ZMod p) {(u : k)}
  haveI : Module.Finite (ZMod p) ↥S := Algebra.finite_adjoin_simple_of_isIntegral hint
  haveI : Finite ↥S := Module.finite_of_finite (ZMod p)
  have huS : (u : k) ∈ S := Algebra.subset_adjoin rfl

  let f : ℕ → ↥S := fun n => ⟨(u : k) ^ n, pow_mem huS n⟩
  obtain ⟨i, j, hij, hfij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hpow : (u : k) ^ i = (u : k) ^ j := by
    have := congrArg Subtype.val hfij; simpa [f] using this
  have hunits : u ^ i = u ^ j := Units.ext (by simpa [Units.val_pow_eq_pow_val] using hpow)
  rw [isOfFinOrder_iff_pow_eq_one]
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · refine ⟨j - i, by omega, ?_⟩
    have : u ^ i * u ^ (j - i) = u ^ i * 1 := by rw [mul_one, ← pow_add, Nat.add_sub_cancel' hlt.le]; exact hunits.symm
    exact mul_left_cancel this
  · refine ⟨i - j, by omega, ?_⟩
    have : u ^ j * u ^ (i - j) = u ^ j * 1 := by rw [mul_one, ← pow_add, Nat.add_sub_cancel' hgt.le]; exact hunits
    exact mul_left_cancel this

end S_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime (solution)
