-- Prove2me | solution 1 for ValuationSubring.exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9420d381-38fb-5bf8-86a6-b369fba245cc

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime

set_option autoImplicit false
set_option linter.unusedVariables false

open IsLocalRing

namespace ResiduePairLift
namespace Inertia

open IsLocalRing

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem natCast_mem_maximalIdeal {p : ℕ} (hA : A.LiesOverPrime p) :
    ((p : ℕ) : A) ∈ maximalIdeal A := by
  have h : A.valuation (((p : ℕ) : A) : AlgebraicClosure ℚ) < 1 := by
    have h' : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rw [ValuationSubring.mem_nonunits_iff] at h'
    simpa using h'
  exact (A.valuation_lt_one_iff _).mpr h

theorem isUnit_natCast {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : ℕ) : A) := by
  have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn).symm
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hcop)
  have h1 : (u : A) * ((n : ℕ) : A) + (v : A) * ((p : ℕ) : A) = 1 := by
    have := congrArg (fun z : ℤ => (z : A)) huv
    push_cast at this
    exact this
  have hmem : (v : A) * ((p : ℕ) : A) ∈ maximalIdeal A :=
    (maximalIdeal A).mul_mem_left _ (natCast_mem_maximalIdeal A hA)
  have hunit : IsUnit ((u : A) * ((n : ℕ) : A)) := by
    have e : (u : A) * ((n : ℕ) : A) = 1 - (v : A) * ((p : ℕ) : A) := by
      rw [← h1]; ring
    rw [e]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hmem
  exact isUnit_of_mul_isUnit_right hunit

theorem eq_one_of_pow_eq_one_of_residue_eq_one {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    {n : ℕ} (hn : ¬ p ∣ n) {u : A} (hu : u ^ n = 1) (hres : residue A u = 1) : u = 1 := by
  have hgeom : (∑ i ∈ Finset.range n, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  have hsum : residue A (∑ i ∈ Finset.range n, u ^ i) = residue A ((n : ℕ) : A) := by
    rw [map_sum, map_natCast]
    simp [map_pow, hres]
  have hunit : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    by_contra hnu
    have hmem : (∑ i ∈ Finset.range n, u ^ i) ∈ maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h0 : residue A (∑ i ∈ Finset.range n, u ^ i) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    rw [hsum] at h0
    have hn' : ((n : ℕ) : A) ∈ maximalIdeal A := (Ideal.Quotient.eq_zero_iff_mem).mp h0
    exact ((IsLocalRing.mem_maximalIdeal _).mp hn') (isUnit_natCast A hp hA hn)
  have := (hunit.mul_right_eq_zero).mp hgeom
  exact sub_eq_zero.mp this

theorem eq_of_pow_eq_one_of_residue_eq {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    {n : ℕ} (hn : ¬ p ∣ n) {a b : A} (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hres : residue A a = residue A b) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0

  have hu : (a * b ^ m) ^ (m + 1) = 1 := by
    rw [mul_pow, ha, one_mul, ← pow_mul, mul_comm m (m + 1), pow_mul, hb, one_pow]
  have hures : residue A (a * b ^ m) = 1 := by
    rw [map_mul, map_pow, hres, ← map_pow, ← map_mul, ← pow_succ', hb, map_one]
  have h1 : a * b ^ m = 1 := eq_one_of_pow_eq_one_of_residue_eq_one A hp hA hn hu hures
  calc a = a * b ^ m * b := by rw [mul_assoc, ← pow_succ, hb, mul_one]
    _ = b := by rw [h1, one_mul]

theorem mem_of_pow_eq_one {n : ℕ} (hn0 : n ≠ 0) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) :
    ζ ∈ A := by
  apply A.mem_of_valuation_le_one
  have h : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζ, map_one]
  by_contra hlt
  push Not at hlt
  have h2 : 1 < A.valuation ζ ^ n := one_lt_pow₀ hlt hn0
  rw [h] at h2
  exact lt_irrefl _ h2

theorem exists_decomposition_of_mem_inertiaSubgroupIn
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    ∃ g : A.decompositionSubgroup ℚ, (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) = σ ∧
      ∀ y : ResidueField A, g • y = y := by
  unfold ValuationSubring.inertiaSubgroupIn at hσ
  rw [Subgroup.mem_map] at hσ
  obtain ⟨g, hgI, hgσ⟩ := hσ
  refine ⟨g, hgσ, fun y => ?_⟩
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (ResidueField A) g = 1 :=
    (MonoidHom.mem_ker).mp hgI
  have h2 := congrArg (fun e : RingAut (ResidueField A) => e y) h1
  simpa [MulSemiringAction.toRingAut_apply] using h2

theorem forall_inertia_apply_eq_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    {n : ℕ} (hn : ¬ p ∣ n) (hn0 : n ≠ 0) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ ζ = ζ := by
  intro σ hσ
  obtain ⟨g, rfl, hfix⟩ := exists_decomposition_of_mem_inertiaSubgroupIn A hσ
  set a : A := ⟨ζ, mem_of_pow_eq_one A hn0 hζ⟩ with ha_def
  have ha : a ^ n = 1 := by
    ext; simp [ha_def, hζ]
  have hb : (g • a) ^ n = 1 := by
    rw [← smul_pow', ha, smul_one]
  have hres : residue A (g • a) = residue A a := by
    rw [ResidueField.residue_smul, hfix]
  have hab : g • a = a := eq_of_pow_eq_one_of_residue_eq A hp hA hn hb ha hres
  have hcoe : ((g • a : A) : AlgebraicClosure ℚ) =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ζ := rfl
  rw [← hcoe, hab]

theorem exists_residue_eq_and_forall_inertia_apply_eq {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (x : ResidueField A) :
    ∃ a : A, residue A a = x ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = a := by
  classical
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx], fun σ _ => by simp⟩

  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime A hA
  obtain ⟨m, hpm, hm0, hxm⟩ : ∃ m : ℕ, ¬ p ∣ m ∧ m ≠ 0 ∧ x ^ m = 1 := by
    set y : AlgebraicClosure (ZMod p) := e x with hy
    have hy0 : y ≠ 0 := by
      intro h; apply hx
      simpa [hy] using (e.injective (h.trans (map_zero e).symm))
    have hyint : IsIntegral (ZMod p) y := (Algebra.IsIntegral.isIntegral (R := ZMod p) y)
    haveI : FiniteDimensional (ZMod p) (IntermediateField.adjoin (ZMod p) ({y} : Set (AlgebraicClosure (ZMod p)))) :=
      IntermediateField.adjoin.finiteDimensional hyint
    set F := IntermediateField.adjoin (ZMod p) ({y} : Set (AlgebraicClosure (ZMod p))) with hF
    haveI : Finite F := Module.finite_of_finite (ZMod p)
    letI : Fintype F := Fintype.ofFinite F
    have hyF : y ∈ F := IntermediateField.subset_adjoin _ _ (Set.mem_singleton y)
    set z : F := ⟨y, hyF⟩ with hz
    have hz0 : z ≠ 0 := by
      intro h; apply hy0; simpa [hz] using congrArg (fun w : F => (w : AlgebraicClosure (ZMod p))) h
    have hzpow : z ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one z hz0
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Fintype.card F = p ^ k := by
      haveI : CharP F p := charP_of_injective_algebraMap (algebraMap (ZMod p) F).injective p
      obtain ⟨k, hk⟩ := FiniteField.card F p
      exact ⟨k, hk.2⟩
    have hcard : 1 < Fintype.card F := Fintype.one_lt_card
    refine ⟨Fintype.card F - 1, ?_, ?_, ?_⟩
    ·
      intro hdvd
      have hk0 : k ≠ 0 := by
        rintro rfl; rw [pow_zero] at hk; omega
      have hpk : p ∣ p ^ k := dvd_pow_self p hk0
      rw [hk] at hdvd
      have hpos : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
      have hpk' : p ∣ (p ^ k - 1) + 1 := by rwa [Nat.sub_add_cancel hpos]
      have : p ∣ 1 := (Nat.dvd_add_right hdvd).mp hpk'
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · omega
    ·
      have hy' : y ^ (Fintype.card F - 1) = 1 := by
        have := congrArg (fun w : F => (w : AlgebraicClosure (ZMod p))) hzpow
        simpa [hz] using this
      apply e.injective
      rw [map_pow, map_one]
      exact hy'

  have hm_ne : ((m : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hm0
  set S : Finset (AlgebraicClosure ℚ) := (Polynomial.nthRoots m (1 : AlgebraicClosure ℚ)).toFinset with hS
  have hSmem : ∀ s ∈ S, s ^ m = 1 := by
    intro s hs
    rw [hS, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0)] at hs
    exact hs
  have hScard : S.card = m := by
    have hnodup : (Polynomial.nthRoots m (1 : AlgebraicClosure ℚ)).Nodup := by
      unfold Polynomial.nthRoots
      exact Polynomial.nodup_roots
        ((Polynomial.separable_X_pow_sub_C (1 : AlgebraicClosure ℚ) hm_ne one_ne_zero))
    rw [hS, Multiset.toFinset_card_of_nodup hnodup]
    unfold Polynomial.nthRoots
    have hsplit := IsAlgClosed.splits (Polynomial.X ^ m - Polynomial.C (1 : AlgebraicClosure ℚ))
    rw [← Polynomial.Splits.natDegree_eq_card_roots hsplit, Polynomial.natDegree_X_pow_sub_C]

  let lift : AlgebraicClosure ℚ → A := fun s =>
    if h : s ^ m = 1 then ⟨s, mem_of_pow_eq_one A hm0 h⟩ else 0
  have hlift : ∀ s ∈ S, ((lift s : A) : AlgebraicClosure ℚ) = s := by
    intro s hs; simp [lift, hSmem s hs]
  have hliftpow : ∀ s ∈ S, (lift s) ^ m = 1 := by
    intro s hs; ext; simp [hlift s hs, hSmem s hs]
  have hinj : Set.InjOn (fun s => residue A (lift s)) (S : Set (AlgebraicClosure ℚ)) := by
    intro s hs t ht hst
    have := eq_of_pow_eq_one_of_residue_eq A hp hA hpm (hliftpow s hs) (hliftpow t ht) hst
    have := congrArg (fun w : A => (w : AlgebraicClosure ℚ)) this
    simpa [hlift s hs, hlift t ht] using this
  set T : Finset (ResidueField A) := (Polynomial.nthRoots m (1 : ResidueField A)).toFinset with hT
  have himage : S.image (fun s => residue A (lift s)) ⊆ T := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0), ← map_pow,
      hliftpow s hs, map_one]
  have hTcard : T.card ≤ m := by
    rw [hT]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)
  have hScard' : (S.image (fun s => residue A (lift s))).card = m := by
    rw [Finset.card_image_of_injOn hinj, hScard]
  have hxT : x ∈ T := by
    rw [hT, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm0)]
    exact hxm
  have heq : S.image (fun s => residue A (lift s)) = T :=
    Finset.eq_of_subset_of_card_le himage (by rw [hScard']; exact hTcard)
  rw [← heq, Finset.mem_image] at hxT
  obtain ⟨s, hs, hsx⟩ := hxT
  refine ⟨lift s, hsx, fun σ hσ => ?_⟩
  rw [hlift s hs]
  exact forall_inertia_apply_eq_of_pow_eq_one A hp hA hpm hm0 (hSmem s hs) σ hσ

end ResiduePairLift.Inertia

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} (hp : p.Prime) (hA : A.LiesOverPrime p)
    (x : IsLocalRing.ResidueField ↥A) :
    ∃ a : ↥A, IsLocalRing.residue ↥A a = x ∧
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : AlgebraicClosure ℚ) = a :=
  ResiduePairLift.Inertia.exists_residue_eq_and_forall_inertia_apply_eq A hp hA x

end S_ValuationSubring_exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_residue_eq_and_forall_mem_inertiaSubgroupIn_apply_eq_of_liesOverPrime (solution)
