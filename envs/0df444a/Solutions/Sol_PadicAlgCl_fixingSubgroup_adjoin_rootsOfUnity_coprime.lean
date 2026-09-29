-- Prove2me | solution 1 for PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6c57adc2-d403-54d5-a479-324c14336a64

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Pointwise NNReal

open IntermediateField

namespace WELV2p

variable (p : ℕ) [Fact p.Prime]

theorem nnnorm_sub_le_max' (x y : PadicAlgCl p) : ‖x - y‖₊ ≤ max ‖x‖₊ ‖y‖₊ := by
  rw [sub_eq_add_neg, ← nnnorm_neg y]
  exact IsUltrametricDist.nnnorm_add_le_max x (-y)

theorem nnnorm_eq_one_of_pow_eq_one' {ξ : PadicAlgCl p} {N : ℕ} (hξ : ξ ^ N = 1) (hN0 : N ≠ 0) :
    ‖ξ‖₊ = 1 := by
  have h : ‖ξ‖ ^ N = 1 := by rw [← norm_pow, hξ, norm_one]
  have := (pow_eq_one_iff_of_nonneg (norm_nonneg ξ) hN0).mp h
  rwa [← coe_nnnorm, NNReal.coe_eq_one] at this

theorem nnnorm_natCast_eq_one {N : ℕ} (hN : ¬ p ∣ N) : ‖(N : PadicAlgCl p)‖₊ = 1 := by
  have hp : p.Prime := Fact.out
  rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_one, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) N,
    show algebraMap ℚ_[p] (PadicAlgCl p) (N : ℚ_[p]) = ((N : ℚ_[p]) : PadicAlgCl p) from rfl,
    PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hN

theorem eq_one_of_pow_eq_one_of_nnnorm_sub_one_lt {N : ℕ} (hN : ¬ p ∣ N) {ξ : PadicAlgCl p}
    (hξ : ξ ^ N = 1) (h1 : ‖ξ - 1‖₊ < 1) : ξ = 1 := by
  classical
  by_contra hne
  have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero p)

  have hsmall : ∀ i : ℕ, ‖ξ ^ i - 1‖₊ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hξ1 : ‖ξ‖₊ ≤ 1 := le_of_eq (nnnorm_eq_one_of_pow_eq_one' p hξ hN0)
      have : ξ ^ (i + 1) - 1 = ξ * (ξ ^ i - 1) + (ξ - 1) := by ring
      rw [this]
      refine lt_of_le_of_lt (IsUltrametricDist.nnnorm_add_le_max _ _) (max_lt ?_ h1)
      rw [nnnorm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (by simp) hξ1) ih

  have hgeom : (∑ i ∈ Finset.range N, ξ ^ i) = 0 := by
    have h := geom_sum_mul ξ N
    rw [hξ, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)

  have hsum : (∑ i ∈ Finset.range N, ξ ^ i) = (N : PadicAlgCl p) + ∑ i ∈ Finset.range N, (ξ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  have hsmallsum : ‖∑ i ∈ Finset.range N, (ξ ^ i - 1)‖₊ < 1 := by
    obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.range N) (fun i => ξ ^ i - 1)
    exact lt_of_le_of_lt (show ‖∑ i ∈ Finset.range N, (ξ ^ i - 1)‖₊ ≤ ‖ξ ^ i - 1‖₊ from hi) (hsmall i)
  have hnormN : ‖(N : PadicAlgCl p)‖₊ = 1 := nnnorm_natCast_eq_one p hN
  have hne' : ‖(N : PadicAlgCl p)‖₊ ≠ ‖∑ i ∈ Finset.range N, (ξ ^ i - 1)‖₊ := by
    rw [hnormN]; exact (ne_of_lt hsmallsum).symm
  have key : ‖(N : PadicAlgCl p) + ∑ i ∈ Finset.range N, (ξ ^ i - 1)‖₊ = 1 := by
    rw [IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hne', hnormN, max_eq_left (le_of_lt hsmallsum)]
  rw [← hsum, hgeom, nnnorm_zero] at key
  exact zero_ne_one key

theorem mem_decompositionSubgroup (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    σ ∈ (padicIntegers p).decompositionSubgroup ℚ_[p] := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    mem_padicIntegers_iff, mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

theorem mem_inertiaSubgroupIn_iff (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔
      ∀ a : padicIntegers p, ‖σ (a : PadicAlgCl p) - a‖₊ < 1 := by
  constructor
  · rintro ⟨d, hd, rfl⟩ a
    rw [SetLike.mem_coe, ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hd
    have h1 : d • IsLocalRing.residue (padicIntegers p) a = IsLocalRing.residue (padicIntegers p) a :=
      RingEquiv.congr_fun hd (IsLocalRing.residue (padicIntegers p) a)
    rw [← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue] at h1
    have h2 : d • a - a ∈ IsLocalRing.maximalIdeal (padicIntegers p) := Ideal.Quotient.eq.mp h1
    rw [ValuationSubring.valuation_lt_one_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring
        (Valued.v : Valuation (PadicAlgCl p) NNReal)).lt_one_iff_lt_one] at h2
    exact h2
  · intro h
    refine ⟨⟨σ, mem_decompositionSubgroup p σ⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    show (⟨σ, mem_decompositionSubgroup p σ⟩ : (padicIntegers p).decompositionSubgroup ℚ_[p]) •
        IsLocalRing.residue (padicIntegers p) a = IsLocalRing.residue (padicIntegers p) a
    rw [← IsLocalRing.ResidueField.residue_smul, IsLocalRing.residue]
    refine Ideal.Quotient.eq.mpr ?_
    rw [ValuationSubring.valuation_lt_one_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring
        (Valued.v : Valuation (PadicAlgCl p) NNReal)).lt_one_iff_lt_one]
    exact h a

theorem mem_maximalIdeal_iff_nnnorm_lt (x : padicIntegers p) :
    x ∈ IsLocalRing.maximalIdeal (padicIntegers p) ↔ ‖(x : PadicAlgCl p)‖₊ < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring
      (Valued.v : Valuation (PadicAlgCl p) NNReal)).lt_one_iff_lt_one]
  rfl

theorem residue_eq_residue_iff (x y : padicIntegers p) :
    IsLocalRing.residue (padicIntegers p) x = IsLocalRing.residue (padicIntegers p) y ↔
      ‖(x : PadicAlgCl p) - y‖₊ < 1 := by
  constructor
  · intro h
    have h' : x - y ∈ IsLocalRing.maximalIdeal (padicIntegers p) := Ideal.Quotient.eq.mp h
    rw [mem_maximalIdeal_iff_nnnorm_lt] at h'
    exact h'
  · intro h
    have h' : x - y ∈ IsLocalRing.maximalIdeal (padicIntegers p) := by
      rw [mem_maximalIdeal_iff_nnnorm_lt]; exact h
    exact Ideal.Quotient.eq.mpr h'

theorem charP_residueField : CharP (IsLocalRing.ResidueField (padicIntegers p)) p := by
  have hp : p.Prime := Fact.out
  refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
  have hpmem : ((p : ℕ) : PadicAlgCl p) ∈ padicIntegers p := by
    rw [mem_padicIntegers_iff, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p,
      show algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) = ((p : ℚ_[p]) : PadicAlgCl p) from rfl,
      ← NNReal.coe_le_coe, coe_nnnorm, PadicAlgCl.norm_extends]
    exact le_of_lt Padic.norm_p_lt_one
  have h1 : (p : IsLocalRing.ResidueField (padicIntegers p)) =
      IsLocalRing.residue (padicIntegers p) ⟨(p : PadicAlgCl p), hpmem⟩ := by
    rw [← map_natCast (IsLocalRing.residue (padicIntegers p)) p]
    congr 1
  rw [h1, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_nnnorm_lt]
  show ‖((p : ℕ) : PadicAlgCl p)‖₊ < 1
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p,
    show algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) = ((p : ℚ_[p]) : PadicAlgCl p) from rfl,
    ← NNReal.coe_lt_coe, coe_nnnorm, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem exists_nnnorm_pow_sub_one_lt (a : PadicAlgCl p) (ha : ‖a‖₊ = 1) :
    ∃ M : ℕ, ¬ p ∣ M ∧ ‖a ^ M - 1‖₊ < 1 := by
  classical
  have hp : p.Prime := Fact.out
  have hai : ∀ i : ℕ, ‖a ^ i‖₊ = 1 := fun i => by rw [nnnorm_pow, ha, one_pow]

  obtain ⟨M₀, hM₀, hclose₀⟩ : ∃ M₀ : ℕ, M₀ ≠ 0 ∧ ‖a ^ M₀ - 1‖₊ < 1 := by
    have hint : IsIntegral ℚ_[p] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
    let W : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {a})
    haveI : FiniteDimensional ℚ_[p] W := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
    haveI : ProperSpace W := FiniteDimensional.proper ℚ_[p] W
    have hmem : ∀ i : ℕ, a ^ i ∈ W := fun i =>
      Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] a) i
    let f : ℕ → W := fun i => ⟨a ^ i, hmem i⟩
    have hball : ∀ i, f i ∈ Metric.closedBall (0 : W) 1 := fun i => by
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖a ^ i‖ ≤ 1
      rw [← coe_nnnorm, hai]; simp
    obtain ⟨t, -, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded
      (isCompact_closedBall (0 : W) 1).totallyBounded 1 one_pos
    have hc : ∀ i, ∃ c ∈ t, f i ∈ Metric.ball c 1 := fun i => by
      simpa only [Set.mem_iUnion, exists_prop] using hcover (hball i)
    choose c hct hcb using hc
    haveI : Finite t := htfin.to_subtype
    obtain ⟨i, j, hij, hcij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨c n, hct n⟩ : t))
    have hcij' : c i = c j := congrArg Subtype.val hcij

    have hd : ∀ n, ‖a ^ n - (c n : PadicAlgCl p)‖₊ < 1 := fun n => by
      have := hcb n
      rw [Metric.mem_ball, dist_eq_norm] at this
      rw [← NNReal.coe_lt_coe, coe_nnnorm]
      exact this
    have hij' : ‖a ^ i - a ^ j‖₊ < 1 := by
      have : a ^ i - a ^ j = (a ^ i - (c i : PadicAlgCl p)) - (a ^ j - (c j : PadicAlgCl p)) := by
        rw [hcij']; ring
      rw [this]
      exact lt_of_le_of_lt (nnnorm_sub_le_max' p _ _) (max_lt (hd i) (hd j))

    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, Nat.sub_ne_zero_of_lt h, ?_⟩
      have heq : a ^ j - a ^ i = a ^ i * (a ^ (j - i) - 1) := by
        rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]
      have : ‖a ^ (j - i) - 1‖₊ = ‖a ^ i - a ^ j‖₊ := by
        rw [← nnnorm_neg (a ^ i - a ^ j), neg_sub, heq, nnnorm_mul, hai, one_mul]
      rw [this]; exact hij'
    · refine ⟨i - j, Nat.sub_ne_zero_of_lt h, ?_⟩
      have heq : a ^ i - a ^ j = a ^ j * (a ^ (i - j) - 1) := by
        rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]
      have : ‖a ^ (i - j) - 1‖₊ = ‖a ^ i - a ^ j‖₊ := by
        rw [heq, nnnorm_mul, hai, one_mul]
      rw [this]; exact hij'

  obtain ⟨k, M, hM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₀ p hp.ne_one
  refine ⟨M, hM, ?_⟩
  haveI := charP_residueField p
  let b : padicIntegers p := ⟨a ^ M, (mem_padicIntegers_iff p).mpr (hai M).le⟩
  have hb : IsLocalRing.residue (padicIntegers p) (b ^ p ^ k) = 1 := by
    rw [← (IsLocalRing.residue (padicIntegers p)).map_one, residue_eq_residue_iff]
    show ‖(a ^ M) ^ p ^ k - 1‖₊ < 1
    rw [← pow_mul, mul_comm]
    exact hclose₀
  have hb1 : IsLocalRing.residue (padicIntegers p) b = 1 := by
    have h := hb
    rw [map_pow] at h
    have : (IsLocalRing.residue (padicIntegers p) b - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, h, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k hp.ne_zero) |>.mp this)
  rw [← (IsLocalRing.residue (padicIntegers p)).map_one, residue_eq_residue_iff] at hb1
  exact hb1

theorem exists_rootOfUnity_coprime_nnnorm_sub_lt (a : PadicAlgCl p) (ha : ‖a‖₊ = 1) :
    ∃ η : PadicAlgCl p, (∃ N : ℕ, ¬ p ∣ N ∧ η ^ N = 1) ∧ ‖a - η‖₊ < 1 := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨M, hM, hclose⟩ := exists_nnnorm_pow_sub_one_lt p a ha
  have hM0 : M ≠ 0 := by rintro rfl; exact hM (dvd_zero p)
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0

  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ M := by
    have hdeg : (Polynomial.cyclotomic M (PadicAlgCl p)).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr hMpos).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff_charZero hMpos).mp hζ⟩
  let S : Finset (PadicAlgCl p) := Polynomial.nthRootsFinset M (1 : PadicAlgCl p)
  have hScard : S.card = M := hζ.card_nthRootsFinset
  have hSmem : ∀ η ∈ S, η ^ M = 1 := fun η hη => (Polynomial.mem_nthRootsFinset hMpos 1).mp hη
  have hSnorm : ∀ η ∈ S, ‖η‖₊ = 1 := fun η hη => nnnorm_eq_one_of_pow_eq_one' p (hSmem η hη) hM0

  let k := IsLocalRing.ResidueField (padicIntegers p)
  let T : Finset k := (Polynomial.nthRoots M (1 : k)).toFinset
  have hTcard : T.card ≤ M := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots M 1)
  let g : ∀ η ∈ S, k := fun η hη =>
    IsLocalRing.residue (padicIntegers p) ⟨η, (mem_padicIntegers_iff p).mpr (hSnorm η hη).le⟩
  have hg : ∀ η hη, g η hη ∈ T := by
    intro η hη
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hMpos]
    show IsLocalRing.residue (padicIntegers p) _ ^ M = 1
    rw [← map_pow, ← (IsLocalRing.residue (padicIntegers p)).map_one, residue_eq_residue_iff]
    show ‖η ^ M - 1‖₊ < 1
    rw [hSmem η hη, sub_self, nnnorm_zero]; exact one_pos
  have hginj : ∀ η₁ η₂ h₁ h₂, g η₁ h₁ = g η₂ h₂ → η₁ = η₂ := by
    intro η₁ η₂ h₁ h₂ h
    rw [residue_eq_residue_iff] at h
    change ‖η₁ - η₂‖₊ < 1 at h
    have hη₂0 : η₂ ≠ 0 := by rintro rfl; have := hSnorm 0 h₂; simp at this
    have hq : (η₁ * η₂⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hSmem η₁ h₁, hSmem η₂ h₂, inv_one, mul_one]
    have hq1 : ‖η₁ * η₂⁻¹ - 1‖₊ < 1 := by
      have : η₁ * η₂⁻¹ - 1 = (η₁ - η₂) * η₂⁻¹ := by field_simp
      rw [this, nnnorm_mul, nnnorm_inv, hSnorm η₂ h₂, inv_one, mul_one]; exact h
    have := eq_one_of_pow_eq_one_of_nnnorm_sub_one_lt p hM hq hq1
    calc η₁ = η₁ * η₂⁻¹ * η₂ := by rw [inv_mul_cancel_right₀ hη₂0]
      _ = η₂ := by rw [this, one_mul]

  have hsurj := Finset.surj_on_of_inj_on_of_card_le g hg hginj (hTcard.trans hScard.ge)
  have haT : IsLocalRing.residue (padicIntegers p) ⟨a, (mem_padicIntegers_iff p).mpr ha.le⟩ ∈ T := by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hMpos, ← map_pow,
      ← (IsLocalRing.residue (padicIntegers p)).map_one, residue_eq_residue_iff]
    exact hclose
  obtain ⟨η, hηS, hηeq⟩ := hsurj _ haT
  refine ⟨η, ⟨M, hM, hSmem η hηS⟩, ?_⟩
  have := (residue_eq_residue_iff p _ _).mp hηeq
  exact this

end WELV2p

theorem solution (p : ℕ) [Fact p.Prime] :
    (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}).fixingSubgroup
      = (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
  classical
  have hp : p.Prime := Fact.out
  apply le_antisymm
  ·
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    rw [WELV2p.mem_inertiaSubgroupIn_iff]
    intro a
    rcases lt_or_eq_of_le ((mem_padicIntegers_iff p).mp a.2) with hlt | heq
    ·
      refine lt_of_le_of_lt (WELV2p.nnnorm_sub_le_max' p (σ (a : PadicAlgCl p)) (a : PadicAlgCl p)) (max_lt ?_ hlt)
      rw [nnnorm_padicAlgCl_algEquiv]; exact hlt
    · obtain ⟨η, hηS, haη⟩ := WELV2p.exists_rootOfUnity_coprime_nnnorm_sub_lt p (a : PadicAlgCl p) heq
      have hση : σ η = η := hσ η (IntermediateField.subset_adjoin ℚ_[p] _ hηS)
      have : σ (a : PadicAlgCl p) - a = σ ((a : PadicAlgCl p) - η) - ((a : PadicAlgCl p) - η) := by
        rw [map_sub, hση]; ring
      rw [this]
      refine lt_of_le_of_lt (WELV2p.nnnorm_sub_le_max' p (σ ((a : PadicAlgCl p) - η)) ((a : PadicAlgCl p) - η)) (max_lt ?_ haη)
      rw [nnnorm_padicAlgCl_algEquiv]; exact haη
  ·
    intro σ hσ
    rw [WELV2p.mem_inertiaSubgroupIn_iff] at hσ
    have hgen : ∀ s ∈ {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}, σ s = s := by
      rintro s ⟨N, hN, hsN⟩
      have hN0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero p)
      have hs1 : ‖s‖₊ = 1 := WELV2p.nnnorm_eq_one_of_pow_eq_one' p hsN hN0
      have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
      have hclose : ‖σ s - s‖₊ < 1 := hσ ⟨s, (mem_padicIntegers_iff p).mpr hs1.le⟩

      have hξN : (σ s * s⁻¹) ^ N = 1 := by
        rw [mul_pow, ← map_pow, hsN, map_one, one_mul, inv_pow, hsN, inv_one]
      have hξ1 : ‖σ s * s⁻¹ - 1‖₊ < 1 := by
        have : σ s * s⁻¹ - 1 = (σ s - s) * s⁻¹ := by field_simp
        rw [this, nnnorm_mul, nnnorm_inv, hs1, inv_one, mul_one]
        exact hclose
      have := WELV2p.eq_one_of_pow_eq_one_of_nnnorm_sub_one_lt p hN hξN hξ1
      calc σ s = σ s * s⁻¹ * s := by rw [inv_mul_cancel_right₀ hs0]
        _ = s := by rw [this, one_mul]

    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hle : IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1} ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_le_iff]
      intro s hs
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro g hg
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) s :=
        Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff]; exact hgen s hs)
      exact hstab hg
    exact (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) σ (Subgroup.mem_zpowers σ)

end S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime
end P2MW
export P2MW.S_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime (solution)
