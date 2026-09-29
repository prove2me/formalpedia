-- Prove2me | solution 1 for RibetIrr.module_finite_padicInt_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1b4eab69-3482-5e58-aa51-e92a8ea018e7

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing

set_option autoImplicit false
set_option Elab.async false

namespace SolS2

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [CharZero O] [Algebra ℤ_[p] O]

omit [Algebra ℤ_[p] O] in

theorem finite_quot_span_p : Finite (O ⧸ Ideal.span {(p : O)}) := by
  have hpp : p.Prime := Fact.out
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hms : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hspan : Ideal.span {(p : O)} = (IsLocalRing.maximalIdeal O) ^ n := by
    rw [Ideal.span_singleton_eq_span_singleton.mpr hn, ← Ideal.span_singleton_pow, ← hms]
  haveI h1 : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField O))
  have hfg : (IsLocalRing.maximalIdeal O).FG := ⟨{ϖ}, by simp [hms]⟩
  rw [hspan]
  exact Ideal.finite_quotient_pow hfg n

omit [Fact (Nat.Prime p)] [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O] in

theorem span_p_pow_le (hp : (p : O) ∈ IsLocalRing.maximalIdeal O) (k : ℕ) :
    (Ideal.span {(p : O)}) ^ k ≤ (IsLocalRing.maximalIdeal O) ^ k := by
  refine Ideal.pow_right_mono ?_ k
  rwa [Ideal.span_singleton_le_iff_mem]

noncomputable def sec (q : O ⧸ Ideal.span {(p : O)}) : O :=
  (Ideal.Quotient.mk_surjective q).choose

omit [Fact (Nat.Prime p)] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O] in
theorem sec_spec (q : O ⧸ Ideal.span {(p : O)}) :
    Ideal.Quotient.mk (Ideal.span {(p : O)}) (sec p O q) = q :=
  (Ideal.Quotient.mk_surjective q).choose_spec

omit [Fact (Nat.Prime p)] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O] in

theorem exists_step (m : O) :
    ∃ q r, m = sec p O q + (p : O) * r := by
  refine ⟨Ideal.Quotient.mk _ m, ?_⟩
  have hmem : m - sec p O (Ideal.Quotient.mk (Ideal.span {(p : O)}) m) ∈
      Ideal.span {(p : O)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sec_spec, sub_self]
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  rw [mul_comm] at hr
  rw [hr]
  ring

noncomputable def stepQ (m : O) : O ⧸ Ideal.span {(p : O)} :=
  (exists_step p O m).choose

noncomputable def stepR (m : O) : O :=
  (exists_step p O m).choose_spec.choose

omit [Fact (Nat.Prime p)] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [CharZero O] [Algebra ℤ_[p] O] in
theorem step_spec (m : O) :
    m = sec p O (stepQ p O m) + (p : O) * stepR p O m :=
  (exists_step p O m).choose_spec.choose_spec

noncomputable def Rm (x : O) : ℕ → O
  | 0 => x
  | k + 1 => stepR p O (Rm x k)

noncomputable def coeff [DecidableEq (O ⧸ Ideal.span {(p : O)})] (x : O) (k : ℕ)
    (q : O ⧸ Ideal.span {(p : O)}) : ℤ_[p] :=
  ∑ i ∈ Finset.range k, if stepQ p O (Rm p O x i) = q then (p : ℤ_[p]) ^ i else 0

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [CharZero O] in
theorem smul_eq_cast_mul (k : ℕ) (y : O) : ((p : ℤ_[p]) ^ k) • y = (p : O) ^ k * y := by
  rw [Algebra.smul_def, map_pow, map_natCast]

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [CharZero O] in

theorem invariant [DecidableEq (O ⧸ Ideal.span {(p : O)})]
    [Fintype (O ⧸ Ideal.span {(p : O)})] (x : O) (k : ℕ) :
    x = (∑ q, coeff p O x k q • sec p O q) + (p : O) ^ k * Rm p O x k := by
  induction k with
  | zero => simp [coeff, Rm]
  | succ k ih =>
    have hco : ∀ q, coeff p O x (k + 1) q
        = coeff p O x k q + (if stepQ p O (Rm p O x k) = q then (p : ℤ_[p]) ^ k else 0) := by
      intro q
      unfold coeff
      exact Finset.sum_range_succ _ _
    have hsum : (∑ q, coeff p O x (k + 1) q • sec p O q)
        = (∑ q, coeff p O x k q • sec p O q)
          + ((p : ℤ_[p]) ^ k) • sec p O (stepQ p O (Rm p O x k)) := by
      simp only [hco, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul]
      congr 1
      simp [Finset.sum_ite_eq]
    rw [hsum, smul_eq_cast_mul]
    have hstep := step_spec p O (Rm p O x k)
    calc x = (∑ q, coeff p O x k q • sec p O q) + (p : O) ^ k * Rm p O x k := ih
      _ = (∑ q, coeff p O x k q • sec p O q)
            + (p : O) ^ k *
              (sec p O (stepQ p O (Rm p O x k)) + (p : O) * stepR p O (Rm p O x k)) := by
          rw [← hstep]
      _ = ((∑ q, coeff p O x k q • sec p O q)
            + (p : O) ^ k * sec p O (stepQ p O (Rm p O x k)))
            + (p : O) ^ (k + 1) * Rm p O x (k + 1) := by
          show _ = _ + (p : O) ^ (k + 1) * stepR p O (Rm p O x k)
          ring

omit [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
  [CharZero O] [Algebra ℤ_[p] O] in

theorem coeff_sub_mem [DecidableEq (O ⧸ Ideal.span {(p : O)})] (x : O)
    (q : O ⧸ Ideal.span {(p : O)}) {m n : ℕ} (h : m ≤ n) :
    coeff p O x n q - coeff p O x m q ∈ (Ideal.span {(p : ℤ_[p])}) ^ m := by
  unfold coeff
  rw [← Finset.sum_Ico_eq_sub _ h, Ideal.span_singleton_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Finset.mem_Ico] at hi
  split
  · exact Ideal.mem_span_singleton.mpr (pow_dvd_pow _ hi.1)
  · exact Ideal.zero_mem _

omit [Finite (IsLocalRing.ResidueField O)] [CharZero O] in

theorem span_sec_eq_top (hp : (p : O) ∈ IsLocalRing.maximalIdeal O)
    [Fintype (O ⧸ Ideal.span {(p : O)})] :
    Submodule.span ℤ_[p] (Set.range (sec p O)) = ⊤ := by
  classical
  refine eq_top_iff.mpr fun x _ => ?_

  have hcau : ∀ q : O ⧸ Ideal.span {(p : O)}, ∃ L : ℤ_[p],
      ∀ n : ℕ, coeff p O x n q ≡ L [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ n •
        (⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro q
    refine IsPrecomplete.prec inferInstance fun {m n} h => ?_
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, PadicInt.maximalIdeal_eq_span_p]
    have hmem := coeff_sub_mem p O x q h
    have hneg : coeff p O x m q - coeff p O x n q
        = -(coeff p O x n q - coeff p O x m q) := by ring
    rw [hneg]
    exact neg_mem hmem
  choose L hL using hcau

  have herr : ∀ k : ℕ, x - ∑ q, L q • sec p O q ∈ (Ideal.span {(p : O)}) ^ k := by
    intro k
    have hinv := invariant p O x k
    have hdiff : ∀ q : O ⧸ Ideal.span {(p : O)},
        (coeff p O x k q - L q) • sec p O q ∈ (Ideal.span {(p : O)}) ^ k := by
      intro q
      have hmem : coeff p O x k q - L q ∈ (Ideal.span {(p : ℤ_[p])}) ^ k := by
        have h0 := (SModEq.sub_mem).mp (hL q k)
        rwa [Ideal.smul_eq_mul, Ideal.mul_top, PadicInt.maximalIdeal_eq_span_p] at h0
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
      obtain ⟨a, ha⟩ := hmem
      rw [← ha, mul_comm, mul_smul, smul_eq_cast_mul, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.mpr ⟨a • sec p O q, rfl⟩
    have hsum : ∑ q, (coeff p O x k q - L q) • sec p O q ∈ (Ideal.span {(p : O)}) ^ k :=
      Ideal.sum_mem _ fun q _ => hdiff q
    have hrm : (p : O) ^ k * Rm p O x k ∈ (Ideal.span {(p : O)}) ^ k := by
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.mpr ⟨Rm p O x k, rfl⟩
    have hsplit : x - ∑ q, L q • sec p O q
        = ((p : O) ^ k * Rm p O x k) + ∑ q, (coeff p O x k q - L q) • sec p O q := by
      conv_lhs => rw [hinv]
      simp only [sub_smul, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    exact add_mem hrm hsum

  have hzero : x - ∑ q, L q • sec p O q = 0 := by
    have hH : IsHausdorff (IsLocalRing.maximalIdeal O) O :=
      IsHausdorff.of_isDomain _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    refine hH.haus _ fun k => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact span_p_pow_le p O hp k (herr k)
  have hfin : x = ∑ q, L q • sec p O q := by rwa [sub_eq_zero] at hzero
  rw [hfin]
  exact Submodule.sum_mem _ fun q _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)

end SolS2

theorem solution
    (p : ℕ) [Fact p.Prime] (𝒪'' : Type) [CommRing 𝒪''] [IsDomain 𝒪'']
    [IsDiscreteValuationRing 𝒪''] [Finite (IsLocalRing.ResidueField 𝒪'')]
    [CharZero 𝒪''] (hp𝒪'' : (p : 𝒪'') ∈ IsLocalRing.maximalIdeal 𝒪'')
    [Algebra ℤ_[p] 𝒪''] : Module.Finite ℤ_[p] 𝒪'' := by
  classical
  haveI := SolS2.finite_quot_span_p p 𝒪''
  haveI := Fintype.ofFinite (𝒪'' ⧸ Ideal.span {(p : 𝒪'')})
  refine Module.finite_def.mpr ⟨(Set.finite_range (SolS2.sec p 𝒪'')).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact SolS2.span_sec_eq_top p 𝒪'' hp𝒪''

end S_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing
end P2MW
export P2MW.S_RibetIrr_module_finite_padicInt_of_isDiscreteValuationRing (solution)
