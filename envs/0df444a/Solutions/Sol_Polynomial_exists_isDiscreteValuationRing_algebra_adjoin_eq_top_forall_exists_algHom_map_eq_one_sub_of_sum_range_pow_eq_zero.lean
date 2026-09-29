-- Prove2me | solution 1 for Polynomial.exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/30f20c67-63e3-59b3-871d-3a2e9153a781

import Mathlib
import Theorems.Thm_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero

set_option autoImplicit false

open IsLocalRing Polynomial

namespace CycloBase
section cyclo

variable (S : Type) [CommRing S]

noncomputable def cycShift (q : ℕ) : S[X] := ((cyclotomic q ℤ).comp (X + 1)).map (Int.castRingHom S)

lemma cycShift_eq (q : ℕ) : cycShift S q = (cyclotomic q S).comp (X + 1) := by
  rw [cycShift, Polynomial.map_comp, map_cyclotomic]
  simp

lemma cycShift_monic (q : ℕ) : (cycShift S q).Monic := by
  rw [cycShift_eq]
  simpa using (cyclotomic.monic q S).comp_X_add_C 1

lemma natDegree_X_add_one' {R : Type} [CommRing R] [Nontrivial R] : (X + 1 : R[X]).natDegree = 1 := by
  rw [← C_1, natDegree_X_add_C]

lemma cycShift_natDegree (q : ℕ) [Fact q.Prime] [Nontrivial S] [NoZeroDivisors S] :
    (cycShift S q).natDegree = q - 1 := by
  rw [cycShift_eq, natDegree_comp, natDegree_cyclotomic, Nat.totient_prime (Fact.out), natDegree_X_add_one',
    mul_one]

lemma cycShift_coeff_zero (q : ℕ) [Fact q.Prime] : (cycShift S q).coeff 0 = (q : S) := by
  rw [cycShift_eq, coeff_zero_eq_eval_zero, eval_comp]
  simp [eval_one_cyclotomic_prime]

lemma cycShift_coeff_mem (q : ℕ) [Fact q.Prime] [Nontrivial S] [NoZeroDivisors S] (n : ℕ) (hn : n < q - 1) :
    (cycShift S q).coeff n ∈ Ideal.span {(q : S)} := by
  have hE := cyclotomic_comp_X_add_one_isEisensteinAt q
  have hdeg : ((cyclotomic q ℤ).comp (X + 1)).natDegree = q - 1 := by
    rw [natDegree_comp, natDegree_cyclotomic, Nat.totient_prime (Fact.out), natDegree_X_add_one', mul_one]
  have hmem := hE.mem (n := n) (by rw [hdeg]; exact hn)
  rw [cycShift, coeff_map]
  rw [Ideal.mem_span_singleton] at hmem ⊢
  obtain ⟨c, hc⟩ := hmem
  refine ⟨(c : S), ?_⟩
  rw [hc]; simp

lemma cycShift_aeval {T : Type} [CommRing T] [Algebra S T] (q : ℕ) [Fact q.Prime] (ζ : T) :
    aeval (ζ - 1) (cycShift S q) = ∑ i ∈ Finset.range q, ζ ^ i := by
  rw [cycShift_eq, aeval_def, eval₂_comp, ← aeval_def, ← aeval_def]
  simp [cyclotomic_prime, aeval_def, eval₂_eq_eval_map]

end cyclo

section Dquot

variable {S : Type} [CommRing S]

theorem nonempty_ringEquiv_adjoinRoot_quotient_span_root (h : S[X]) :
    Nonempty ((AdjoinRoot h ⧸ Ideal.span {AdjoinRoot.root h}) ≃+* (S ⧸ Ideal.span {h.coeff 0})) := by
  classical
  let χ : AdjoinRoot h →+* S ⧸ Ideal.span {h.coeff 0} :=
    AdjoinRoot.lift (Ideal.Quotient.mk _) 0 (by
      rw [eval₂_at_zero, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl)
  have hχsurj : Function.Surjective χ := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨AdjoinRoot.of h s, by simp [χ, AdjoinRoot.lift_of]⟩
  have hof0 : AdjoinRoot.of h (h.coeff 0) ∈ Ideal.span {AdjoinRoot.root h} := by
    have hh : AdjoinRoot.mk h (X * h.divX + C (h.coeff 0)) = 0 := by rw [X_mul_divX_add]; exact AdjoinRoot.mk_self
    rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
    have : AdjoinRoot.of h (h.coeff 0) = -(AdjoinRoot.root h * AdjoinRoot.mk h h.divX) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hh
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hker : RingHom.ker χ = Ideal.span {AdjoinRoot.root h} := by
    apply le_antisymm
    · intro d hd
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective d
      rw [RingHom.mem_ker] at hd
      simp only [χ, AdjoinRoot.lift_mk, eval₂_at_zero, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton] at hd
      obtain ⟨s, hs⟩ := hd
      rw [← X_mul_divX_add p, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, hs, map_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_
      exact Ideal.mul_mem_right _ _ hof0
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp [χ, AdjoinRoot.lift_root]
  rw [← hker]
  exact ⟨RingHom.quotientKerEquivOfSurjective hχsurj⟩

end Dquot

end CycloBase

open CycloBase in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q)
    (Z₀ : Type) [CommRing Z₀] [IsDomain Z₀] [IsDiscreteValuationRing Z₀]
    (hZ₀ : maximalIdeal Z₀ = Ideal.span {(q : Z₀)}) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra Z₀ V)
      (_ : Module.Finite Z₀ V) (_ : Module.Free Z₀ V)
      (_ : Finite (ResidueField Z₀) → Finite (ResidueField V))
      (ϖ : V) (_ : maximalIdeal V = Ideal.span {ϖ}) (_ : Algebra.adjoin Z₀ {ϖ} = ⊤)
      (ε : V) (_ : IsUnit ε) (_ : ϖ ^ (q - 1) = ε * (q : V))
      (_ : ∑ i ∈ Finset.range q, (1 - ϖ) ^ i = 0),
      ∀ (R : Type) [CommRing R] [Algebra Z₀ R] (ζ : R), ∑ i ∈ Finset.range q, ζ ^ i = 0 →
        ∃ ι : V →ₐ[Z₀] R, ι ϖ = 1 - ζ := by
  classical
  have hqp : q.Prime := Fact.out
  haveI : IsRegularLocalRing Z₀ := inferInstance

  have hqmem : (q : Z₀) ∈ maximalIdeal Z₀ := by rw [hZ₀]; exact Ideal.mem_span_singleton_self _
  have hq0 : (q : Z₀) ≠ 0 := by
    intro h0
    have : maximalIdeal Z₀ = ⊥ := by rw [hZ₀, h0, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField Z₀ (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)

  have hhm : (cycShift Z₀ q).Monic := cycShift_monic _ q
  have hhdeg : (cycShift Z₀ q).natDegree = q - 1 := cycShift_natDegree _ q
  have hh0 : (cycShift Z₀ q).coeff 0 = (q : Z₀) := cycShift_coeff_zero _ q
  have hhcoeff : ∀ i < (cycShift Z₀ q).natDegree, (cycShift Z₀ q).coeff i ∈ maximalIdeal Z₀ := by
    intro i hi
    rw [hhdeg] at hi
    rw [hZ₀]; exact cycShift_coeff_mem Z₀ q i hi
  have hh0' : (cycShift Z₀ q).coeff 0 ∉ maximalIdeal Z₀ ^ 2 := by
    rw [hh0, hZ₀, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    apply (IsLocalRing.mem_maximalIdeal _).mp hqmem
    refine isUnit_iff_exists_inv.mpr ⟨c, ?_⟩
    have : (q : Z₀) * 1 = (q : Z₀) * ((q : Z₀) * c) := by rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
    exact (mul_left_cancel₀ hq0 this).symm
  have hq1 : 1 ≤ (cycShift Z₀ q).natDegree := by rw [hhdeg]; omega
  obtain ⟨hreg, hdim⟩ :=
    IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
      Z₀ (cycShift Z₀ q) hhm hq1 hhcoeff hh0'
  haveI := hreg
  haveI hVdom : IsDomain (AdjoinRoot (cycShift Z₀ q)) := IsRegularLocalRing.isDomain _

  obtain ⟨e₁⟩ := nonempty_ringEquiv_adjoinRoot_quotient_span_root (cycShift Z₀ q)
  have hmaxq : (Ideal.span {(q : Z₀)}).IsMaximal := by rw [← hZ₀]; exact maximalIdeal.isMaximal Z₀
  have hfield : IsField (Z₀ ⧸ Ideal.span {(cycShift Z₀ q).coeff 0}) := by
    rw [hh0]; exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmaxq
  have hrootmax : (Ideal.span {AdjoinRoot.root (cycShift Z₀ q)}).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr (e₁.toMulEquiv.isField hfield)
  have hmV : maximalIdeal (AdjoinRoot (cycShift Z₀ q)) = Ideal.span {AdjoinRoot.root (cycShift Z₀ q)} :=
    (IsLocalRing.eq_maximalIdeal hrootmax).symm

  have hroot0 : AdjoinRoot.root (cycShift Z₀ q) ≠ 0 := by
    rw [← AdjoinRoot.mk_X]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt hhm X_ne_zero (by rw [natDegree_X, hhdeg]; omega)
  have hnf : ¬ IsField (AdjoinRoot (cycShift Z₀ q)) := by
    intro hf
    have := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [hmV, Ideal.span_singleton_eq_bot] at this
    exact hroot0 this
  haveI hVdvr : IsDiscreteValuationRing (AdjoinRoot (cycShift Z₀ q)) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot (cycShift Z₀ q)) hnf).out 0 4).mpr
      (⟨⟨AdjoinRoot.root (cycShift Z₀ q), hmV⟩⟩ : (maximalIdeal (AdjoinRoot (cycShift Z₀ q))).IsPrincipal)

  haveI : Module.Finite Z₀ (AdjoinRoot (cycShift Z₀ q)) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hhm).basis
  haveI : Module.Free Z₀ (AdjoinRoot (cycShift Z₀ q)) := Module.Free.of_basis (AdjoinRoot.powerBasis' hhm).basis

  have hres : Finite (ResidueField Z₀) → Finite (ResidueField (AdjoinRoot (cycShift Z₀ q))) := by
    intro hfin
    have e₂ : ResidueField (AdjoinRoot (cycShift Z₀ q)) ≃+* ResidueField Z₀ :=
      (Ideal.quotEquivOfEq hmV).trans (e₁.trans ((Ideal.quotEquivOfEq (by rw [hh0])).trans (Ideal.quotEquivOfEq hZ₀.symm)))
    exact Finite.of_equiv _ e₂.symm.toEquiv

  have hrootmem : AdjoinRoot.root (cycShift Z₀ q) ∈ maximalIdeal (AdjoinRoot (cycShift Z₀ q)) := by
    rw [hmV]; exact Ideal.mem_span_singleton_self _
  have hcoef : ∀ i : ℕ, ∃ dᵢ : Z₀, i < q - 1 → (cycShift Z₀ q).coeff i = (q : Z₀) * dᵢ := by
    intro i
    by_cases hi : i < q - 1
    · obtain ⟨dᵢ, hdᵢ⟩ := Ideal.mem_span_singleton'.mp (cycShift_coeff_mem Z₀ q i hi)
      exact ⟨dᵢ, fun _ => by rw [← hdᵢ, mul_comm]⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose d hd using hcoef
  have haeval : aeval (AdjoinRoot.root (cycShift Z₀ q)) (cycShift Z₀ q) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hsum0 : AdjoinRoot.root (cycShift Z₀ q) ^ (q - 1) + ∑ i ∈ Finset.range (q - 1),
      algebraMap Z₀ (AdjoinRoot (cycShift Z₀ q)) ((cycShift Z₀ q).coeff i) * AdjoinRoot.root (cycShift Z₀ q) ^ i = 0 := by
    have h1 : aeval (AdjoinRoot.root (cycShift Z₀ q)) (X ^ (cycShift Z₀ q).natDegree +
        ∑ i ∈ Finset.range (cycShift Z₀ q).natDegree, C ((cycShift Z₀ q).coeff i) * X ^ i) = 0 := by
      rw [← hhm.as_sum]; exact haeval
    rw [hhdeg, map_add, map_pow, aeval_X, map_sum] at h1
    simpa only [map_mul, aeval_C, map_pow, aeval_X] using h1
  let u : AdjoinRoot (cycShift Z₀ q) :=
    ∑ i ∈ Finset.range (q - 1), algebraMap Z₀ (AdjoinRoot (cycShift Z₀ q)) (d i) * AdjoinRoot.root (cycShift Z₀ q) ^ i
  have hu_eq : ∑ i ∈ Finset.range (q - 1),
      algebraMap Z₀ (AdjoinRoot (cycShift Z₀ q)) ((cycShift Z₀ q).coeff i) * AdjoinRoot.root (cycShift Z₀ q) ^ i =
      (q : AdjoinRoot (cycShift Z₀ q)) * u := by
    simp only [u, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hd i (Finset.mem_range.mp hi), map_mul, map_natCast]; ring
  have hpow : AdjoinRoot.root (cycShift Z₀ q) ^ (q - 1) = -((q : AdjoinRoot (cycShift Z₀ q)) * u) := by
    rw [hu_eq] at hsum0; exact eq_neg_of_add_eq_zero_left hsum0
  have hd0 : d 0 = 1 := by
    have h := hd 0 (by omega)
    rw [hh0] at h
    have : (q : Z₀) * 1 = (q : Z₀) * d 0 := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hq0 this).symm
  have hu_unit : IsUnit u := by

    have hsub : u - 1 ∈ maximalIdeal (AdjoinRoot (cycShift Z₀ q)) := by
      obtain ⟨n, hn⟩ : ∃ n, q - 1 = n + 1 := ⟨q - 2, by omega⟩
      simp only [u, hn, Finset.sum_range_succ', pow_zero, mul_one, hd0, map_one, add_sub_cancel_right]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [pow_succ]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hrootmem)
    by_contra hu
    have hmem : u ∈ maximalIdeal (AdjoinRoot (cycShift Z₀ q)) := (IsLocalRing.mem_maximalIdeal _).mpr hu
    have : (1 : AdjoinRoot (cycShift Z₀ q)) ∈ maximalIdeal (AdjoinRoot (cycShift Z₀ q)) := by
      have := Ideal.sub_mem _ hmem hsub; rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hev : Even (q - 1) := hqp.even_sub_one (by omega)
  refine ⟨AdjoinRoot (cycShift Z₀ q), inferInstance, hVdom, hVdvr, inferInstance, inferInstance, inferInstance, hres,
    -AdjoinRoot.root (cycShift Z₀ q), ?_, ?_, -u, hu_unit.neg, ?_, ?_, ?_⟩
  · rw [hmV, Ideal.span_singleton_neg]
  · apply top_le_iff.mp
    rw [← AdjoinRoot.adjoinRoot_eq_top (f := cycShift Z₀ q)]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    have h := Subalgebra.neg_mem _ (Algebra.self_mem_adjoin_singleton Z₀ (-AdjoinRoot.root (cycShift Z₀ q)))
    rwa [neg_neg] at h
  · rw [hev.neg_pow, hpow]; ring
  · have h2 := cycShift_aeval Z₀ (T := AdjoinRoot (cycShift Z₀ q)) q (1 + AdjoinRoot.root (cycShift Z₀ q))
    rw [show (1 + AdjoinRoot.root (cycShift Z₀ q)) - 1 = AdjoinRoot.root (cycShift Z₀ q) by ring, haeval] at h2
    rw [sub_neg_eq_add]; exact h2.symm
  · intro R _ _ ζ hζ
    have hev₂ : eval₂ (↑(Algebra.ofId Z₀ R)) (ζ - 1) (cycShift Z₀ q) = 0 := by
      have h3 := cycShift_aeval Z₀ (T := R) q ζ
      rw [hζ, aeval_def] at h3
      exact h3
    refine ⟨AdjoinRoot.liftAlgHom (cycShift Z₀ q) (Algebra.ofId Z₀ R) (ζ - 1) hev₂, ?_⟩
    rw [map_neg]
    simp

end S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero
end P2MW
export P2MW.S_Polynomial_exists_isDiscreteValuationRing_algebra_adjoin_eq_top_forall_exists_algHom_map_eq_one_sub_of_sum_range_pow_eq_zero (solution)
