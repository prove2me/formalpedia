-- Prove2me | solution 1 for ValuationSubring.exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/c6d9234b-8414-50e5-980d-780e158e38c4

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Theorems.Thm_ValuationSubring_valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

open ValuationSubring

noncomputable section

namespace WittUnramSol

variable (p : ℕ) [hp : Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

abbrev CA : Type := A.valuation.Completion

abbrev OA : ValuationSubring (CA A) := (Valued.v : Valuation (CA A) A.ValueGroup).valuationSubring

theorem mem_OA_iff (x : CA A) : x ∈ OA A ↔ Valued.v x ≤ 1 := Valuation.mem_valuationSubring_iff _ _

theorem v_coe_le_one (x : ↥(OA A)) : Valued.v (x : CA A) ≤ 1 := (mem_OA_iff A x).mp x.2

theorem isUnit_iff_v_eq_one (x : ↥(OA A)) : IsUnit x ↔ Valued.v (x : CA A) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 := v_coe_le_one A (u : ↥(OA A))
    have h2 := v_coe_le_one A (↑u⁻¹ : ↥(OA A))
    have h3 : Valued.v ((u : ↥(OA A)) : CA A) * Valued.v ((↑u⁻¹ : ↥(OA A)) : CA A) = 1 := by
      rw [← map_mul, ← Subring.coe_mul]
      change Valued.v (((u * u⁻¹ : (↥(OA A))ˣ) : ↥(OA A)) : CA A) = 1
      rw [mul_inv_cancel]; simp
    apply le_antisymm h1
    by_contra hlt
    push Not at hlt
    have : Valued.v ((u : ↥(OA A)) : CA A) * Valued.v ((↑u⁻¹ : ↥(OA A)) : CA A) < 1 * 1 :=
      mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hlt h2 zero_le' zero_lt_one
    rw [h3, mul_one] at this
    exact lt_irrefl _ this
  · intro h
    have hx0 : (x : CA A) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hinv : (x : CA A)⁻¹ ∈ OA A := by
      rw [mem_OA_iff, map_inv₀, h, inv_one]
    refine ⟨⟨x, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (x : CA A) * (x : CA A)⁻¹ = 1
      exact mul_inv_cancel₀ hx0
    · apply Subtype.ext
      change (x : CA A)⁻¹ * (x : CA A) = 1
      exact inv_mul_cancel₀ hx0

theorem mem_maximalIdeal_iff (x : ↥(OA A)) :
    x ∈ IsLocalRing.maximalIdeal ↥(OA A) ↔ Valued.v (x : CA A) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_v_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (v_coe_le_one A x) h, fun h => h.ne⟩

theorem coe_natCast_completion (n : ℕ) :
    ((n : AlgebraicClosure ℚ) : CA A) = (n : CA A) := by
  show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
      ((WithVal.equiv A.valuation).symm (n : AlgebraicClosure ℚ)) = _
  rw [map_natCast, map_natCast]

theorem v_coe_algClosure (a : AlgebraicClosure ℚ) :
    Valued.v ((a : AlgebraicClosure ℚ) : CA A) = A.valuation a := by
  rw [Valued.valuedCompletion_apply]
  rfl

omit hp in
theorem coe_p : (((p : ℕ) : ↥(OA A)) : CA A) = (p : ℕ) := by simp

theorem isClosed_closedBall_sub (c : CA A) (r : CA A) :
    IsClosed {x : CA A | Valued.v (x - c) ≤ Valued.v r} := by
  have h := (Valued.isClosed_closedBall (CA A) (Valued.v.restrict r)).preimage (continuous_sub_right c)
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Valuation.restrict_le_iff]

section OverP

variable (hA : A.LiesOverPrime p)
include hA

theorem v_p_pos : 0 < Valued.v ((p : ℕ) : CA A) := by
  obtain ⟨h, -, -⟩ :=
    ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime p A hA
  exact h

theorem v_p_lt_one : Valued.v ((p : ℕ) : CA A) < 1 := by
  obtain ⟨-, h, -⟩ :=
    ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime p A hA
  exact h

theorem rankOne (x y : CA A) (hx : Valued.v x < 1) (hy : y ≠ 0) : ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y := by
  obtain ⟨-, -, h⟩ :=
    ValuationSubring.valuation_completion_ratClosure_natCast_pos_and_lt_one_and_rankOne_of_liesOverPrime p A hA
  exact h x y hx hy

theorem p_ne_zero : ((p : ℕ) : CA A) ≠ 0 := by
  intro h
  have := v_p_pos p A hA
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem not_isUnit_p : ¬ IsUnit ((p : ℕ) : ↥(OA A)) := by
  rw [isUnit_iff_v_eq_one, coe_p]
  exact (v_p_lt_one p A hA).ne

theorem p_mem_maximalIdeal : ((p : ℕ) : ↥(OA A)) ∈ IsLocalRing.maximalIdeal ↥(OA A) := by
  rw [mem_maximalIdeal_iff, coe_p]; exact v_p_lt_one p A hA

theorem exists_eq_pow_mul (x : CA A) (n : ℕ) (hx : Valued.v x ≤ Valued.v ((p : ℕ) : CA A) ^ n) :
    ∃ z : ↥(OA A), x = ((p : ℕ) : CA A) ^ n * (z : CA A) := by
  have hpn : ((p : ℕ) : CA A) ^ n ≠ 0 := pow_ne_zero _ (p_ne_zero p A hA)
  refine ⟨⟨x / ((p : ℕ) : CA A) ^ n, ?_⟩, ?_⟩
  · rw [mem_OA_iff, map_div₀, map_pow, div_le_one₀]
    · exact hx
    · rw [← map_pow]; exact (Valuation.pos_iff _).mpr hpn
  · simp only
    rw [mul_div_cancel₀ _ hpn]

theorem mem_span_pow_iff (x : ↥(OA A)) (n : ℕ) :
    x ∈ Ideal.span {((p : ℕ) : ↥(OA A)) ^ n} ↔ Valued.v (x : CA A) ≤ Valued.v ((p : ℕ) : CA A) ^ n := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h
    rw [← ha, Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, coe_p, map_pow]
    calc Valued.v (a : CA A) * Valued.v ((p : ℕ) : CA A) ^ n ≤ 1 * Valued.v ((p : ℕ) : CA A) ^ n := by
          gcongr; exact v_coe_le_one A a
      _ = _ := one_mul _
  · intro h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul p A hA x n h
    refine Ideal.mem_span_singleton'.mpr ⟨z, ?_⟩
    apply Subtype.ext
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_p, hz, mul_comm]

theorem exists_pow_mem_span_p (x : ↥(OA A)) (hx : x ∈ IsLocalRing.maximalIdeal ↥(OA A)) :
    ∃ n : ℕ, x ^ n ∈ Ideal.span {((p : ℕ) : ↥(OA A))} := by
  rw [mem_maximalIdeal_iff] at hx
  obtain ⟨n, hn⟩ := rankOne p A hA (x : CA A) _ hx (p_ne_zero p A hA)
  refine ⟨n, ?_⟩
  rw [← pow_one ((p : ℕ) : ↥(OA A)), mem_span_pow_iff p A hA, pow_one, SubmonoidClass.coe_pow, map_pow]
  exact hn

theorem isHausdorff : IsHausdorff (Ideal.span {((p : ℕ) : ↥(OA A))}) ↥(OA A) := by
  refine ⟨fun x hx => ?_⟩
  have hb : ∀ n : ℕ, Valued.v (x : CA A) ≤ Valued.v ((p : ℕ) : CA A) ^ n := by
    intro n
    have := hx n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at this
    exact (mem_span_pow_iff p A hA x n).mp this
  by_contra hne
  have hne' : (x : CA A) ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨m, hm⟩ := rankOne p A hA _ _ (v_p_lt_one p A hA) hne'
  have h1 := hb (m + 1)
  have h2 : Valued.v ((p : ℕ) : CA A) ^ (m + 1) < Valued.v ((p : ℕ) : CA A) ^ m :=
    pow_lt_pow_right_of_lt_one₀ (v_p_pos p A hA) (v_p_lt_one p A hA) (Nat.lt_succ_self m)
  exact lt_irrefl _ (lt_of_le_of_lt (hm.trans h1) h2)

theorem cauchySeq_of_le (f : ℕ → CA A)
    (hf : ∀ m n : ℕ, m ≤ n → Valued.v (f n - f m) ≤ Valued.v ((p : ℕ) : CA A) ^ m) : CauchySeq f := by
  rw [(Valued.hasBasis_uniformity (CA A) A.ValueGroup).cauchySeq_iff]
  intro γ _
  obtain ⟨r, s, hr, hs, hrs⟩ := Valuation.exists_div_eq_of_unit (Valued.v : Valuation (CA A) A.ValueGroup) γ
  have hr0 : r ≠ 0 := fun h => by rw [h, map_zero] at hr; exact lt_irrefl _ hr
  have hs0 : s ≠ 0 := fun h => by rw [h, map_zero] at hs; exact lt_irrefl _ hs
  have ha0 : r / s ≠ 0 := div_ne_zero hr0 hs0
  obtain ⟨N, hN⟩ := rankOne p A hA ((p : ℕ) : CA A) (r / s) (v_p_lt_one p A hA) ha0
  have key : ∀ m n : ℕ, N + 1 ≤ m → m ≤ n → Valued.v (f n - f m) < Valued.v (r / s) := by
    intro m n hm hmn
    calc Valued.v (f n - f m) ≤ Valued.v ((p : ℕ) : CA A) ^ m := hf m n hmn
      _ ≤ Valued.v ((p : ℕ) : CA A) ^ (N + 1) :=
          pow_le_pow_right_of_le_one' (v_p_lt_one p A hA).le hm
      _ < Valued.v ((p : ℕ) : CA A) ^ N :=
          pow_lt_pow_right_of_lt_one₀ (v_p_pos p A hA) (v_p_lt_one p A hA) (Nat.lt_succ_self N)
      _ ≤ Valued.v (r / s) := hN
  refine ⟨N + 1, fun m hm n hn => ?_⟩
  change (Valued.v : Valuation (CA A) A.ValueGroup).restrict (f n - f m) < γ.val
  rw [← hrs, ← map_div₀, Valuation.restrict_lt_iff]
  rcases le_total m n with hmn | hnm
  · exact key m n hm hmn
  · rw [Valuation.map_sub_swap]; exact key n m hn hnm

theorem isPrecomplete : IsPrecomplete (Ideal.span {((p : ℕ) : ↥(OA A))}) ↥(OA A) := by
  refine ⟨fun f hf => ?_⟩

  have hf' : ∀ m n : ℕ, m ≤ n →
      Valued.v ((f n : CA A) - (f m : CA A)) ≤ Valued.v ((p : ℕ) : CA A) ^ m := by
    intro m n hmn
    have h := hf hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, mem_span_pow_iff p A hA] at h
    rw [← Valuation.map_neg, neg_sub]
    exact_mod_cast h
  have hc : CauchySeq (fun n => (f n : CA A)) := cauchySeq_of_le p A hA _ hf'
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc

  have hLO : L ∈ OA A := by
    refine (Valued.isClosed_valuationSubring (CA A)).mem_of_tendsto hL ?_
    exact Filter.Eventually.of_forall (fun n => (f n).2)
  refine ⟨⟨L, hLO⟩, fun m => ?_⟩

  have hmem : L ∈ {x : CA A | Valued.v (x - (f m : CA A)) ≤ Valued.v (((p : ℕ) : CA A) ^ m)} := by
    refine (isClosed_closedBall_sub A _ _).mem_of_tendsto hL ?_
    rw [Filter.eventually_atTop]
    refine ⟨m, fun n hn => ?_⟩
    change Valued.v ((f n : CA A) - (f m : CA A)) ≤ Valued.v (((p : ℕ) : CA A) ^ m)
    rw [map_pow]
    exact hf' m n hn
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, mem_span_pow_iff p A hA]
  change Valued.v ((f m : CA A) - L) ≤ _
  rw [← Valuation.map_neg, neg_sub, ← map_pow]
  exact hmem

theorem isAdicComplete : IsAdicComplete (Ideal.span {((p : ℕ) : ↥(OA A))}) ↥(OA A) :=
  { toIsHausdorff := isHausdorff p A hA, toIsPrecomplete := isPrecomplete p A hA }

end OverP

theorem exists_algClosure_v_sub_lt (c : CA A) :
    ∃ a : AlgebraicClosure ℚ, Valued.v (c - ((a : AlgebraicClosure ℚ) : CA A)) < 1 := by
  have hU : IsOpen {x : CA A | Valued.v (x - c) < 1} := by
    have h := (Valued.isOpen_ball (CA A)
      (1 : MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v : Valuation (CA A) A.ValueGroup)))).preimage
      (continuous_sub_right c)
    convert h using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact (Valuation.restrict_lt_one_iff _).symm
  have hne : ({x : CA A | Valued.v (x - c) < 1}).Nonempty := ⟨c, by simp⟩
  obtain ⟨w, hw⟩ :=
    (UniformSpace.Completion.denseRange_coe (α := WithVal A.valuation)).exists_mem_open hU hne
  refine ⟨WithVal.equiv A.valuation w, ?_⟩
  change Valued.v (c - (((WithVal.equiv A.valuation).symm (WithVal.equiv A.valuation w) :
    WithVal A.valuation) : CA A)) < 1
  rw [RingEquiv.symm_apply_apply, ← Valuation.map_neg, neg_sub]
  exact hw

abbrev res : ↥(OA A) →+* IsLocalRing.ResidueField ↥(OA A) := IsLocalRing.residue ↥(OA A)

theorem res_eq_res_iff (x y : ↥(OA A)) :
    res A x = res A y ↔ Valued.v ((x : CA A) - (y : CA A)) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff]
  rfl

theorem exists_mem_A_res_eq (z : ↥(OA A)) :
    ∃ (a : AlgebraicClosure ℚ) (ha : ((a : AlgebraicClosure ℚ) : CA A) ∈ OA A),
      a ∈ A ∧ res A ⟨_, ha⟩ = res A z := by
  obtain ⟨a, ha⟩ := exists_algClosure_v_sub_lt A (z : CA A)
  have hva : Valued.v ((a : AlgebraicClosure ℚ) : CA A) ≤ 1 := by
    have : ((a : AlgebraicClosure ℚ) : CA A) = (z : CA A) - ((z : CA A) - (a : CA A)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le (v_coe_le_one A z) ha.le)
  refine ⟨a, (mem_OA_iff A _).mpr hva, ?_, ?_⟩
  · rw [← ValuationSubring.valuation_le_one_iff, ← v_coe_algClosure]; exact hva
  · rw [res_eq_res_iff, ← Valuation.map_neg, neg_sub]
    exact ha

theorem root_bound {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation F Γ)
    (d : ℕ) (a : ℕ → F) (ha : ∀ i, w (a i) ≤ 1) (α : F)
    (hα : α ^ d + ∑ i ∈ Finset.range d, a i * α ^ i = 0) : w α ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hα0 : w α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have h1 : w (∑ i ∈ Finset.range d, a i * α ^ i) < w α ^ d := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ hα0) (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc w (a i) * w α ^ i ≤ 1 * w α ^ i := by gcongr; exact ha i
      _ = w α ^ i := one_mul _
      _ < w α ^ d := pow_lt_pow_right₀ hgt hi
  have h2 : α ^ d = -(∑ i ∈ Finset.range d, a i * α ^ i) := eq_neg_of_add_eq_zero_left hα
  have h3 : w (α ^ d) = w (∑ i ∈ Finset.range d, a i * α ^ i) := by rw [h2, Valuation.map_neg]
  rw [map_pow] at h3
  rw [← h3] at h1
  exact lt_irrefl _ h1

def J : AlgebraicClosure ℚ →+* CA A :=
  (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion).comp
    (WithVal.equiv A.valuation).symm.toRingHom

theorem J_apply (a : AlgebraicClosure ℚ) : J A a = ((a : AlgebraicClosure ℚ) : CA A) := rfl

theorem isAlgClosed_residueField : IsAlgClosed (IsLocalRing.ResidueField ↥(OA A)) := by
  refine IsAlgClosed.of_exists_root _ (fun P hPm hPirr => ?_)

  have hlift : P ∈ Polynomial.lifts (res A) :=
    (Polynomial.mem_lifts P).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective P)
  obtain ⟨Q, hQmap, hQdeg, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hPm
  set d := Q.natDegree with hd
  have hd1 : 1 ≤ d := by
    have h0 := Polynomial.degree_pos_of_irreducible hPirr
    have h1 : 0 < P.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr h0
    have h2 : Q.natDegree = P.natDegree := hQdeg
    omega

  choose a ha hAa hres using fun i : ℕ => exists_mem_A_res_eq A (Q.coeff i)

  set R : Polynomial (AlgebraicClosure ℚ) :=
    Polynomial.X ^ d + ∑ i ∈ Finset.range d, Polynomial.C (a i) * Polynomial.X ^ i with hR
  have hlow : (∑ i ∈ Finset.range d, Polynomial.C (a i) * Polynomial.X ^ i).degree < (d : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr ?_
    intro i hi
    rw [Finset.mem_range] at hi
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le i (a i)) (WithBot.coe_lt_coe.mpr hi)
  have hRdeg : R.degree = (d : WithBot ℕ) := by
    rw [hR, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rwa [Polynomial.degree_X_pow]
  have hRdeg0 : R.degree ≠ 0 := by
    rw [hRdeg]; exact_mod_cast (Nat.one_le_iff_ne_zero.mp hd1)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root R hRdeg0
  have hαeval : α ^ d + ∑ i ∈ Finset.range d, a i * α ^ i = 0 := by
    have := hα
    rw [Polynomial.IsRoot.def, hR, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at this
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using this

  have hαA : A.valuation α ≤ 1 :=
    root_bound A.valuation d a (fun i => (A.valuation_le_one_iff _).mpr (hAa i)) α hαeval
  have hαO : ((α : AlgebraicClosure ℚ) : CA A) ∈ OA A := by
    rw [mem_OA_iff, v_coe_algClosure]; exact hαA
  set α' : ↥(OA A) := ⟨_, hαO⟩ with hα'
  refine ⟨res A α', ?_⟩

  rw [← hQmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_iff]

  have hQsum : ((Polynomial.eval α' Q : ↥(OA A)) : CA A) =
      (α' : CA A) ^ d + ∑ i ∈ Finset.range d, ((Q.coeff i : ↥(OA A)) : CA A) * (α' : CA A) ^ i := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, ← hd, hQm.coeff_natDegree, one_mul, add_comm]
    push_cast
    rfl
  have hRC : (α' : CA A) ^ d + ∑ i ∈ Finset.range d, ((a i : AlgebraicClosure ℚ) : CA A) * (α' : CA A) ^ i = 0 := by
    have := congrArg (J A) hαeval
    rw [map_zero, map_add, map_pow, map_sum] at this
    simp only [map_mul, map_pow, J_apply] at this
    exact this
  have hdiff : ((Polynomial.eval α' Q : ↥(OA A)) : CA A) =
      ∑ i ∈ Finset.range d, (((Q.coeff i : ↥(OA A)) : CA A) - ((a i : AlgebraicClosure ℚ) : CA A)) *
        (α' : CA A) ^ i := by
    rw [hQsum, ← sub_zero ((α' : CA A) ^ d + _), ← hRC]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hdiff]
  refine Valuation.map_sum_lt _ one_ne_zero (fun i _ => ?_)
  rw [map_mul, map_pow]
  have h1 : Valued.v (((Q.coeff i : ↥(OA A)) : CA A) - ((a i : AlgebraicClosure ℚ) : CA A)) < 1 := by
    have := (res_eq_res_iff A _ _).mp (hres i).symm
    exact this
  calc Valued.v (((Q.coeff i : ↥(OA A)) : CA A) - ((a i : AlgebraicClosure ℚ) : CA A)) * Valued.v (α' : CA A) ^ i
      ≤ Valued.v (((Q.coeff i : ↥(OA A)) : CA A) - ((a i : AlgebraicClosure ℚ) : CA A)) * 1 := by
        gcongr
        exact pow_le_one₀ zero_le' (v_coe_le_one A α')
    _ < 1 := by rw [mul_one]; exact h1

section OverP2

variable [hA : Fact (A.LiesOverPrime p)]

set_option synthInstance.checkSynthOrder false in
scoped instance charP_residueField : CharP (IsLocalRing.ResidueField ↥(OA A)) p := by
  refine (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_
  have : ((p : ℕ) : IsLocalRing.ResidueField ↥(OA A)) = res A ((p : ℕ) : ↥(OA A)) := by rw [map_natCast]
  rw [this, IsLocalRing.residue_eq_zero_iff]
  exact p_mem_maximalIdeal p A hA.out

scoped instance fact_not_isUnit : Fact (¬ IsUnit ((p : ℕ) : ↥(OA A))) := ⟨not_isUnit_p p A hA.out⟩

scoped instance isAdicComplete_inst : IsAdicComplete (Ideal.span {((p : ℕ) : ↥(OA A))}) ↥(OA A) :=
  isAdicComplete p A hA.out

theorem residue_pow_eq (x : IsLocalRing.ResidueField ↥(OA A)) : ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  classical
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥(OA A)) := ZMod.algebra _ p
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨a, ha, hAa, hres⟩ := exists_mem_A_res_eq A z

  have halg : IsAlgebraic ℚ a := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a
  obtain ⟨P, hP0, hPa⟩ := halg
  set Pz : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P with hPz
  have hPza : Polynomial.aeval a Pz = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) P hPa
  have hPz0 : Pz ≠ 0 := by
    intro h
    exact hP0 ((IsLocalization.integerNormalization_eq_zero_iff (le_refl _) P).mp h)
  set P₁ : Polynomial ℤ := Pz.primPart with hP₁
  have hprim : P₁.IsPrimitive := Polynomial.isPrimitive_primPart Pz
  have hP₁a : Polynomial.aeval a P₁ = 0 := by
    have h := Polynomial.eq_C_content_mul_primPart Pz
    have hc : Pz.content ≠ 0 := fun hc => hPz0 (Polynomial.content_eq_zero_iff.mp hc)
    rw [h, map_mul, Polynomial.aeval_C] at hPza
    have hc' : (algebraMap ℤ (AlgebraicClosure ℚ)) Pz.content ≠ 0 :=
      (map_ne_zero_iff _ (RingHom.injective_int _)).mpr hc
    exact (mul_eq_zero.mp hPza).resolve_left hc'

  set Pbar : Polynomial (ZMod p) := P₁.map (Int.castRingHom (ZMod p)) with hPbar
  have hPbar0 : Pbar ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ P₁ := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have : (Pbar.coeff i) = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [hPbar, Polynomial.coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have hu := hprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := hp.out.two_le
    omega

  have hroot : Polynomial.aeval (res A z) Pbar = 0 := by
    have h1 : Polynomial.aeval (res A z) Pbar = Polynomial.aeval (res A z) P₁ := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, hPbar, Polynomial.eval₂_map,
        Subsingleton.elim ((algebraMap (ZMod p) (IsLocalRing.ResidueField ↥(OA A))).comp (Int.castRingHom (ZMod p)))
          (algebraMap ℤ (IsLocalRing.ResidueField ↥(OA A)))]
    rw [h1, ← hres, ← RingHom.toIntAlgHom_apply (res A), Polynomial.aeval_algHom_apply,
      RingHom.toIntAlgHom_apply, IsLocalRing.residue_eq_zero_iff]
    have h2 : (Polynomial.aeval (⟨_, ha⟩ : ↥(OA A)) P₁ : ↥(OA A)) = 0 := by
      apply Subtype.ext
      change (OA A).subtype (Polynomial.eval₂ (algebraMap ℤ ↥(OA A)) ⟨_, ha⟩ P₁) = 0
      rw [Polynomial.hom_eval₂,
        Subsingleton.elim ((OA A).subtype.comp (algebraMap ℤ ↥(OA A))) ((J A).comp (algebraMap ℤ (AlgebraicClosure ℚ)))]
      change Polynomial.eval₂ ((J A).comp (algebraMap ℤ (AlgebraicClosure ℚ))) (J A a) P₁ = 0
      rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hP₁a, map_zero]
    rw [h2]
    exact Ideal.zero_mem _
  have halgz : IsAlgebraic (ZMod p) (res A z) := ⟨Pbar, hPbar0, hroot⟩

  set F := IntermediateField.adjoin (ZMod p) {res A z} with hF
  haveI : FiniteDimensional (ZMod p) ↥F := IntermediateField.adjoin.finiteDimensional halgz.isIntegral
  haveI : Finite ↥F := Module.finite_of_finite (ZMod p)
  letI : Fintype ↥F := Fintype.ofFinite ↥F
  have hcard : Fintype.card ↥F = p ^ Module.finrank (ZMod p) ↥F := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := ↥F), ZMod.card]
  refine ⟨Module.finrank (ZMod p) ↥F, Module.finrank_pos, ?_⟩
  have hmem : res A z ∈ F := IntermediateField.mem_adjoin_simple_self (ZMod p) (res A z)
  have h := FiniteField.pow_card (⟨res A z, hmem⟩ : ↥F)
  rw [hcard] at h
  have h' := congrArg (fun y : ↥F => (y : IsLocalRing.ResidueField ↥(OA A))) h
  simpa using h'

scoped instance perfectRing_residueField : PerfectRing (IsLocalRing.ResidueField ↥(OA A)) p := by
  haveI := isAlgClosed_residueField A
  haveI := IsAlgClosed.perfectField (IsLocalRing.ResidueField ↥(OA A))
  exact PerfectField.toPerfectRing p

abbrev B : Type := ModP ↥(OA A) p

abbrev πB : ↥(OA A) →+* B p A := Ideal.Quotient.mk _

theorem span_p_le_maximalIdeal : Ideal.span {((p : ℕ) : ↥(OA A))} ≤ IsLocalRing.maximalIdeal ↥(OA A) := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact p_mem_maximalIdeal p A hA.out

def τ : B p A →+* IsLocalRing.ResidueField ↥(OA A) :=
  Ideal.Quotient.lift _ (res A) (fun a ha =>
    (IsLocalRing.residue_eq_zero_iff a).mpr (span_p_le_maximalIdeal p A ha))

theorem τ_πB (x : ↥(OA A)) : τ p A (πB p A x) = res A x := Ideal.Quotient.lift_mk _ _ _

theorem τ_surjective : Function.Surjective (τ p A) := by
  intro x
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨πB p A z, τ_πB p A z⟩

theorem exists_pow_eq_zero_of_τ_eq_zero (b : B p A) (hb : τ p A b = 0) : ∃ n : ℕ, b ^ n = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  change τ p A (πB p A x) = 0 at hb
  rw [τ_πB, IsLocalRing.residue_eq_zero_iff] at hb
  obtain ⟨n, hn⟩ := exists_pow_mem_span_p p A hA.out x hb
  refine ⟨n, ?_⟩
  change πB p A x ^ n = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hn

theorem pow_iterate_sub {R : Type*} [CommRing R] [CharP R p] (u : R) (r : ℕ) (s : ℕ) :
    u ^ (p ^ r) ^ (s + 1) - u ^ (p ^ r) ^ s = (u ^ p ^ r - u) ^ (p ^ r) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e1 : u ^ (p ^ r) ^ (s + 1 + 1) = (u ^ (p ^ r) ^ (s + 1)) ^ p ^ r := by
      rw [pow_succ (p ^ r) (s + 1), pow_mul]
    have e2 : u ^ (p ^ r) ^ (s + 1) = (u ^ (p ^ r) ^ s) ^ p ^ r := by
      rw [pow_succ (p ^ r) s, pow_mul]
    have e3 : (u ^ p ^ r - u) ^ (p ^ r) ^ (s + 1) = ((u ^ p ^ r - u) ^ (p ^ r) ^ s) ^ p ^ r := by
      rw [pow_succ (p ^ r) s, pow_mul]
    rw [e1, e3, ← ih, sub_pow_char_pow, ← e2]

theorem exists_fixedPoint (u : B p A) (r : ℕ) (hr : 0 < r) (hu : ∃ e : ℕ, (u ^ p ^ r - u) ^ e = 0) :
    ∃ s : ℕ, (u ^ (p ^ r) ^ s) ^ p ^ r = u ^ (p ^ r) ^ s := by
  obtain ⟨e, he⟩ := hu
  refine ⟨e, ?_⟩
  have h1 : (u ^ (p ^ r) ^ e) ^ p ^ r = u ^ (p ^ r) ^ (e + 1) := by
    rw [pow_succ (p ^ r) e, pow_mul]
  rw [h1, ← sub_eq_zero, pow_iterate_sub p u r e]
  have hle : e ≤ (p ^ r) ^ e := by
    have : 1 < p ^ r := Nat.one_lt_pow hr.ne' hp.out.one_lt
    exact (Nat.lt_pow_self this).le
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  rw [hc, pow_add, he, zero_mul]

theorem fixedPoint_unique (w₁ w₂ : B p A) (r : ℕ) (hr : 0 < r) (h₁ : w₁ ^ p ^ r = w₁) (h₂ : w₂ ^ p ^ r = w₂)
    (h : ∃ e : ℕ, (w₁ - w₂) ^ e = 0) : w₁ = w₂ := by
  obtain ⟨e, he⟩ := h
  have hfix : ∀ s : ℕ, (w₁ - w₂) ^ (p ^ r) ^ s = w₁ - w₂ := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ (p ^ r) s, pow_mul, ih, sub_pow_char_pow, h₁, h₂]
  have hle : e ≤ (p ^ r) ^ e := by
    have : 1 < p ^ r := Nat.one_lt_pow hr.ne' hp.out.one_lt
    exact (Nat.lt_pow_self this).le
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  have := hfix e
  rw [hc, pow_add, he, zero_mul] at this
  exact (sub_eq_zero.mp this.symm)

theorem fixed_mul {R : Type*} [Monoid R] (w : R) (r t : ℕ) (h : w ^ p ^ r = w) : w ^ p ^ (r * t) = w := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

theorem exists_sec (x : IsLocalRing.ResidueField ↥(OA A)) :
    ∃ w : B p A, τ p A w = x ∧ ∃ r : ℕ, 0 < r ∧ w ^ p ^ r = w := by
  obtain ⟨r, hr, hx⟩ := residue_pow_eq p A x
  obtain ⟨u, rfl⟩ := τ_surjective p A x
  have hd : ∃ e : ℕ, (u ^ p ^ r - u) ^ e = 0 := by
    apply exists_pow_eq_zero_of_τ_eq_zero
    rw [map_sub, map_pow, hx, sub_self]
  obtain ⟨s, hs⟩ := exists_fixedPoint p A u r hr hd
  refine ⟨u ^ (p ^ r) ^ s, ?_, r, hr, hs⟩
  rw [map_pow]

  have : ∀ t : ℕ, τ p A u ^ (p ^ r) ^ t = τ p A u := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ (p ^ r) t, pow_mul, ih, hx]
  exact this s

def secFun (x : IsLocalRing.ResidueField ↥(OA A)) : B p A := (exists_sec p A x).choose

theorem τ_secFun (x : IsLocalRing.ResidueField ↥(OA A)) : τ p A (secFun p A x) = x :=
  (exists_sec p A x).choose_spec.1

theorem secFun_fixed (x : IsLocalRing.ResidueField ↥(OA A)) :
    ∃ r : ℕ, 0 < r ∧ (secFun p A x) ^ p ^ r = secFun p A x :=
  (exists_sec p A x).choose_spec.2

theorem secFun_eq_of_fixed (x : IsLocalRing.ResidueField ↥(OA A)) (w : B p A) (hw : τ p A w = x)
    (r : ℕ) (hr : 0 < r) (hfix : w ^ p ^ r = w) : secFun p A x = w := by
  obtain ⟨r₁, hr₁, h₁⟩ := secFun_fixed p A x
  refine fixedPoint_unique p A _ _ (r₁ * r) (Nat.mul_pos hr₁ hr) (fixed_mul p _ r₁ r h₁) ?_ ?_
  · rw [mul_comm]; exact fixed_mul p _ r r₁ hfix
  · apply exists_pow_eq_zero_of_τ_eq_zero
    rw [map_sub, τ_secFun, hw, sub_self]

def secHom : IsLocalRing.ResidueField ↥(OA A) →+* B p A where
  toFun := secFun p A
  map_one' := secFun_eq_of_fixed p A 1 1 (map_one _) 1 one_pos (one_pow _)
  map_mul' x y := by
    obtain ⟨r₁, hr₁, h₁⟩ := secFun_fixed p A x
    obtain ⟨r₂, hr₂, h₂⟩ := secFun_fixed p A y
    refine secFun_eq_of_fixed p A (x * y) _ ?_ (r₁ * r₂) (Nat.mul_pos hr₁ hr₂) ?_
    · rw [map_mul, τ_secFun, τ_secFun]
    · rw [mul_pow, fixed_mul p _ r₁ r₂ h₁, mul_comm r₁ r₂, fixed_mul p _ r₂ r₁ h₂]
  map_zero' := secFun_eq_of_fixed p A 0 0 (map_zero _) 1 one_pos (by
    rw [pow_one]; exact zero_pow hp.out.ne_zero)
  map_add' x y := by
    obtain ⟨r₁, hr₁, h₁⟩ := secFun_fixed p A x
    obtain ⟨r₂, hr₂, h₂⟩ := secFun_fixed p A y
    refine secFun_eq_of_fixed p A (x + y) _ ?_ (r₁ * r₂) (Nat.mul_pos hr₁ hr₂) ?_
    · rw [map_add, τ_secFun, τ_secFun]
    · rw [add_pow_char_pow, fixed_mul p _ r₁ r₂ h₁, mul_comm r₁ r₂, fixed_mul p _ r₂ r₁ h₂]

theorem τ_secHom (x : IsLocalRing.ResidueField ↥(OA A)) : τ p A (secHom p A x) = x := τ_secFun p A x

def ιTilt : IsLocalRing.ResidueField ↥(OA A) →+* PreTilt ↥(OA A) p :=
  Perfection.lift p (IsLocalRing.ResidueField ↥(OA A)) (ModP ↥(OA A) p) (secHom p A)

theorem coeff_zero_ιTilt (x : IsLocalRing.ResidueField ↥(OA A)) :
    PreTilt.coeff 0 (ιTilt p A x) = secHom p A x := by
  have h := Perfection.lift_symm_apply p (IsLocalRing.ResidueField ↥(OA A)) (S := ModP ↥(OA A) p) (ιTilt p A)
  rw [ιTilt, Equiv.symm_apply_apply] at h
  have := congrArg (fun f => f x) h
  first | simpa using this | (simp at this; exact this.symm) | exact this.symm | exact this

def ψ : WittVector p (IsLocalRing.ResidueField ↥(OA A)) →+* CA A :=
  (OA A).subtype.comp ((WittVector.fontaineTheta ↥(OA A) p).comp (WittVector.map (ιTilt p A)))

theorem ψ_apply (y : WittVector p (IsLocalRing.ResidueField ↥(OA A))) :
    ψ p A y = ((WittVector.fontaineTheta ↥(OA A) p (WittVector.map (ιTilt p A) y) : ↥(OA A)) : CA A) := rfl

theorem v_ψ_le_one (y : WittVector p (IsLocalRing.ResidueField ↥(OA A))) : Valued.v (ψ p A y) ≤ 1 :=
  v_coe_le_one A _

theorem ψ_natCast (n : ℕ) : ψ p A n = n := map_natCast _ n

theorem ψ_injective : Function.Injective (ψ p A) := by
  haveI := isAlgClosed_residueField A
  rw [injective_iff_map_eq_zero]
  intro y hy
  by_contra hy0

  set K := RingHom.ker (ψ p A) with hK
  haveI : K.IsPrime := RingHom.ker_isPrime _
  have hpK : ((p : ℕ) : WittVector p (IsLocalRing.ResidueField ↥(OA A))) ∉ K := by
    intro h
    rw [hK, RingHom.mem_ker, ψ_natCast] at h
    exact p_ne_zero p A hA.out h
  have hKne : K ≠ ⊥ := by
    intro h
    have : y ∈ K := hy
    rw [h, Ideal.mem_bot] at this
    exact hy0 this
  have hKmax : K.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hKne
  have hKeq : K = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal hKmax
  apply hpK
  rw [hKeq]
  exact (WittVector.irreducible p (k := IsLocalRing.ResidueField ↥(OA A))).not_isUnit

theorem ψ_teichmuller (x : IsLocalRing.ResidueField ↥(OA A)) :
    ψ p A (WittVector.teichmuller p x) = ((PreTilt.untilt (ιTilt p A x) : ↥(OA A)) : CA A) := by
  rw [ψ_apply, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]

theorem residual_surjective (z : CA A) (hz : Valued.v z ≤ 1) :
    ∃ y : WittVector p (IsLocalRing.ResidueField ↥(OA A)), Valued.v (z - ψ p A y) < 1 := by
  set z' : ↥(OA A) := ⟨z, (mem_OA_iff A z).mpr hz⟩ with hz'
  refine ⟨WittVector.teichmuller p (res A z'), ?_⟩
  rw [ψ_teichmuller]
  set w : ↥(OA A) := PreTilt.untilt (ιTilt p A (res A z')) with hw
  have h1 : πB p A w = secHom p A (res A z') := by
    rw [hw, PreTilt.mk_untilt_eq_coeff_zero, coeff_zero_ιTilt]
  have h2 : res A w = res A z' := by
    rw [← τ_πB p A w, h1, τ_secHom]
  have h3 := (res_eq_res_iff A _ _).mp h2.symm
  exact h3

end OverP2

end WittUnramSol
p2m_reactivate "P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime.WittUnramSol"

end
p2m_reactivate "P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime.WittUnramSol"

open WittUnramSol in
theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (_ : PerfectRing k p) (_ : IsAlgClosed k)
      (ψ : WittVector p k →+* A.valuation.Completion),
      (∀ x : k, ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x) ∧
      Function.Injective ψ ∧
      (∀ y : WittVector p k, Valued.v (ψ y) ≤ 1) ∧
      (∀ z : A.valuation.Completion, Valued.v z ≤ 1 → ∃ y : WittVector p k, Valued.v (z - ψ y) < 1) := by
  haveI : Fact (A.LiesOverPrime p) := ⟨hA⟩
  haveI := isAlgClosed_residueField A
  exact ⟨IsLocalRing.ResidueField ↥(OA A), inferInstance, inferInstance, inferInstance, inferInstance,
    WittUnramSol.ψ p A, residue_pow_eq p A, ψ_injective p A, v_ψ_le_one p A, residual_surjective p A⟩

end S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_isAlgClosed_wittVector_ringHom_completion_of_liesOverPrime (solution)
