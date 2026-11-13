-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.caseB_order_u_of_analytic_inequality
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:00:54.199619+00:00
-- url     : https://prove2.me/submissions/d7611887-4b6a-416a-9970-d0021a7bfc20

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CaseBOrder.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Theorems.Thm_OddOrder_Peterfalvi_S15_caseB_order_x_absurd_of_ge
import Theorems.Thm_OddOrder_Peterfalvi_S15_numeric_bounds_of_analytic_inequality
import Theorems.Thm_OddOrder_Peterfalvi_S15_c_eq_one_of_analytic_inequality

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`S`-instance chief-factor `q` identity**: the `(9.x)` chief-factor prime `data.q` of the
`S`-instance `toTypesIIIIIIVSetupS` is the type-`P` invariant `q = |W₁|`.  Extracted from
`u_le_cyclotomicQuotient` for reuse by the (13.3.b) dichotomy translations. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_q_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
  change Nat.card ↥hyp.Sdata.W1 = hyp.q
  rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]

/-- **`S`-instance chief-factor prime identity**: the chief prime `chief.p = p`, forced by
`|P| = p^q = chief.p^q · |N|`.  Extracted from `u_le_cyclotomicQuotient`. -/
theorem Hypothesis.chiefFactorS_p_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.p = hyp.p := by
  have := chief.N_normal
  have hHeq : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [hHeq]; exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hyp.toTypesIIIIIIVSetupS_q_eq hG] at hquot
  have hsplitP := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplitP
  have hdvd : chief.p ∣ hyp.p ^ hyp.q :=
    dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') (hsplitP ▸ Dvd.intro _ rfl)
  exact (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
    (chief.p_prime.dvd_of_dvd_pow hdvd)

/-- **`S`-instance `u` identity**: the `U`-action image order `chars.u = |Ū| = [U : C_U(P)] = u`.
Extracted from `u_le_cyclotomicQuotient`; the (13.3.b) dichotomy uses it to transport the
`caseB_of_no_irreducible_sOf_H0Cprime` conclusion `chars.u = (p^q−1)/(p−1)` to `hyp.u`. -/
theorem Hypothesis.mkSection11CharacterDataS_u_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    (hyp.mkSection11CharacterDataS hG chief).u = hyp.u := by
  have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hc0 ?_
  have key : (hyp.mkSection11CharacterDataS hG chief).u
      * Nat.card ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
      = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).U := by
    rw [← OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u (hyp.mkSection11CharacterDataS hG chief)]
    have h := Subgroup.index_mul_card
      ((OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief).subgroupOf
        (hyp.toTypesIIIIIIVSetupS hG).U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)).toEquiv] at h
  rw [hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief, ← hyp.c_eq_card_C,
    show (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U from hyp.Sdata_U_eq, hyp.card_U_eq_uc] at key
  exact key

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- Lower estimate for the analytic parameter `m` of **Peterfalvi (13.10)**.
Dropping the (positive) last summand and bounding `(q-1)/q^p ≤ 1/q^2` (valid once
`p ≥ 3`) gives `m ≥ 1 - 1/(q-1) - 1/q^2`. -/
theorem m_value_ge_aux {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (1 : ℚ) - 1 / ((q : ℚ) - 1) - 1 / (q : ℚ) ^ 2 ≤
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hqpos : (0 : ℚ) < (q : ℚ) := by linarith
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have hXpos : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hX3 : (q : ℚ) ^ 3 ≤ (q : ℚ) ^ p := pow_le_pow_right₀ (by linarith) hp
  have hfrac : ((q : ℚ) - 1) / (q : ℚ) ^ p ≤ 1 / (q : ℚ) ^ 2 := by
    rw [div_le_div_iff₀ hXpos (by positivity)]
    have e : (q : ℚ) ^ 3 = ((q : ℚ) - 1) * (q : ℚ) ^ 2 + (q : ℚ) ^ 2 := by ring
    have hsq : (0 : ℚ) ≤ (q : ℚ) ^ 2 := sq_nonneg _
    linarith [hX3, e, hsq]
  have hpos : (0 : ℚ) ≤ 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by positivity
  linarith [hfrac, hpos]

/-- **Peterfalvi (13.11.b)** numeric bound: `q ≥ 5 ⇒ m > 7/10`. -/
theorem m_value_gt_seven_tenths {q p : ℕ} (hq : 5 ≤ q) (hp : 3 ≤ p) :
    (7 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have haux := m_value_ge_aux hq hp
  have hq5 : (5 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 25 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq5]
  linarith [haux, h1, h2]

/-- **Peterfalvi (13.11.a)** numeric bound: `q ≥ 7 ⇒ m > 8/10`. -/
theorem m_value_gt_four_fifths {q p : ℕ} (hq : 7 ≤ q) (hp : 3 ≤ p) :
    (8 : ℚ) / 10 <
      1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
        1 / (((q : ℚ) - 1) * (q : ℚ) ^ p) := by
  have hq5 : 5 ≤ q := by omega
  have haux := m_value_ge_aux hq5 hp
  have hq7 : (7 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
  have hq1pos : (0 : ℚ) < (q : ℚ) - 1 := by linarith
  have h1 : 1 / ((q : ℚ) - 1) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hq1pos (by norm_num)]; linarith
  have h2 : 1 / (q : ℚ) ^ 2 ≤ 1 / 49 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hq7]
  linarith [haux, h1, h2]

namespace Hypothesis

/-- **Peterfalvi (13.11.a)** at the Section 15 hypothesis level: if `q ≥ 7`,
then the concrete analytic parameter satisfies `m > 8/10`. -/
theorem m_gt_four_fifths_of_seven_le_q (hyp : Hypothesis (G := G))
    (hq7 : 7 ≤ hyp.q) :
    hyp.m > (8 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_four_fifths hq7 hyp.three_le_p

/-- **Peterfalvi (13.11.b)** at the Section 15 hypothesis level: if `q ≥ 5`,
then the concrete analytic parameter satisfies `m > 7/10`. -/
theorem m_gt_seven_tenths_of_five_le_q (hyp : Hypothesis (G := G))
    (hq5 : 5 ≤ hyp.q) :
    hyp.m > (7 / 10 : ℚ) := by
  rw [hyp.m_eq]
  exact m_value_gt_seven_tenths hq5 hyp.three_le_p

end Hypothesis

/-- The parity calculation behind **Peterfalvi (13.14)**: if `p` is odd, the
geometric sum of its first `q` powers has the same parity as `q`. -/
private theorem sum_range_pow_mod_two_eq {p q : ℕ} (hpodd : Odd p) :
    (∑ k ∈ Finset.range q, p ^ k) % 2 = q % 2 := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hpow : p ^ q % 2 = 1 := Nat.odd_iff.mp hpodd.pow
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hpow]
      omega

/-- The oddness part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_odd {p q : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hqodd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [Nat.odd_iff, sum_range_pow_mod_two_eq hpodd, Nat.odd_iff.mp hqodd]

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

/-- If `p` is not `1 mod q`, then the prime `q` does not divide the
cyclotomic quotient in **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_not_dvd_self_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ¬ q ∣ (p ^ q - 1) / (p - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  intro hdiv
  rw [← Nat.geomSum_eq hp.two_le q] at hdiv
  have hsum_zero_nat : ((∑ k ∈ Finset.range q, p ^ k : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hsum_zero_zmod : (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_pow] using hsum_zero_nat
  have hgeom :
      (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) =
        (p : ZMod q) ^ q - 1 :=
    geom_sum_mul (p : ZMod q) q
  have hp_eq_one : (p : ZMod q) = 1 := by
    have hzero :
        (∑ k ∈ Finset.range q, (p : ZMod q) ^ k) * ((p : ZMod q) - 1) = 0 := by
      rw [hsum_zero_zmod, zero_mul]
    rw [hgeom, ZMod.pow_card] at hzero
    exact sub_eq_zero.mp hzero
  exact hpq ((ZMod.natCast_eq_natCast_iff p 1 q).mp (by simpa using hp_eq_one))

/-- Prime divisors of the cyclotomic quotient in the non-`1 mod q` case are
`1 mod q`. -/
theorem cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q])
    (hr : r.Prime) (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r ≡ 1 [MOD q] := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact q.Prime := ⟨hq⟩
  have hr_ne_q : r ≠ q := by
    intro h
    exact cyclotomic_quotient_not_dvd_self_of_not_modEq_one hp hq hpq
      (by simpa [h] using hrdvd)
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdiv
    rcases (Nat.dvd_prime hq).mp hdiv with hr_eq_one | hr_eq_q
    · exact hr.ne_one hr_eq_one
    · exact hr_ne_q hr_eq_q
  have : NeZero (q : ZMod r) :=
    NeZero.of_not_dvd (ZMod r) hr_not_dvd_q
  have hrdvd_sum : r ∣ ∑ k ∈ Finset.range q, p ^ k := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hroot :
      Polynomial.IsRoot (Polynomial.cyclotomic q (ZMod r))
        (Nat.castRingHom (ZMod r) p) := by
    rw [Polynomial.IsRoot.def, Polynomial.cyclotomic_prime]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    simpa [Nat.cast_sum, Nat.cast_pow] using
      (ZMod.natCast_eq_zero_iff (∑ k ∈ Finset.range q, p ^ k) r).mpr hrdvd_sum
  have hcop : p.Coprime r :=
    Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  have hnot_r_dvd_p : ¬ r ∣ p :=
    hr.coprime_iff_not_dvd.mp hcop.symm
  have hp_ne_zero : (p : ZMod r) ≠ 0 := by
    intro hzero
    exact hnot_r_dvd_p ((ZMod.natCast_eq_zero_iff p r).mp hzero)
  have horder_dvd : orderOf (p : ZMod r) ∣ r - 1 :=
    ZMod.orderOf_dvd_card_sub_one hp_ne_zero
  have horder_eq : q = orderOf (p : ZMod r) :=
    (Polynomial.isRoot_cyclotomic_iff.mp hroot).eq_orderOf
  rw [← horder_eq] at horder_dvd
  exact ((Nat.modEq_iff_dvd' hr.pos).mpr horder_dvd).symm

/-- If every prime factor of `x` is `1 mod q`, then `x` is `1 mod q`. -/
theorem modEq_one_of_forall_primeFactors_modEq_one {x q : ℕ} (hx : x ≠ 0)
    (h : ∀ r ∈ x.primeFactors, r ≡ 1 [MOD q]) :
    x ≡ 1 [MOD q] := by
  rw [Nat.prod_primeFactors_coe_pow_factorization hx]
  have hprod :
      (∏ r ∈ x.primeFactors, r ^ x.factorization r) ≡
        ∏ r ∈ x.primeFactors, 1 [MOD q] :=
    Nat.ModEq.prod fun r hr => by
      simpa using (h r hr).pow (x.factorization r)
  simpa using hprod

/-- The divisor-congruence part of **Peterfalvi (13.14)** when `p` is not
`1 mod q`. -/
theorem cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : ¬ p ≡ 1 [MOD q]) :
    ∀ x : ℕ, x ≠ 0 → x ∣ (p ^ q - 1) / (p - 1) → x ≡ 1 [MOD q] := by
  intro x hx hxdvd
  refine modEq_one_of_forall_primeFactors_modEq_one hx fun r hrx => ?_
  exact cyclotomic_quotient_prime_dvd_modEq_one_of_not_modEq_one hp hq hpq
    (Nat.prime_of_mem_primeFactors hrx)
    ((Nat.dvd_of_mem_primeFactors hrx).trans hxdvd)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CaseBOrder.lean =====
namespace OddOrder.Peterfalvi.S15

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.15), the non-`1 mod q` branch** (side-agnostic): in case (9.7.b), if
`p ≢ 1 (mod q)` then the complement has the *full* Singer cyclotomic order `u = (p^q − 1)/(p − 1)`.

The cofactor `x` (with `u·x = (p^q − 1)/(p − 1)`) satisfies `x ≡ 1 (mod q)` by the (13.14)
divisor-congruence `cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one` and is odd (it divides the
odd cyclotomic quotient, `cyclotomic_quotient_odd`); with `q` odd these force `x = 1` or
`x ≥ 2q + 1`,
and the latter is ruled out by `caseB_order_x_absurd_of_ge`. Hence `x = 1` and
`u = (p^q − 1)/(p − 1)`.

The `T`-side `v`-value `v = (q^p − 1)/(q − 1)` of Peterfalvi (14.4) is the instance with the roles
of
`p, q` swapped and `q ≢ 1 (mod p)` (04.16 p. 87).  The char/`σ`-theory inputs `hanalytic`, `hm5`,
`hm7`, `h11c` are supplied by the caller (they bottom out in the analytic inequality (13.10) with
`c = 1`/`d = 1`, i.e. `typeP_Galois`, issue 9000). -/
theorem caseB_order_u_full_of_not_modEq {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (hnotmod : ¬ p ≡ 1 [MOD q])
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u) (hx0 : x ≠ 0)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    u = (p ^ q - 1) / (p - 1) := by
  have hx1 : x = 1 := by
    by_contra hxne1
    -- `x ∣ (p^q-1)/(p-1)` is odd and `≡ 1 (mod q)`; with `q` odd, `x ≠ 1 ⟹ x ≥ 2q+1`.
    have hvalodd : Odd ((p ^ q - 1) / (p - 1)) := cyclotomic_quotient_odd hp hpodd hqodd
    have hxdvd : x ∣ (p ^ q - 1) / (p - 1) := ⟨u, by rw [← hux]; ring⟩
    have hxmod : x ≡ 1 [MOD q] :=
      cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one hp hq hnotmod x hx0 hxdvd
    have hxodd : Odd x := by
      rcases Nat.even_or_odd x with he | ho
      · exact absurd (even_iff_two_dvd.mpr (he.two_dvd.trans hxdvd))
          (Nat.not_even_iff_odd.mpr hvalodd)
      · exact ho
    have hx1le : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hx1le).mp hxmod.symm  -- `x - 1 = q * k`
    have hxk : x = q * k + 1 := by omega
    have hk_ne : k ≠ 0 := by
      intro h0; rw [h0, Nat.mul_zero] at hk; omega
    have hk_even : Even k := by
      rcases Nat.even_or_odd k with he | ho
      · exact he
      · exact absurd (show Even x by rw [hxk]; exact (hqodd.mul ho).add_one)
          (Nat.not_even_iff_odd.mpr hxodd)
    obtain ⟨j, hj⟩ := hk_even
    have hk2 : 2 ≤ k := by omega
    have hx_ge : 2 * q + 1 ≤ x := by
      have hqk : 2 * q ≤ q * k := by
        calc 2 * q = q * 2 := by ring
          _ ≤ q * k := by gcongr
      rw [hxk]; omega
    exact caseB_order_x_absurd_of_ge hp hq hp3 hq2 hpq hx_ge hux hu_ne_one hu_cop_q
      hm5 hm7 h11c hanalytic
  rw [hx1, mul_one] at hux
  exact hux

/-- **Peterfalvi (13.15), the `p ≡ 1 (mod q)` branch** (side-agnostic): in case (9.7.b), if
`p ≡ 1 (mod q)` then the complement order is `u = (p^q − 1)/(q(p − 1))`.

The cofactor `x` (with `u·x = (p^q − 1)/(p − 1)`) is divisible by `q`: by (13.14)
`cyclotomic_quotient_dvd_of_modEq_one`, `q ∣ (p^q − 1)/(p − 1) = u·x`, and `q ∤ u` (coprimality)
forces `q ∣ x`.  Writing `x = q·t`, oddness of `x` (it divides the odd cyclotomic quotient) forces
`t` odd; with `t ≠ 1` this gives `t ≥ 3`, i.e. `x ≥ 3q ≥ 2q + 1`, ruled out by
`caseB_order_x_absurd_of_ge`.  Hence `x = q` and `u = (p^q − 1)/(q(p − 1))`. -/
theorem caseB_order_u_div_q_of_modEq {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q) (hmod : p ≡ 1 [MOD q])
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u) (_hx0 : x ≠ 0)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    u = (p ^ q - 1) / (q * (p - 1)) := by
  have hqpos : 0 < q := hq.pos
  have hxq : x = q := by
    by_contra hxne
    have hqdvd_val : q ∣ (p ^ q - 1) / (p - 1) := cyclotomic_quotient_dvd_of_modEq_one hp hmod
    have hvalodd : Odd ((p ^ q - 1) / (p - 1)) := cyclotomic_quotient_odd hp hpodd hqodd
    have hxdvd : x ∣ (p ^ q - 1) / (p - 1) := ⟨u, by rw [← hux]; ring⟩
    have hcop : Nat.Coprime q u := hq.coprime_iff_not_dvd.mpr hu_cop_q
    have hqx : q ∣ x := hcop.dvd_of_dvd_mul_left (by rw [hux]; exact hqdvd_val)
    obtain ⟨t, ht⟩ := hqx  -- `x = q * t`
    have hxodd : Odd x := by
      rcases Nat.even_or_odd x with he | ho
      · exact absurd (even_iff_two_dvd.mpr (he.two_dvd.trans hxdvd))
          (Nat.not_even_iff_odd.mpr hvalodd)
      · exact ho
    have htodd : Odd t := by
      rcases Nat.even_or_odd t with he | ho
      · exact absurd (show Even x by rw [ht]; exact Nat.even_mul.mpr (Or.inr he))
          (Nat.not_even_iff_odd.mpr hxodd)
      · exact ho
    have ht_ne : t ≠ 1 := fun h1 => hxne (by rw [ht, h1, Nat.mul_one])
    have ht3 : 3 ≤ t := by obtain ⟨s, hs⟩ := htodd; omega
    have hx_ge : 2 * q + 1 ≤ x := by
      have h3q : 3 * q ≤ q * t := by
        calc 3 * q = q * 3 := by ring
          _ ≤ q * t := by gcongr
      rw [ht]; omega
    exact caseB_order_x_absurd_of_ge hp hq hp3 hq2 hpq hx_ge hux hu_ne_one hu_cop_q
      hm5 hm7 h11c hanalytic
  rw [hxq] at hux  -- `hux : u * q = (p^q - 1)/(p - 1)`
  have hval : u = (p ^ q - 1) / (p - 1) / q := by
    rw [← hux, Nat.mul_comm u q, Nat.mul_div_cancel_left u hqpos]
  rw [hval, Nat.div_div_eq_div_mul, Nat.mul_comm (p - 1) q]

/-- **Peterfalvi (13.15)** (side-agnostic numeric engine, assembled dichotomy): in case (9.7.b),
the complement order `u` is the Singer cyclotomic value
`u = (p^q − 1)/(p − 1)` when `p ≢ 1 (mod q)`, or `u = (p^q − 1)/(q(p − 1))` when `p ≡ 1 (mod q)`.

This packages the two branches `caseB_order_u_div_q_of_modEq` (the `p ≡ 1 (mod q)` case) and
`caseB_order_u_full_of_not_modEq` (the `p ≢ 1 (mod q)` case) into the exact conjunction shape of the
`S`-side statement `S15.caseB_order_u`: once the char/`σ`-theory inputs (`hanalytic`, the (13.11)
`m`-lower bounds, `h11c`) are supplied for the concrete `Hypothesis` data — which bottom out in the
analytic inequality (13.10) with `c = 1`/`d = 1`, i.e. `typeP_Galois`, issue 9000 — this engine
discharges `caseB_order_u` by instantiation, and the `T`-side `v`-value `v = (q^p − 1)/(q − 1)` of
(14.4) is the `p ↔ q` instance.  The engine itself is *ungated* (all char content is hypotheses). -/
theorem caseB_order_u_value {p q x u : ℕ} {m : ℚ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hpodd : Odd p) (hqodd : Odd q)
    (hux : u * x = (p ^ q - 1) / (p - 1))
    (hu_ne_one : u ≠ 1) (hu_cop_q : ¬ q ∣ u) (hx0 : x ≠ 0)
    (hm5 : 5 ≤ q → (7 : ℚ) / 10 < m) (hm7 : 7 ≤ q → (8 : ℚ) / 10 < m)
    (h11c : q = 3 → ((p : ℚ) ^ 2 - 1) / 6 < (u : ℚ))
    (hanalytic : m < (q : ℚ) * ((p : ℚ) ^ q - 1)
      / ((p : ℚ) ^ (q - 1) * (x : ℚ) * ((p : ℚ) - 1))) :
    (p ≡ 1 [MOD q] → u = (p ^ q - 1) / (q * (p - 1))) ∧
      (¬ p ≡ 1 [MOD q] → u = (p ^ q - 1) / (p - 1)) :=
  ⟨fun hmod => caseB_order_u_div_q_of_modEq hp hq hp3 hq2 hpq hpodd hqodd hmod hux
      hu_ne_one hu_cop_q hx0 hm5 hm7 h11c hanalytic,
    fun hnotmod => caseB_order_u_full_of_not_modEq hp hq hp3 hq2 hpq hpodd hqodd hnotmod hux
      hu_ne_one hu_cop_q hx0 hm5 hm7 h11c hanalytic⟩

/-- **Peterfalvi (13.15)**: if the genuine Clifford case (9.7.b) holds for `S`, then `u` has
the final Singer cyclotomic order, with the extra factor `q` precisely in the `p ≡ 1 (mod q)`
branch.

The case-(b) certificate supplies `u ∣ (p^q - 1)/(p - 1)`, hence a cofactor `x`.  The remaining
inputs of `caseB_order_u_value` are the already-proved (13.10)--(13.14) facts: `c = 1`, the lower
bounds for `m`, `u ≡ 1 (mod q)`, and the oddness of the cyclotomic quotient. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (h1310 : (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ))
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataS hG chief)) :
    (hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.q * (hyp.p - 1))) ∧
      (¬ hyp.p ≡ 1 [MOD hyp.q] →
        hyp.u = (hyp.p ^ hyp.q - 1) / (hyp.p - 1)) := by
  have hc1 := c_eq_one_of_analytic_inequality hG hyp h1310
  have hdiv := caseB.u_dvd_norm_quotient
  rw [hyp.mkSection11CharacterDataS_u_eq hG chief,
    hyp.chiefFactorS_p_eq hG chief, hyp.toTypesIIIIIIVSetupS_q_eq hG] at hdiv
  obtain ⟨x, hx⟩ := hdiv
  have hux : hyp.u * x = (hyp.p ^ hyp.q - 1) / (hyp.p - 1) := hx.symm
  have hu_ne_one : hyp.u ≠ 1 := by
    intro hu1
    have hUcard : Nat.card ↥hyp.U = 1 := by
      rw [hyp.card_U_eq_uc, hu1, hc1]
    have hUne : hyp.U ≠ ⊥ := by
      rw [← hyp.Sdata_U_eq]
      exact (hyp.toTypesIIIIIIVSetupS hG).nontrivial.1
    exact hUne (Subgroup.card_eq_one.mp hUcard)
  have hu_cop_q : ¬ hyp.q ∣ hyp.u := by
    intro hqu
    have hmod : hyp.u % hyp.q = 1 % hyp.q := hyp.u_modEq_one hG
    obtain ⟨k, hk⟩ := hqu
    have hq2 : 2 ≤ hyp.q := hyp.q_prime.two_le
    have h1q : 1 % hyp.q = 1 := Nat.one_mod_eq_one.mpr (by omega)
    rw [hk, Nat.mul_mod_right, h1q] at hmod
    omega
  have hvalodd : Odd ((hyp.p ^ hyp.q - 1) / (hyp.p - 1)) :=
    cyclotomic_quotient_odd hyp.p_prime hyp.p_odd hyp.q_odd
  have hx0 : x ≠ 0 := by
    intro hx0
    have hzero : (hyp.p ^ hyp.q - 1) / (hyp.p - 1) = 0 := by
      rw [← hux, hx0, mul_zero]
    rw [hzero] at hvalodd
    obtain ⟨k, hk⟩ := hvalodd
    omega
  have h11c : hyp.q = 3 →
      ((hyp.p : ℚ) ^ 2 - 1) / 6 < (hyp.u : ℚ) := by
    intro hq3
    have h := ((numeric_bounds_of_analytic_inequality hyp h1310).2.2 hq3).2
    rw [hc1] at h
    norm_num at h
    have hp2one : 1 ≤ hyp.p ^ 2 := Nat.one_le_pow _ _ hyp.p_prime.pos
    push_cast [Nat.cast_sub hp2one] at h
    exact h
  rw [hc1] at h1310
  norm_num at h1310
  have hp1 : 1 ≤ hyp.p := hyp.p_prime.one_le
  have hpq1 : 1 ≤ hyp.p ^ hyp.q := Nat.one_le_pow _ _ hyp.p_prime.pos
  have hpred_dvd : hyp.p - 1 ∣ hyp.p ^ hyp.q - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.p 1 hyp.q
  have hquotient_mul :
      (hyp.p ^ hyp.q - 1) / (hyp.p - 1) * (hyp.p - 1) = hyp.p ^ hyp.q - 1 :=
    Nat.div_mul_cancel hpred_dvd
  have hquotient_mulQ :
      (((hyp.p ^ hyp.q - 1) / (hyp.p - 1) : ℕ) : ℚ) * ((hyp.p : ℚ) - 1) =
        (hyp.p : ℚ) ^ hyp.q - 1 := by
    have h := congrArg (Nat.cast (R := ℚ)) hquotient_mul
    push_cast [Nat.cast_sub hp1, Nat.cast_sub hpq1] at h
    convert h using 1
  have huxQ : (hyp.u : ℚ) * (x : ℚ) =
      (((hyp.p ^ hyp.q - 1) / (hyp.p - 1) : ℕ) : ℚ) := by
    exact_mod_cast hux
  have hproduct :
      (hyp.u : ℚ) * (x : ℚ) * ((hyp.p : ℚ) - 1) =
        (hyp.p : ℚ) ^ hyp.q - 1 := by
    rw [huxQ]
    exact hquotient_mulQ
  have hqR : (0 : ℚ) < (hyp.q : ℚ) := by exact_mod_cast hyp.q_prime.pos
  have hp1R : (0 : ℚ) < (hyp.p : ℚ) - 1 := by
    have hp2R : (2 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hyp.p_prime.two_le
    linarith
  have hxR : (0 : ℚ) < (x : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hx0
  rw [div_lt_iff₀ hqR] at h1310
  have hanalytic : hyp.m < (hyp.q : ℚ) * ((hyp.p : ℚ) ^ hyp.q - 1) /
      ((hyp.p : ℚ) ^ (hyp.q - 1) * (x : ℚ) * ((hyp.p : ℚ) - 1)) := by
    have hden : (0 : ℚ) <
        (hyp.p : ℚ) ^ (hyp.q - 1) * (x : ℚ) * ((hyp.p : ℚ) - 1) := by positivity
    rw [lt_div_iff₀ hden]
    have hscale := mul_lt_mul_of_pos_right h1310 (mul_pos hxR hp1R)
    nlinarith [hproduct]
  exact caseB_order_u_value hyp.p_prime hyp.q_prime hyp.three_le_p hyp.q_ne_two hyp.p_ne_q
    hyp.p_odd hyp.q_odd hux hu_ne_one hu_cop_q hx0
    hyp.m_gt_seven_tenths_of_five_le_q hyp.m_gt_four_fifths_of_seven_le_q h11c hanalytic

end OddOrder.Peterfalvi.S15
