-- Prove2me | solution 1 for ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/8d3ac42f-4eaf-502d-b174-c940c786d377

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace ValuationSubring
p2m_export "ValuationSubring" "ext nonunits mem_nonunits_iff mk ValueGroup valuation_le_one_iff valuation LiesOverPrime"
namespace MuExist
p2m_open "ValuationSubring"

open MonoidWithZeroHom

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ}

local notation "ℚb" => AlgebraicClosure ℚ

theorem val_natCast_eq_one (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) {n : ℕ} (hn : ¬ p ∣ n) :
    A.valuation (n : ℚb) = 1 := by
  have hle : A.valuation (n : ℚb) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have hp1 : A.valuation ((p : ℕ) : ℚb) < 1 := (A.mem_nonunits_iff).mp hA
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have h1 : (a : ℚb) * (p : ℚb) + (b : ℚb) * (n : ℚb) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℚb) hab
  by_contra hne
  have hlt : A.valuation (n : ℚb) < 1 := lt_of_le_of_ne hle hne
  have hmul : ∀ x y : ℚb, A.valuation x ≤ 1 → A.valuation y < 1 → A.valuation (x * y) < 1 := by
    intro x y hx hy
    rw [map_mul]
    exact lt_of_le_of_lt ((mul_le_mul_left hx _).trans_eq (one_mul _)) hy
  have ha : A.valuation ((a : ℚb) * (p : ℚb)) < 1 := hmul _ _ ((A.valuation_le_one_iff _).mpr (intCast_mem A a)) hp1
  have hb : A.valuation ((b : ℚb) * (n : ℚb)) < 1 := hmul _ _ ((A.valuation_le_one_iff _).mpr (intCast_mem A b)) hlt
  have := Valuation.map_add_lt A.valuation ha hb
  rw [h1, map_one] at this
  exact lt_irrefl _ this

theorem val_natCast_eq_pow (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) {n : ℕ} (hn : n ≠ 0) :
    ∃ e : ℕ, A.valuation (n : ℚb) = A.valuation ((p : ℕ) : ℚb) ^ e := by
  obtain ⟨e, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.one_lt.ne'
  refine ⟨e, ?_⟩
  push_cast
  rw [map_mul, map_pow, val_natCast_eq_one A hp hA hn', mul_one]

theorem val_intCast_eq_pow (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) {z : ℤ} (hz : z ≠ 0) :
    ∃ e : ℕ, A.valuation (z : ℚb) = A.valuation ((p : ℕ) : ℚb) ^ e := by
  obtain ⟨e, he⟩ := val_natCast_eq_pow A hp hA (Int.natAbs_ne_zero.mpr hz)
  refine ⟨e, ?_⟩
  rcases Int.natAbs_eq z with h | h
  · rw [h, Int.cast_natCast]; exact he
  · rw [h, Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact he

theorem val_ratCast_eq_zpow (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) {c : ℚ} (hc : c ≠ 0) :
    ∃ m : ℤ, A.valuation (c : ℚb) = A.valuation ((p : ℕ) : ℚb) ^ m := by
  have hp0 : A.valuation ((p : ℕ) : ℚb) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  obtain ⟨e₁, h₁⟩ := val_intCast_eq_pow A hp hA (Rat.num_ne_zero.mpr hc)
  obtain ⟨e₂, h₂⟩ := val_natCast_eq_pow A hp hA c.den_nz
  refine ⟨(e₁ : ℤ) - e₂, ?_⟩
  rw [Rat.cast_def, map_div₀, h₁, h₂, zpow_sub₀ hp0, zpow_natCast, zpow_natCast, div_eq_mul_inv]

theorem exists_ne_val_eq {ι : Type*} (s : Finset ι) (f : ι → ℚb) (h0 : ∑ i ∈ s, f i = 0)
    {i₀ : ι} (hi₀s : i₀ ∈ s) (hi₀ : f i₀ ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ f i ≠ 0 ∧ A.valuation (f i) = A.valuation (f j) := by
  classical
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun k => A.valuation (f k)) ⟨i₀, hi₀s⟩
  have hvi : A.valuation (f i) ≠ 0 := by
    intro h
    have := hmax i₀ hi₀s
    rw [h] at this
    exact ((Valuation.ne_zero_iff _).mpr hi₀) (le_antisymm this zero_le')
  have hfi : f i ≠ 0 := fun h => hvi (by rw [h, map_zero])
  by_contra hall
  push Not at hall
  have hlt : ∀ j ∈ s.erase i, A.valuation (f j) < A.valuation (f i) := by
    intro j hj
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    exact lt_of_le_of_ne (hmax j hjs) (fun h => hall i hi j hjs (Ne.symm hji) hfi h.symm)
  have hsum := Valuation.map_sum_lt A.valuation hvi hlt
  have herase : ∑ j ∈ s.erase i, f j = -f i := by
    have := Finset.add_sum_erase s f hi
    rw [h0] at this
    linear_combination this
  rw [herase, Valuation.map_neg] at hsum
  exact lt_irrefl _ hsum

theorem exists_pow_val_eq_zpow (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) {a : ℚb} (ha : a ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : ℤ, A.valuation a ^ N = A.valuation ((p : ℕ) : ℚb) ^ m := by
  classical
  have hp0 : A.valuation ((p : ℕ) : ℚb) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have ha0 : A.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  obtain ⟨q, hq0, hq⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic a
  rw [Polynomial.aeval_eq_sum_range] at hq
  set f : ℕ → ℚb := fun i => q.coeff i • a ^ i with hf
  have hfval : ∀ i, f i = ((q.coeff i : ℚ) : ℚb) * a ^ i := fun i => by
    rw [hf]; simp only [Algebra.smul_def, eq_ratCast]
  have hi₀s : q.natDegree ∈ Finset.range (q.natDegree + 1) := Finset.self_mem_range_succ _
  have hc0 : ((q.coeff q.natDegree : ℚ) : ℚb) ≠ 0 := by
    rw [Ne, Rat.cast_eq_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq0
  have hi₀ : f q.natDegree ≠ 0 := by
    rw [hfval]
    exact mul_ne_zero hc0 (pow_ne_zero _ ha)
  obtain ⟨i, -, j, -, hij, hfi, hv⟩ := exists_ne_val_eq A (Finset.range (q.natDegree + 1)) f hq hi₀s hi₀
  have hfj : f j ≠ 0 := by
    intro h; apply (Valuation.ne_zero_iff A.valuation).mpr hfi; rw [hv, h, map_zero]
  have hci : q.coeff i ≠ 0 := by intro h; apply hfi; rw [hfval, h]; simp
  have hcj : q.coeff j ≠ 0 := by intro h; apply hfj; rw [hfval, h]; simp
  obtain ⟨mi, hmi⟩ := val_ratCast_eq_zpow A hp hA hci
  obtain ⟨mj, hmj⟩ := val_ratCast_eq_zpow A hp hA hcj
  rw [hfval, hfval, map_mul, map_mul, map_pow, map_pow, hmi, hmj] at hv

  set vp := A.valuation ((p : ℕ) : ℚb)
  set va := A.valuation a
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, mi - mj, ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h' : va ^ i * vp ^ mi = va ^ i * (vp ^ mj * va ^ (d + 1)) := by
      rw [mul_comm, hv, show i + d + 1 = i + (d + 1) by omega, pow_add]; ac_rfl
    have h2 := mul_left_cancel₀ (pow_ne_zero i ha0) h'
    rw [show i + d + 1 - i = d + 1 by omega, zpow_sub₀ hp0, h2, mul_div_cancel_left₀ _ (zpow_ne_zero mj hp0)]
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, mj - mi, ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h' : va ^ j * vp ^ mj = va ^ j * (vp ^ mi * va ^ (d + 1)) := by
      rw [mul_comm, ← hv, show j + d + 1 = j + (d + 1) by omega, pow_add]; ac_rfl
    have h2 := mul_left_cancel₀ (pow_ne_zero j ha0) h'
    rw [show j + d + 1 - j = d + 1 by omega, zpow_sub₀ hp0, h2, mul_div_cancel_left₀ _ (zpow_ne_zero mi hp0)]

theorem mulArchimedean_valueGroup (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) :
    MulArchimedean ↥(valueGroup (.ofClass A.valuation)) := by
  classical
  have hp0 : A.valuation ((p : ℕ) : ℚb) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)

  set up : (A.ValueGroup)ˣ := Units.mk0 _ hp0 with hup
  have hupmem : up ∈ valueGroup (.ofClass A.valuation) := by
    have : (up : A.ValueGroup) ∈ Units.val '' (↑(valueGroup (.ofClass A.valuation)) : Set (A.ValueGroup)ˣ) := by
      rw [valueGroup_eq_range]
      exact ⟨⟨(p : ℚb), rfl⟩, hp0⟩
    obtain ⟨u, hu, huv⟩ := this
    rwa [← Units.ext huv]
  set gp : ↥(valueGroup (.ofClass A.valuation)) := ⟨up, hupmem⟩ with hgp

  have key : ∀ g : ↥(valueGroup (.ofClass A.valuation)), g ≠ 1 → MulArchimedeanClass.mk g = MulArchimedeanClass.mk gp := by
    intro g hg

    have hmem : ((g : (A.ValueGroup)ˣ) : A.ValueGroup) ∈ Set.range A.valuation \ {0} := by
      rw [← MonoidWithZeroHom.coe_ofClass A.valuation, ← valueGroup_eq_range]; exact ⟨g, g.2, rfl⟩
    obtain ⟨⟨a, ha⟩, h0⟩ := hmem
    have ha0 : a ≠ 0 := by
      intro h; apply h0; show ((g : (A.ValueGroup)ˣ) : A.ValueGroup) ∈ ({0} : Set A.ValueGroup)
      rw [← ha, h, map_zero]; rfl
    obtain ⟨N, hN, m, hm⟩ := exists_pow_val_eq_zpow A hp hA ha0

    have hpow : g ^ N = gp ^ m := by
      apply Subtype.ext; apply Units.ext
      simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
        hgp, hup, Units.val_mk0, ← ha]
      exact hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zpow_zero] at hpow
      exact hg ((pow_eq_one_iff_left hN.ne').mp hpow)
    rw [MulArchimedeanClass.mk_eq_mk]
    have habs : |g|ₘ ^ N = |gp|ₘ ^ m.natAbs := by
      rw [← mabs_pow, hpow, mabs_zpow, ← Int.natCast_natAbs, zpow_natCast]
    have hm1 : m.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm0
    exact ⟨⟨N, (le_self_pow (one_le_mabs gp) hm1).trans_eq habs.symm⟩,
      ⟨m.natAbs, (le_self_pow (one_le_mabs g) hN.ne').trans_eq habs⟩⟩
  apply MulArchimedeanClass.mulArchimedean_of_mk_eq_mk
  intro a ha b hb
  rw [key a ha, key b hb]

theorem exists_absoluteValue (hp : p.Prime) (hA : ((p : ℕ) : ℚb) ∈ A.nonunits) :
    ∃ μ : AbsoluteValue ℚb ℝ, IsNonarchimedean μ ∧
      μ (p : ℚb) < 1 ∧ ∀ a : ℚb, a ∈ A ↔ μ a ≤ 1 := by
  classical
  have hp0 : A.valuation ((p : ℕ) : ℚb) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hp1 : A.valuation ((p : ℕ) : ℚb) < 1 := (A.mem_nonunits_iff).mp hA
  haveI : A.valuation.IsNontrivial := ⟨⟨(p : ℚb), hp0, hp1.ne⟩⟩
  haveI : MulArchimedean (ValueGroup₀ (.ofClass A.valuation)) :=
    WithZero.mulArchimedean_iff.mpr (mulArchimedean_valueGroup A hp hA)
  obtain ⟨hR⟩ := (Valuation.nonempty_rankOne_iff_mulArchimedean (v := A.valuation)).mpr inferInstance

  set w := ValueGroup₀.restrict₀ (.ofClass A.valuation) with hw
  set φ := Valuation.RankOne.hom A.valuation with hφ
  have hφm : StrictMono φ := Valuation.RankOne.strictMono A.valuation
  have hemb : StrictMono (ValueGroup₀.embedding (f := .ofClass A.valuation)) := ValueGroup₀.embedding_strictMono
  have hwle : ∀ a b : ℚb, w a ≤ w b ↔ A.valuation a ≤ A.valuation b := by
    intro a b
    rw [← hemb.le_iff_le, ValueGroup₀.embedding_restrict₀, ValueGroup₀.embedding_restrict₀,
      MonoidWithZeroHom.coe_ofClass]
  have hwlt : ∀ a b : ℚb, w a < w b ↔ A.valuation a < A.valuation b := by
    intro a b
    rw [← hemb.lt_iff_lt, ValueGroup₀.embedding_restrict₀, ValueGroup₀.embedding_restrict₀,
      MonoidWithZeroHom.coe_ofClass]
  have hwadd : ∀ a b : ℚb, w (a + b) ≤ max (w a) (w b) := by
    intro a b
    rw [← hemb.le_iff_le, hemb.monotone.map_max, ValueGroup₀.embedding_restrict₀, ValueGroup₀.embedding_restrict₀,
      ValueGroup₀.embedding_restrict₀]
    exact A.valuation.map_add a b
  have hw1 : w 1 = 1 := map_one w

  let f : ℚb → ℝ := fun a => ((φ (w a) : NNReal) : ℝ)
  have hf : ∀ a, f a = ((φ (w a) : NNReal) : ℝ) := fun a => rfl
  have hfadd : ∀ a b, f (a + b) ≤ max (f a) (f b) := by
    intro a b
    rw [hf, hf, hf, ← NNReal.coe_max, NNReal.coe_le_coe, ← hφm.monotone.map_max]
    exact hφm.monotone (hwadd a b)
  have hf0 : ∀ a, 0 ≤ f a := fun a => NNReal.coe_nonneg _
  refine ⟨{ toFun := f
            map_mul' := fun a b => by simp only [hf, map_mul, NNReal.coe_mul]
            nonneg' := hf0
            eq_zero' := fun a => by
              rw [hf, NNReal.coe_eq_zero, Valuation.RankOne.hom_eq_zero_iff, ValueGroup₀.restrict₀_eq_zero_iff]
              exact map_eq_zero (MonoidWithZeroHom.ofClass A.valuation)
            add_le' := fun a b => (hfadd a b).trans (max_le_add_of_nonneg (hf0 a) (hf0 b)) }, hfadd, ?_, ?_⟩
  ·
    show f (p : ℚb) < 1
    rw [hf, ← NNReal.coe_one, NNReal.coe_lt_coe, ← map_one φ, hφm.lt_iff_lt, ← hw1, hwlt, map_one]
    exact hp1
  ·
    intro a
    show a ∈ A ↔ f a ≤ 1
    rw [hf, ← NNReal.coe_one, NNReal.coe_le_coe, ← map_one φ, hφm.le_iff_le, ← hw1, hwle, map_one,
      A.valuation_le_one_iff]

end ValuationSubring.MuExist

theorem solution
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ ∧
      μ (p : AlgebraicClosure ℚ) < 1 ∧ ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1 :=
  ValuationSubring.MuExist.exists_absoluteValue A hp hA

end S_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (solution)
