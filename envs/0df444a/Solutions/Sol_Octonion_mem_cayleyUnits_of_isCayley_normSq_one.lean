-- Prove2me | solution 1 for Octonion.mem_cayleyUnits_of_isCayley_normSq_one
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:30:39.142403+00:00
-- url     : https://prove2.me/submissions/66216406-d8bd-4a19-ab85-ef4144ff96fc

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_cayleyUnits
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion BigOperators

namespace Octonion

/-- The norm of a half-vector is a quarter of the integer square sum: `N (a/2) = (Σ aᵢ²)/4`.
Proved over opaque quaternion halves (`set` + `rfl` coordinate facts): rewriting `normSq` at an
unfolded quaternion literal leaves terms not type-correct at reducible transparency. -/
theorem normSq_halfOf (a : Fin 8 → ℤ) :
    normSq (halfOf a) = (∑ i : Fin 8, ((a i : ℚ))^2) / 4 := by
  set p : ℍ[ℚ] := (halfOf a).fst
  set q : ℍ[ℚ] := (halfOf a).snd
  have hsum : normSq (halfOf a) = Quaternion.normSq p + Quaternion.normSq q := rfl
  rw [hsum, Quaternion.normSq_def', Quaternion.normSq_def']
  have e0 : p.1 = (a 0 : ℚ) / 2 := rfl
  have e1 : p.2 = (a 1 : ℚ) / 2 := rfl
  have e2 : p.3 = (a 2 : ℚ) / 2 := rfl
  have e3 : p.4 = (a 3 : ℚ) / 2 := rfl
  have e4 : q.1 = (a 4 : ℚ) / 2 := rfl
  have e5 : q.2 = (a 5 : ℚ) / 2 := rfl
  have e6 : q.3 = (a 6 : ℚ) / 2 := rfl
  have e7 : q.4 = (a 7 : ℚ) / 2 := rfl
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  rw [Fin.sum_univ_eight]
  field_simp
  ring

end Octonion

set_option maxHeartbeats 1000000
open BigOperators Quaternion

namespace Octonion

/-- Bit extraction for a sum of distinct powers of two: the `j`-th bit of
`∑_{i : s i = true} 2^i` is `s j`. Closed by `decide +kernel` over all `2^8` predicates. -/
private theorem testBit_pow2_filter (s : Fin 8 → Bool) (j : Fin 8) :
    Nat.testBit ((Finset.univ.filter fun i => decide (s i)).sum fun i => 2 ^ i.val) j.val = s j := by
  have key : ∀ t ∈ (Finset.univ : Finset (Fin 8 → Bool)),
      ∀ j ∈ (Finset.univ : Finset (Fin 8)),
        decide (Nat.testBit ((Finset.univ.filter fun i => decide (t i)).sum fun i => 2 ^ i.val)
          j.val = t j) = true := by
    decide +kernel
  exact of_decide_eq_true (key s (Finset.mem_univ _) j (Finset.mem_univ _))

private theorem cayleyCode_card : ∀ c ∈ cayleyCode,
    ((Finset.univ : Finset (Fin 8)).filter fun i => c i).card = 0 ∨
      ((Finset.univ : Finset (Fin 8)).filter fun i => c i).card = 4 ∨
        ((Finset.univ : Finset (Fin 8)).filter fun i => c i).card = 8 := by
  decide +kernel

end Octonion

open Octonion

/-- Converse of `cayleyUnits_isCayley_normSq_one`, proved structurally. From
`normSq_halfOf`, `normSq x = 1` turns the doubled coordinate vector `a : Fin 8 → ℤ` into an
integer solution of `∑ a_i^2 = 4`. The parity code of `isCayley` has weight 0, 4 or 8
(`cayleyCode_card`). Weight 0: all coordinates are even, so `b_i = a_i / 2` satisfies
`∑ b_i^2 = 1`, forcing `x = ±basisVec k`. Weight 4: the four odd coordinates carry squares
summing to 4, hence are `±1` and the even ones vanish, so `x = signedRep m t` for a suitable
sign mask `t < 256` (bit extraction via `testBit_pow2_filter`). Weight 8 is impossible. -/
theorem solution {x : octonions ℚ}
    (hx : Octonion.isCayley x) (h1 : Octonion.normSq x = 1) : x ∈ Octonion.cayleyUnits := by
  obtain ⟨a, rfl, pa⟩ := hx
  rw [Octonion.normSq_halfOf] at h1
  have hq : (∑ i : Fin 8, ((a i : ℚ))^2) = 4 := by
    field_simp at h1 ⊢
    exact h1
  have hsum4 : (∑ i : Fin 8, (a i)^2) = 4 := by exact_mod_cast hq
  obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
  set O : Finset (Fin 8) := (Finset.univ : Finset (Fin 8)).filter fun i => decide (Odd (a i))
  have memO : ∀ i, i ∈ O ↔ Odd (a i) := by
    intro i
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
  have hwt : O.card = 0 ∨ O.card = 4 ∨ O.card = 8 := by
    have hc := cayleyCode_card (fun i => decide (Odd (a i))) pa
    simpa only [] using hc
  rcases hwt with h0 | h4 | h8
  · -- pattern 0: all coordinates even; a doubled unit vector is ±2eₖ
    have heven : ∀ i, ∃ t : ℤ, a i = 2 * t := by
      intro i
      rcases Int.even_or_odd (a i) with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact ⟨t, by omega⟩
      · exfalso
        have hi : i ∈ O := (memO i).mpr ⟨t, ht⟩
        have hze : O = ∅ := Finset.card_eq_zero.mp h0
        rw [hze] at hi
        exact absurd hi (by simp)
    choose b hb using heven
    have hb1 : (∑ i : Fin 8, (b i)^2) = 1 := by
      have hmul : (∑ i : Fin 8, (b i)^2) * 4 = 4 := calc
        (∑ i : Fin 8, (b i)^2) * 4 = ∑ i : Fin 8, (b i)^2 * 4 := by rw [Finset.sum_mul]
        _ = ∑ i : Fin 8, (a i)^2 := Finset.sum_congr rfl fun i _ => by rw [hb i]; ring
        _ = 4 := hsum4
      omega
    set Z : Finset (Fin 8) := Finset.univ.filter fun i => decide (b i ≠ 0)
    have memZ : ∀ i, i ∈ Z ↔ b i ≠ 0 := by
      intro i
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩
    have hZ1 : Z.card = 1 := by
      have hge : (∑ i ∈ Z, (1 : ℤ)) ≤ ∑ i ∈ Z, (b i)^2 :=
        Finset.sum_le_sum fun i hi => by
          obtain hnz : b i ≠ 0 := (memZ i).mp hi
          have hpos : (0 : ℤ) < (b i)^2 := sq_pos_of_ne_zero hnz
          omega
      have hsumZ : ∑ i ∈ Z, (1 : ℤ) = (Z.card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hleZ : ∑ i ∈ Z, (b i)^2 ≤ 1 := calc
        _ ≤ ∑ i : Fin 8, (b i)^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => sq_nonneg _
        _ = 1 := hb1
      have hne : ∃ k : Fin 8, b k ≠ 0 := by
        by_contra h
        have hall : ∀ i : Fin 8, b i = 0 := fun i => by
          by_contra hne'
          exact h ⟨i, hne'⟩
        rw [Finset.sum_eq_zero (fun i _ => by rw [hall i]; simp)] at hb1
        omega
      obtain ⟨k, hk⟩ := hne
      have hcardpos : 1 ≤ Z.card := Finset.card_pos.mpr ⟨k, (memZ k).mpr hk⟩
      have hcast : (Z.card : ℤ) ≤ 1 := by
        rw [← hsumZ]
        exact hge.trans hleZ
      omega
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hZ1
    have hkb : b k ≠ 0 := (memZ k).mp (by rw [hk]; simp)
    have hbk : b k = 1 ∨ b k = -1 := by
      have hle : (b k)^2 ≤ 1 := calc
        _ ≤ ∑ i : Fin 8, (b i)^2 :=
          Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ k)
        _ = 1 := hb1
      have hnd : -1 ≤ b k ∧ b k ≤ 1 := by
        constructor <;> nlinarith
      rcases lt_trichotomy (b k) 0 with hlt | heq | hgt
      · exact .inr (by omega)
      · exfalso; exact hkb heq
      · exact .inl (by omega)
    have hbf : ∀ i, b i = if i = k then b k else 0 := by
      intro i
      by_cases h : i = k
      · simp [h]
      · rw [if_neg h]
        have hiZ : i ∉ Z := by
          rw [hk]
          intro hc
          exact h (Finset.mem_singleton.mp hc)
        apply not_not.mp
        intro hne
        exact hiZ ((memZ i).mpr hne)
    have hxk : Octonion.halfOf a = Octonion.basisVec k ∨ Octonion.halfOf a = -Octonion.basisVec k := by
      cases hbk with
      | inl hbk =>
        refine .inl (Octonion.ext_coord8 fun i => ?_)
        rw [Octonion.coord8_halfOf, hb, Octonion.coord8_basisVec, hbf i]
        by_cases h : i = k
        · rw [if_pos h, if_pos h.symm, hbk]
          norm_num
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
          norm_num
      | inr hbk =>
        refine .inr (Octonion.ext_coord8 fun i => ?_)
        rw [Octonion.coord8_halfOf, Octonion.coord8_neg, hb, Octonion.coord8_basisVec, hbf i]
        by_cases h : i = k
        · rw [if_pos h, if_pos h.symm, hbk]
          norm_num
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
          norm_num
    rcases hxk with e | e
    · rw [e]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩)
      simp
    · rw [e]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, ?_⟩)
      simp
  · -- pattern of weight 4: four odd coordinates ±1 and vanishing even ones
    have hO4 : ∑ i ∈ O, (a i)^2 = 4 := by
      have hge : (∑ i ∈ O, (1 : ℤ)) ≤ ∑ i ∈ O, (a i)^2 :=
        Finset.sum_le_sum fun i hi => by
          obtain ⟨s, hs⟩ := (memO i).mp hi
          have hnz : a i ≠ 0 := by omega
          have hpos : (0 : ℤ) < (a i)^2 := sq_pos_of_ne_zero hnz
          omega
      have hsumO : ∑ i ∈ O, (1 : ℤ) = (4 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
        omega
      have hle : ∑ i ∈ O, (a i)^2 ≤ 4 := calc
        _ ≤ ∑ i : Fin 8, (a i)^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => sq_nonneg _
        _ = 4 := hsum4
      omega
    have ha1 : ∀ i ∈ O, a i = 1 ∨ a i = -1 := by
      intro i hi
      obtain ⟨s, hs⟩ := (memO i).mp hi
      have hle : (a i)^2 ≤ 4 := calc
        _ ≤ ∑ j : Fin 8, (a j)^2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 4 := hsum4
      have hnd : -2 ≤ a i ∧ a i ≤ 2 := by
        constructor <;> nlinarith
      rcases lt_trichotomy (a i) 0 with hlt | heq | hgt
      · exact .inr (by omega)
      · exfalso; omega
      · exact .inl (by omega)
    have haz : ∀ i ∉ O, a i = 0 := by
      intro i hi
      have hunion : ∑ j ∈ O ∪ {i}, (a j)^2 = ∑ j ∈ O, (a j)^2 + (a i)^2 := by
        have hd : Disjoint O ({i} : Finset (Fin 8)) := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          rw [Finset.mem_singleton] at hj2
          subst hj2
          exact hi hj1
        rw [Finset.sum_union hd, Finset.sum_singleton]
      have hle : ∑ j ∈ O, (a j)^2 + (a i)^2 ≤ 4 := calc
        _ = ∑ j ∈ O ∪ {i}, (a j)^2 := hunion.symm
        _ ≤ ∑ j : Fin 8, (a j)^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
        _ = 4 := hsum4
      nlinarith
    set s : Fin 8 → Bool := fun i => Nat.testBit m i.val && decide (0 < a i)
    set t : ℕ := (Finset.univ.filter fun i => decide (s i)).sum fun i => 2 ^ i.val
    have htb : ∀ j : Fin 8, Nat.testBit t j.val = s j := fun j => testBit_pow2_filter s j
    have ht256 : t < 256 := by
      have hsub : t ≤ (Finset.univ : Finset (Fin 8)).sum (fun i => 2 ^ i.val) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => Nat.zero_le _
      have : (Finset.univ : Finset (Fin 8)).sum (fun i => 2 ^ i.val) = 255 := by decide
      omega
    have heq : Octonion.halfOf a = Octonion.signedRep m t := by
      refine Octonion.ext_coord8 fun i => ?_
      have h1' : Octonion.coord8 (Octonion.signedRep m t) i =
          ((if Nat.testBit m i.val then if Nat.testBit t i.val then 1 else -1 else 0 : ℤ) : ℚ) / 2 := by
        show Octonion.coord8 (Octonion.halfOf _) i = _
        rw [Octonion.coord8_halfOf]
      rw [Octonion.coord8_halfOf, h1']
      by_cases hiO : i ∈ O
      · obtain h | h := ha1 i hiO
        · have hbTrue : Nat.testBit m i.val = true :=
            (congr_fun ham i).trans (decide_eq_true ((memO i).mp hiO))
          have ht' : Nat.testBit t i.val = true := by
            rw [htb i]
            change (Nat.testBit m i.val && decide (0 < a i)) = true
            rw [hbTrue, h]
            decide
          rw [hbTrue, h, ht']
          norm_num
        · have hbTrue : Nat.testBit m i.val = true :=
            (congr_fun ham i).trans (decide_eq_true ((memO i).mp hiO))
          have ht' : Nat.testBit t i.val = false := by
            rw [htb i]
            change (Nat.testBit m i.val && decide (0 < a i)) = false
            rw [hbTrue, h]
            decide
          rw [hbTrue, h, ht']
          norm_num
      · have hbFalse : Nat.testBit m i.val = false := by
          have hnz : ¬ Odd (a i) := fun ho => hiO ((memO i).mpr ho)
          exact (congr_fun ham i).trans (decide_eq_false hnz)
        rw [hbFalse, haz i hiO]
        norm_num
    refine Finset.mem_union.mpr (Or.inr ?_)
    refine Finset.mem_biUnion.mpr ⟨m, ?_, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht256, heq.symm⟩⟩
    show m ∈ Octonion.weight4Masks
    have hfeq : (Finset.univ : Finset (Fin 8)).filter (fun i => Nat.testBit m i.val) = O := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, O]
      have e := congr_fun ham i
      simp only [Octonion.patOfMask] at e
      exact ⟨fun h => by rw [← e]; exact h, fun h => by rw [e]; exact h⟩
    have hwf : ((Finset.univ : Finset (Fin 8)).filter fun i => Nat.testBit m i.val).card = 4 := by
      rw [hfeq]
      exact h4
    rw [Octonion.weight4Masks]
    exact Finset.mem_filter.mpr ⟨hm, hwf⟩
  · -- pattern 255: eight odd coordinates already exceed norm one
    have hge : (8 : ℤ) ≤ ∑ i ∈ O, (a i)^2 := calc
      (8 : ℤ) = ∑ i ∈ O, (1 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
        omega
      _ ≤ _ := Finset.sum_le_sum fun i hi => by
        obtain ⟨s, hs⟩ := (memO i).mp hi
        have hnz : a i ≠ 0 := by omega
        have hpos : (0 : ℤ) < (a i)^2 := sq_pos_of_ne_zero hnz
        omega
    have hle : ∑ i ∈ O, (a i)^2 ≤ 4 := calc
      _ ≤ ∑ i : Fin 8, (a i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ => sq_nonneg _
      _ = 4 := hsum4
    omega

namespace Octonion


end Octonion
