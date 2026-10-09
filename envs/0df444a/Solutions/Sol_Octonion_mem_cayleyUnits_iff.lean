-- Prove2me | solution 1 for Octonion.mem_cayleyUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @jawneeboy
-- created : 2026-09-23T13:30:34.637999+00:00
-- url     : https://prove2.me/submissions/def40ef2-90d7-47ac-8c9b-34b6d572c052

import Definitions.Def_Octonion_IsCayleyUnit
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

open BigOperators

namespace Octonion

private theorem signedRep_isCayley {m : ℕ} (hm : m ∈ cayleyMasks) (t : ℕ) :
    isCayley (signedRep m t) := by
  refine ⟨_, rfl, Finset.mem_image.mpr ⟨m, hm, ?_⟩⟩
  funext i
  cases hm' : Nat.testBit m i.val <;> cases ht : Nat.testBit t i.val <;>
    simp [patOfMask, hm', ht]

private theorem signedRep_normSq {m : ℕ} (hm : m ∈ weight4Masks) (t : ℕ) :
    normSq (signedRep m t) = 1 := by
  rw [signedRep, normSq_halfOf]
  have hs (i : Fin 8) :
      (((if Nat.testBit m i.val then if Nat.testBit t i.val then 1 else -1 else 0 : ℤ) : ℚ))^2 =
        if Nat.testBit m i.val then 1 else 0 := by
    cases hm' : Nat.testBit m i.val <;> cases ht : Nat.testBit t i.val <;> norm_num
  simp_rw [hs]
  rw [Finset.sum_boole, (Finset.mem_filter.mp hm).2]
  norm_num

/-- Everything enumerated in `cayleyUnits` is a Cayley integer of norm one.
The signed half-vectors are handled uniformly by their parity and weight;
only the sixteen signed basis vectors require a small kernel computation. -/
theorem cayleyUnits_isCayley_normSq_one : ∀ u ∈ cayleyUnits, isCayley u ∧ normSq u = 1 := by
  have hb : ∀ k : Fin 8, ∀ u ∈ ({basisVec k, -basisVec k} : Finset (octonions ℚ)),
      decMem u = true ∧ normSq u = 1 := by
    decide +kernel
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hu
    exact ⟨isCayley_of_decMem (hb k u hk).1, (hb k u hk).2⟩
  · obtain ⟨m, hm, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨signedRep_isCayley (Finset.mem_filter.mp hm).1 t, signedRep_normSq hm t⟩

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

/-- Converse of `cayleyUnits_isCayley_normSq_one`, proved structurally. From
`normSq_halfOf`, `normSq x = 1` turns the doubled coordinate vector `a : Fin 8 → ℤ` into an
integer solution of `∑ a_i^2 = 4`. The parity code of `isCayley` has weight 0, 4 or 8
(`cayleyCode_card`). Weight 0: all coordinates are even, so `b_i = a_i / 2` satisfies
`∑ b_i^2 = 1`, forcing `x = ±basisVec k`. Weight 4: the four odd coordinates carry squares
summing to 4, hence are `±1` and the even ones vanish, so `x = signedRep m t` for a suitable
sign mask `t < 256` (bit extraction via `testBit_pow2_filter`). Weight 8 is impossible. -/
theorem mem_cayleyUnits_of_isCayley_normSq_one {x : octonions ℚ}
    (hx : isCayley x) (h1 : normSq x = 1) : x ∈ cayleyUnits := by
  obtain ⟨a, rfl, pa⟩ := hx
  rw [normSq_halfOf] at h1
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
    have hxk : halfOf a = basisVec k ∨ halfOf a = -basisVec k := by
      cases hbk with
      | inl hbk =>
        refine .inl (ext_coord8 fun i => ?_)
        rw [coord8_halfOf, hb, coord8_basisVec, hbf i]
        by_cases h : i = k
        · rw [if_pos h, if_pos h.symm, hbk]
          norm_num
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
          norm_num
      | inr hbk =>
        refine .inr (ext_coord8 fun i => ?_)
        rw [coord8_halfOf, coord8_neg, hb, coord8_basisVec, hbf i]
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
    have heq : halfOf a = signedRep m t := by
      refine ext_coord8 fun i => ?_
      have h1' : coord8 (signedRep m t) i =
          ((if Nat.testBit m i.val then if Nat.testBit t i.val then 1 else -1 else 0 : ℤ) : ℚ) / 2 := by
        show coord8 (halfOf _) i = _
        rw [coord8_halfOf]
      rw [coord8_halfOf, h1']
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
    show m ∈ weight4Masks
    have hfeq : (Finset.univ : Finset (Fin 8)).filter (fun i => Nat.testBit m i.val) = O := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, O]
      have e := congr_fun ham i
      simp only [patOfMask] at e
      exact ⟨fun h => by rw [← e]; exact h, fun h => by rw [e]; exact h⟩
    have hwf : ((Finset.univ : Finset (Fin 8)).filter fun i => Nat.testBit m i.val).card = 4 := by
      rw [hfeq]
      exact h4
    rw [weight4Masks]
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

end Octonion

open BigOperators Quaternion

namespace Octonion

/-- Every extended Hamming codeword has weight `0 mod 4`: the sum of its indicator values is
divisible by `4`. Closed by `decide +kernel` over the sixteen codewords. -/
private theorem code_sum_mod4 : ∀ u ∈ cayleyCode,
    (∑ i : Fin 8, if u i then (1 : ℤ) else 0) % 4 = 0 := by
  decide +kernel

/-- The norm of a Cayley integer is an integer: writing `(a i)² = 4·eᵢ + [odd]`, the square sum
is `4 · Σ eᵢ + wt(code)`, and the codeword weight vanishes mod `4`. -/
theorem normSq_int {x : octonions ℚ} (hx : isCayley x) : ∃ n : ℤ, normSq x = n := by
  obtain ⟨a, rfl, pa⟩ := hx
  rw [normSq_halfOf]
  have hcode : 4 ∣ ∑ i : Fin 8, if decide (Odd (a i)) then (1 : ℤ) else 0 := by
    have h := code_sum_mod4 (fun i => decide (Odd (a i))) pa
    exact Int.dvd_of_emod_eq_zero h
  have hsq : ∀ i : Fin 8, ∃ t : ℤ, (a i)^2 = 4 * t + if decide (Odd (a i)) then 1 else 0 := by
    intro i
    rcases Int.even_or_odd (a i) with ⟨t, ht⟩ | ⟨t, ht⟩
    · refine ⟨t^2, ?_⟩
      have hnot : ¬ Odd (a i) := fun ho => by
        have hodd := Int.odd_iff.mp ho
        rw [ht] at hodd
        omega
      rw [if_neg (by simpa using hnot), ht]
      ring
    · refine ⟨t^2 + t, ?_⟩
      rw [if_pos (decide_eq_true (show Odd (a i) from ⟨t, ht⟩)), ht]
      ring
  choose e he using hsq
  obtain ⟨k, hk⟩ := hcode
  have hsumz : ∑ i : Fin 8, (a i)^2 = 4 * (∑ i : Fin 8, e i + k) := by
    rw [Finset.sum_congr rfl fun i _ => he i, Finset.sum_add_distrib, ← Finset.mul_sum, hk]
    ring
  refine ⟨∑ i : Fin 8, e i + k, ?_⟩
  have hq : (∑ i : Fin 8, ((a i : ℚ))^2) = ((4 * (∑ i : Fin 8, e i + k) : ℤ) : ℚ) := by
    exact_mod_cast hsumz
  rw [hq]
  push_cast
  ring

end Octonion

open Quaternion

namespace Octonion
variable {R : Type*} [CommRing R]

/-- The norm is multiplicative (the Hurwitz property): `N (x * y) = N x * N y`.
Proved over any commutative base ring by expanding both sides into eight coordinates
and closing with `ring`. This statement does not assert a division structure. -/
theorem normSq_mul (x y : octonions R) : normSq (x * y) = normSq x * normSq y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  show Quaternion.normSq (((⟨a, b⟩ : octonions R) * ⟨c, d⟩).fst) +
      Quaternion.normSq (((⟨a, b⟩ : octonions R) * ⟨c, d⟩).snd) =
    (Quaternion.normSq a + Quaternion.normSq b) * (Quaternion.normSq c + Quaternion.normSq d)
  simp only [fst_mul, snd_mul, normSq_def', re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
    imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul,
    re_star, imI_star, imJ_star, imK_star]
  ring

end Octonion

namespace Octonion

/-- The norm of one is one. -/
@[simp]
theorem normSq_one : normSq (1 : octonions ℚ) = 1 := by simp [normSq]

end Octonion

open Quaternion

namespace Octonion

/-- `x · x̄ = N x`: the product with the conjugate is the real octonion of the norm. Expanded
coordinate by coordinate over `ℚ` (the `ext_coord8`/`fin_cases` pattern of `inGraves_mul`). -/
theorem mul_conj (x : octonions ℚ) : x * conj x = ⟨⟨normSq x, 0, 0, 0⟩, 0⟩ := by
  obtain ⟨a, b⟩ := x
  refine ext_coord8 fun i => ?_
  fin_cases i
  all_goals
    simp only [coord8, fst_mul, snd_mul, conj, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
      imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul, re_star, imI_star, imJ_star, imK_star,
      re_neg, imI_neg, imJ_neg, imK_neg, normSq, Quaternion.normSq_def']
    simp
    try ring

end Octonion

open Quaternion

namespace Octonion

/-- `x̄ · x = N x`: the conjugate-side companion of `mul_conj`, needed because the octonion
product is not commutative (nor associative). Same coordinate expansion. -/
theorem conj_mul (x : octonions ℚ) : conj x * x = ⟨⟨normSq x, 0, 0, 0⟩, 0⟩ := by
  obtain ⟨a, b⟩ := x
  refine ext_coord8 fun i => ?_
  fin_cases i
  all_goals
    simp only [coord8, fst_mul, snd_mul, conj, re_add, imI_add, imJ_add, imK_add, re_sub, imI_sub,
      imJ_sub, imK_sub, re_mul, imI_mul, imJ_mul, imK_mul, re_star, imI_star, imJ_star, imK_star,
      re_neg, imI_neg, imJ_neg, imK_neg, normSq, Quaternion.normSq_def']
    simp
    try ring

end Octonion

namespace Octonion

/-- Membership in the Cayley integers is exactly the lattice condition `isCayley`: all eight
coordinates lie in `½ℤ` and the parity pattern of the doubled coordinates is a Hamming codeword.
As a `simp` lemma this insulates users from the subring's set representation. -/
@[simp]
theorem mem_cayleyIntegers (x : octonions ℚ) :
    x ∈ cayleyIntegers ↔ isCayley x :=
  Iff.rfl

end Octonion

open Quaternion

namespace Octonion

/-- The Cayley integers are closed under octonion conjugation: `star` negates the imaginary
coordinates, and negation preserves parity, so the doubled coordinate vector keeps its Hamming
pattern. -/
theorem star_mem_cayleyIntegers {x : octonions ℚ} (hx : x ∈ cayleyIntegers) :
    star x ∈ cayleyIntegers := by
  rw [mem_cayleyIntegers] at hx ⊢
  obtain ⟨a, rfl, pa⟩ := hx
  refine ⟨fun i => if i = 0 then a i else -a i, ?_, ?_⟩
  · apply ext_coord8
    intro i
    have hst : star (halfOf a) = conj (halfOf a) := rfl
    rw [hst, coord8_conj]
    by_cases h : i = 0
    · simp [h, coord8_halfOf]
    · simp only [if_neg h, coord8_halfOf]
      push_cast
      ring
  · obtain ⟨m, hm, ham⟩ := Finset.mem_image.mp pa
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    have key : (fun i => decide (Odd (if i = 0 then a i else -a i))) =
        fun i => decide (Odd (a i)) := by
      funext i
      by_cases hi : i = 0 <;> by_cases h : Odd (a i) <;> simp [hi, h]
    rw [key, ← ham]

end Octonion

open Quaternion

namespace Octonion

/-- The real unit octonion written as a coordinate literal. -/
private theorem one_coord8_zero : (⟨⟨(1 : ℚ), 0, 0, 0⟩, 0⟩ : octonions ℚ) = 1 := by
  apply ext_coord8
  intro i
  fin_cases i <;> simp [coord8, fst_one, snd_one]

/-- The unit criterion: a Cayley integer is invertible inside the order iff its norm is one.
Forward: multiplicativity makes the norms of `x` and its inverse integral factors of `1`, and
nonnegativity (a sum of squares) leaves only `1`. Backward: `mul_conj`/`conj_mul` exhibit
`conj x`, a Cayley integer, as the two-sided inverse at norm one. -/
theorem isCayleyUnit_iff_normSq {x : octonions ℚ} (hx : isCayley x) :
    IsCayleyUnit x ↔ normSq x = 1 := by
  constructor
  · rintro ⟨_, y, hy, hxy, _⟩
    obtain ⟨p, hp⟩ := normSq_int hx
    obtain ⟨q, hq⟩ := normSq_int hy
    have hprod : (p : ℚ) * q = 1 := by rw [← hp, ← hq, ← normSq_mul, hxy, normSq_one]
    have hx0 : (0 : ℚ) ≤ normSq x := by
      obtain ⟨a, rfl, _⟩ := hx
      rw [normSq_halfOf]
      refine div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)
    have hy0 : (0 : ℚ) ≤ normSq y := by
      obtain ⟨a, rfl, _⟩ := hy
      rw [normSq_halfOf]
      refine div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (by norm_num)
    -- integral nonnegative factors of `1` in `ℚ`: `(p-1)(q-1) ≥ 0` expands to `p + q ≤ 2`
    have hp1 : (1 : ℚ) ≤ p := by
      have hz : (0 : ℤ) ≤ p := by exact_mod_cast hx0.trans_eq hp
      have hne : p ≠ 0 := by
        intro hc
        subst hc
        simp at hprod
      have hge : (1 : ℤ) ≤ p := by omega
      exact_mod_cast hge
    have hq1 : (1 : ℚ) ≤ q := by
      have hz : (0 : ℤ) ≤ q := by exact_mod_cast hy0.trans_eq hq
      have hge : (1 : ℤ) ≤ q := by
        by_contra hc
        have hle : q ≤ 0 := by omega
        have : (p : ℚ) * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by exact_mod_cast hle)
        linarith
      exact_mod_cast hge
    have hkey : ((p : ℚ) - 1) * (q - 1) = (p : ℚ) * q - p - q + 1 := by ring
    have hge0 : (0 : ℚ) ≤ ((p : ℚ) - 1) * (q - 1) :=
      mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1)
    rw [hkey, hprod] at hge0
    have hpeq : (p : ℚ) = 1 := by linarith
    rw [hp]
    exact hpeq
  · intro h1
    refine ⟨hx, conj x, star_mem_cayleyIntegers hx, ?_, ?_⟩
    · have e := mul_conj x
      rw [h1] at e
      exact e.trans one_coord8_zero
    · have e := conj_mul x
      rw [h1] at e
      exact e.trans one_coord8_zero

end Octonion

namespace Octonion

end Octonion

open Octonion

/-- The classification of Cayley units: the enumerated `Finset` is exactly the set of invertible
Cayley integers. Forward: every listed element has squared norm one
and `mul_conj` inverts it. Backward: an invertible Cayley integer has norm one, and the
structural analysis of `Σ aᵢ² = 4` puts it on the list. -/
theorem solution {x : octonions ℚ} : x ∈ Octonion.cayleyUnits ↔ Octonion.IsCayleyUnit x := by
  constructor
  · intro hxu
    obtain ⟨hc, h1⟩ := Octonion.cayleyUnits_isCayley_normSq_one x hxu
    exact (Octonion.isCayleyUnit_iff_normSq hc).mpr h1
  · intro hu
    have hnorm : Octonion.normSq x = 1 := (Octonion.isCayleyUnit_iff_normSq hu.1).mp hu
    exact Octonion.mem_cayleyUnits_of_isCayley_normSq_one hu.1 hnorm

namespace Octonion


end Octonion
