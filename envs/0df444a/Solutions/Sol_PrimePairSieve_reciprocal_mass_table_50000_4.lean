-- Prove2me | solution 1 for PrimePairSieve.reciprocal_mass_table_50000_4
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:21:50.496826+00:00
-- url     : https://prove2.me/submissions/7c2a275b-b895-4126-aa25-c394ab9cef9e

import Theorems.Thm_PrimePairSieve_reciprocal_mass_certificate_sound

import Mathlib.Tactic.NormNum.Prime

import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false

set_option maxRecDepth 100000

set_option maxHeartbeats 20000000


set_option autoImplicit false
open scoped BigOperators
namespace PrimePairSieve.ReciprocalBatch

def primeCheck (p : ℕ) : Bool := decide (2 ≤ p) &&
  (List.range (Nat.sqrt p + 1)).all (fun m => decide (m < 2 ∨ ¬ m ∣ p))

lemma primeCheck_spec (p : ℕ) : primeCheck p = true ↔ Nat.Prime p := by
  simp only [primeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨hp, fun m hm hms => ?_⟩
    exact (h m (by omega)).resolve_left (by omega)
  · rintro ⟨hp,h⟩
    refine ⟨hp, fun m hm => ?_⟩
    by_cases hm2 : m < 2
    · exact Or.inl hm2
    · exact Or.inr (h m (by omega) (by omega))

def fastRowCheck (r : Row) : Bool :=
  decide ((∀ p ∈ r.factors, primeCheck p = true) ∧ (∏ p ∈ r.factors, p) = r.n) &&
    decide (r.a = ∏ p ∈ r.factors, if p = 2 then 1 else 2) &&
    decide (r.b = ∏ p ∈ r.factors, if p = 2 then 1 else p-2) &&
    decide (0 < r.b ∧ 0 < r.n)

lemma fastRowCheck_eq : fastRowCheck = rowCheck := by
  funext r
  simp only [fastRowCheck, rowCheck, primeCheck_spec]

example : primeCheck 4999 = true := by decide +kernel
example : primeCheck 49 = false := by decide +kernel
example : primeCheck 1 = false := by decide +kernel
example : primeCheck 2 = true := by decide +kernel
end PrimePairSieve.ReciprocalBatch


open scoped BigOperators
set_option autoImplicit false
namespace PrimePairSieve.ReciprocalBatch

inductive PrimeTree where
  | empty
  | node (p : ℕ) (left right : PrimeTree)
  deriving DecidableEq

def PrimeTree.check : PrimeTree → Bool
  | .empty => true
  | .node p left right => primeCheck p && left.check && right.check

def PrimeTree.contains (n : ℕ) : PrimeTree → Bool
  | .empty => false
  | .node p left right => if n = p then true else
      if n < p then left.contains n else right.contains n

lemma PrimeTree.contains_prime (tree : PrimeTree) (n : ℕ)
    (hc : tree.check = true) (hn : tree.contains n = true) : Nat.Prime n := by
  induction tree with
  | empty => simp [PrimeTree.contains] at hn
  | node p left right ihl ihr =>
    simp only [PrimeTree.check, Bool.and_eq_true] at hc
    simp only [PrimeTree.contains] at hn
    split_ifs at hn with heq hlt
    · subst n
      exact (primeCheck_spec p).mp hc.1.1
    · exact ihl hc.1.2 hn
    · exact ihr hc.2 hn

def treeRowCheck (tree : PrimeTree) (r : Row) : Bool :=
  decide ((∀ p ∈ r.factors, tree.contains p = true) ∧ (∏ p ∈ r.factors, p) = r.n) &&
    decide (r.a = ∏ p ∈ r.factors, if p = 2 then 1 else 2) &&
    decide (r.b = ∏ p ∈ r.factors, if p = 2 then 1 else p-2) &&
    decide (0 < r.b ∧ 0 < r.n)

lemma treeRowCheck_sound (tree : PrimeTree) (r : Row) (ht : tree.check = true)
    (hr : treeRowCheck tree r = true) : rowCheck r = true := by
  simp only [treeRowCheck, Bool.and_eq_true, decide_eq_true_eq] at hr
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_,hr.1.1.1.2⟩,hr.1.1.2⟩,hr.1.2⟩,hr.2⟩
  intro p hp
  exact tree.contains_prime p ht (hr.1.1.1.1 p hp)

lemma treeRows_sound (tree : PrimeTree) (rows : List Row) (ht : tree.check = true)
    (hr : rows.all (treeRowCheck tree) = true) : rows.all rowCheck = true := by
  rw [List.all_eq_true] at hr ⊢
  exact fun r hmem => treeRowCheck_sound tree r ht (hr r hmem)

example : (PrimeTree.node 3 (.node 2 .empty .empty) (.node 5 .empty .empty)).check = true := by decide +kernel
example : (PrimeTree.node 9 .empty .empty).check = false := by decide +kernel
example : (PrimeTree.node 3 (.node 2 .empty .empty) (.node 5 .empty .empty)).contains 4 = false := by decide +kernel
end PrimePairSieve.ReciprocalBatch

namespace MassTable50000_4

open PrimePairSieve.ReciprocalBatch

open PrimePairSieve.ReciprocalMass

def rows_0 : List Row := [
⟨48090,16,3405,{2,3,5,7,229}⟩,
⟨48093,16,12285,{3,17,23,41}⟩,
⟨48111,16,10395,{3,7,29,79}⟩,
⟨48126,8,6765,{2,3,13,617}⟩,
⟨48138,8,7659,{2,3,71,113}⟩,
⟨48162,8,7287,{2,3,23,349}⟩,
⟨48174,16,5075,{2,3,7,31,37}⟩,
⟨48198,8,7425,{2,3,29,277}⟩,
⟨48210,8,4815,{2,3,5,1607}⟩,
⟨48230,16,8415,{2,5,7,13,53}⟩,
⟨48246,16,5535,{2,3,11,17,43}⟩,
⟨48270,8,4821,{2,3,5,1609}⟩,
⟨48282,8,6787,{2,3,13,619}⟩,
⟨48306,8,7695,{2,3,83,97}⟩,
⟨48342,8,5745,{2,3,7,1151}⟩,
⟨48345,16,7857,{3,5,11,293}⟩,
⟨48378,8,6579,{2,3,11,733}⟩,
⟨48390,8,4833,{2,3,5,1613}⟩,
⟨48399,16,11715,{3,13,17,73}⟩,
⟨48405,16,6885,{3,5,7,461}⟩,
⟨48426,8,5755,{2,3,7,1153}⟩,
⟨48462,8,7605,{2,3,41,197}⟩,
⟨48477,16,10989,{3,11,13,113}⟩,
⟨48495,16,9027,{3,5,53,61}⟩,
⟨48498,8,7695,{2,3,59,137}⟩,
⟨48507,16,12495,{3,19,23,37}⟩,
⟨48570,8,4851,{2,3,5,1619}⟩,
⟨48585,16,9009,{3,5,41,79}⟩,
⟨48594,16,4785,{2,3,7,13,89}⟩,
⟨48615,16,6915,{3,5,7,463}⟩,
⟨48630,8,4857,{2,3,5,1621}⟩,
⟨48633,16,12177,{3,13,29,43}⟩,
⟨48678,16,5015,{2,3,7,19,61}⟩,
⟨48705,16,8505,{3,5,17,191}⟩,
⟨48714,8,7371,{2,3,23,353}⟩,
⟨48741,16,9405,{3,7,11,211}⟩,
⟨48774,8,6633,{2,3,11,739}⟩,
⟨48783,16,10395,{3,7,23,101}⟩,
⟨48786,8,7695,{2,3,47,173}⟩,
⟨48790,16,8775,{2,5,7,17,41}⟩,
⟨48810,8,4875,{2,3,5,1627}⟩,
⟨48822,8,7777,{2,3,79,103}⟩,
⟨48846,8,5805,{2,3,7,1163}⟩,
⟨48858,8,7155,{2,3,17,479}⟩,
⟨48867,16,9735,{3,7,13,179}⟩,
⟨48894,8,7533,{2,3,29,281}⟩,
⟨48909,16,10125,{3,7,17,137}⟩,
⟨48918,8,7569,{2,3,31,263}⟩,
⟨48930,16,3465,{2,3,5,7,233}⟩,
⟨48945,16,8217,{3,5,13,251}⟩,
⟨48954,8,7683,{2,3,41,199}⟩,
⟨48990,16,4347,{2,3,5,23,71}⟩,
⟨49035,16,6975,{3,5,7,467}⟩,
⟨49038,8,6669,{2,3,11,743}⟩
]

def rows_1 : List Row := [
⟨49062,16,5775,{2,3,13,17,37}⟩,
⟨49110,8,4905,{2,3,5,1637}⟩,
⟨49134,8,7293,{2,3,19,431}⟩,
⟨49155,16,8991,{3,5,29,113}⟩,
⟨49170,16,3969,{2,3,5,11,149}⟩,
⟨49182,8,5845,{2,3,7,1171}⟩,
⟨49206,8,7809,{2,3,59,139}⟩,
⟨49210,16,8925,{2,5,7,19,37}⟩,
⟨49215,16,8595,{3,5,17,193}⟩,
⟨49218,8,6919,{2,3,13,631}⟩,
⟨49242,8,7587,{2,3,29,283}⟩,
⟨49278,8,7749,{2,3,43,191}⟩,
⟨49290,16,4437,{2,3,5,31,53}⟩,
⟨49305,16,8721,{3,5,19,173}⟩,
⟨49335,32,6237,{3,5,11,13,23}⟩,
⟨49362,8,7327,{2,3,19,433}⟩,
⟨49395,16,9135,{3,5,37,89}⟩,
⟨49413,16,9845,{3,7,13,181}⟩,
⟨49434,16,4725,{2,3,7,11,107}⟩,
⟨49470,16,4275,{2,3,5,17,97}⟩,
⟨49494,8,7881,{2,3,73,113}⟩,
⟨49506,8,7735,{2,3,37,223}⟩,
⟨49530,16,4125,{2,3,5,13,127}⟩,
⟨49533,16,11781,{3,11,19,79}⟩,
⟨49542,8,7497,{2,3,23,359}⟩,
⟨49566,8,6741,{2,3,11,751}⟩,
⟨49569,16,12441,{3,13,31,41}⟩,
⟨49602,8,5895,{2,3,7,1181}⟩,
⟨49623,16,10275,{3,7,17,139}⟩,
⟨49647,16,12155,{3,13,19,67}⟩,
⟨49665,32,5535,{3,5,7,11,43}⟩,
⟨49674,8,7275,{2,3,17,487}⟩,
⟨49710,8,4965,{2,3,5,1657}⟩,
⟨49742,16,11475,{2,7,11,17,19}⟩,
⟨49749,16,10605,{3,7,23,103}⟩,
⟨49755,16,9135,{3,5,31,107}⟩,
⟨49794,8,7831,{2,3,43,193}⟩,
⟨49830,16,4023,{2,3,5,11,151}⟩,
⟨49854,8,5925,{2,3,7,1187}⟩,
⟨49890,8,4983,{2,3,5,1663}⟩,
⟨49910,16,9135,{2,5,7,23,31}⟩,
⟨49926,8,7905,{2,3,53,157}⟩,
⟨49929,16,11745,{3,11,17,89}⟩,
⟨49938,16,5265,{2,3,7,29,41}⟩,
⟨49962,8,6795,{2,3,11,757}⟩,
⟨49998,8,7029,{2,3,13,641}⟩
]

def certs : List (Bucket × List Row) := [
(⟨48087,49048,9420644⟩,rows_0),
(⟨49049,50000,8840669⟩,rows_1)
]

def primes : PrimeTree := (.node 223 (.node 79 (.node 31 (.node 13 (.node 5 (.node 3 (.node 2 .empty .empty) .empty) (.node 11 (.node 7 .empty .empty) .empty)) (.node 23 (.node 19 (.node 17 .empty .empty) .empty) (.node 29 .empty .empty))) (.node 59 (.node 43 (.node 41 (.node 37 .empty .empty) .empty) (.node 53 (.node 47 .empty .empty) .empty)) (.node 71 (.node 67 (.node 61 .empty .empty) .empty) (.node 73 .empty .empty)))) (.node 149 (.node 107 (.node 97 (.node 89 (.node 83 .empty .empty) .empty) (.node 103 (.node 101 .empty .empty) .empty)) (.node 137 (.node 127 (.node 113 .empty .empty) .empty) (.node 139 .empty .empty))) (.node 191 (.node 173 (.node 157 (.node 151 .empty .empty) .empty) (.node 181 (.node 179 .empty .empty) .empty)) (.node 199 (.node 197 (.node 193 .empty .empty) .empty) (.node 211 .empty .empty))))) (.node 641 (.node 359 (.node 281 (.node 251 (.node 233 (.node 229 .empty .empty) .empty) (.node 277 (.node 263 .empty .empty) .empty)) (.node 349 (.node 293 (.node 283 .empty .empty) .empty) (.node 353 .empty .empty))) (.node 479 (.node 461 (.node 433 (.node 431 .empty .empty) .empty) (.node 467 (.node 463 .empty .empty) .empty)) (.node 619 (.node 617 (.node 487 .empty .empty) .empty) (.node 631 .empty .empty)))) (.node 1187 (.node 1151 (.node 743 (.node 739 (.node 733 .empty .empty) .empty) (.node 757 (.node 751 .empty .empty) .empty)) (.node 1171 (.node 1163 (.node 1153 .empty .empty) .empty) (.node 1181 .empty .empty))) (.node 1621 (.node 1613 (.node 1609 (.node 1607 .empty .empty) .empty) (.node 1619 .empty .empty)) (.node 1657 (.node 1637 (.node 1627 .empty .empty) .empty) (.node 1663 .empty .empty))))))

lemma primes_valid : primes.check = true := by
  simp only [primes, PrimeTree.check, Bool.and_eq_true, primeCheck_spec]
  norm_num

lemma rows_valid : (certs.flatMap Prod.snd).all rowCheck = true :=
  treeRows_sound primes (certs.flatMap Prod.snd) primes_valid (by decide +kernel)

lemma checks_valid : certs.all (massCheck 100000000) = true := by decide +kernel

end MassTable50000_4

theorem solution :
    PrimePairSieve.ReciprocalMass.Valid 100000000 {⟨48087,49048,9420644⟩,
⟨49049,50000,8840669⟩} := by
  have ht : (MassTable50000_4.certs.map Prod.fst).toFinset =
      ({⟨48087,49048,9420644⟩,
⟨49049,50000,8840669⟩} : Finset PrimePairSieve.ReciprocalMass.Bucket) := by decide +kernel
  rw [← ht]
  exact PrimePairSieve.reciprocal_mass_certificate_sound 100000000 (by norm_num)
    MassTable50000_4.certs MassTable50000_4.rows_valid MassTable50000_4.checks_valid
#print axioms solution
