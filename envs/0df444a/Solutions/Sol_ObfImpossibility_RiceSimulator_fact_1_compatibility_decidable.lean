-- Prove2me | solution 1 for ObfImpossibility.RiceSimulator.fact_1_compatibility_decidable
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T11:10:31.573804+00:00
-- url     : https://prove2.me/submissions/51a093d7-3b75-4a22-b730-59159ee6d9ec

import Mathlib
import Definitions.Def_ObfImpossibility_RiceSimulator_Setting

open FriedbergMuchnik
namespace RiceUniform

/-- A single oracle program realizes a family of total functions, uniformly in the oracle. -/
def Realizes (f : (ℕ → ℕ) → ℕ → ℕ) : Prop :=
  ∃ c : Program, ∀ O x, oracleEval (PFun.lift O) c x = Part.some (f O x)

/-- Ordinary partial recursive programs embed uniformly into this oracle language. -/
lemma pure_partial {f : ℕ →. ℕ} (h : Nat.Partrec f) :
    ∃ c : Program, ∀ O : ℕ →. ℕ, oracleEval O c = f := by
  induction h with
  | zero =>
    refine ⟨.mu .right, ?_⟩
    intro O
    funext n
    apply Part.eq_some_iff.mpr
    simp only [oracleEval, Nat.unpair_pair]
    apply Nat.mem_rfind.mpr
    exact ⟨by simp, fun hm => (Nat.not_lt_zero _ hm).elim⟩
  | succ => exact ⟨.succ, fun _ => rfl⟩
  | left => exact ⟨.left, fun _ => rfl⟩
  | right => exact ⟨.right, fun _ => rfl⟩
  | pair hf hg ihf ihg =>
    obtain ⟨cf, hf⟩ := ihf
    obtain ⟨cg, hg⟩ := ihg
    exact ⟨.pair cf cg, fun O => by simp only [oracleEval, hf O, hg O]; rfl⟩
  | comp hf hg ihf ihg =>
    obtain ⟨cf, hf⟩ := ihf
    obtain ⟨cg, hg⟩ := ihg
    exact ⟨.comp cf cg, fun O => by simp only [oracleEval, hf O, hg O]; rfl⟩
  | prec hf hg ihf ihg =>
    obtain ⟨cf, hf⟩ := ihf
    obtain ⟨cg, hg⟩ := ihg
    exact ⟨.prec cf cg, fun O => by simp only [oracleEval, hf O, hg O]; rfl⟩
  | rfind hf ihf =>
    obtain ⟨cf, hf⟩ := ihf
    exact ⟨.mu cf, fun O => by simp only [oracleEval, hf O]; rfl⟩

lemma pure {f : ℕ → ℕ} (h : Computable f) : Realizes (fun _ => f) := by
  obtain ⟨c, hc⟩ := pure_partial (Partrec.nat_iff.mp h.partrec)
  exact ⟨c, fun O x => congrFun (hc (PFun.lift O)) x⟩

lemma query : Realizes (fun O => O) := ⟨.query, fun _ _ => rfl⟩

lemma comp {f g : (ℕ → ℕ) → ℕ → ℕ} (hf : Realizes f) (hg : Realizes g) :
    Realizes (fun O x => f O (g O x)) := by
  obtain ⟨cf, hf⟩ := hf
  obtain ⟨cg, hg⟩ := hg
  refine ⟨.comp cf cg, ?_⟩
  intro O x
  change Part.bind (oracleEval (PFun.lift O) cg x) (fun z => oracleEval (PFun.lift O) cf z) = _
  rw [hg, Part.bind_some]
  exact hf O _

lemma pair {f g : (ℕ → ℕ) → ℕ → ℕ} (hf : Realizes f) (hg : Realizes g) :
    Realizes (fun O x => Nat.pair (f O x) (g O x)) := by
  obtain ⟨cf, hf⟩ := hf
  obtain ⟨cg, hg⟩ := hg
  exact ⟨.pair cf cg, fun O x => by simp [oracleEval, hf, hg, Seq.seq]⟩

lemma prec {f g : (ℕ → ℕ) → ℕ → ℕ} (hf : Realizes f) (hg : Realizes g) :
    Realizes (fun O p => p.unpair.2.rec (f O p.unpair.1)
      (fun k z => g O (Nat.pair p.unpair.1 (Nat.pair k z)))) := by
  obtain ⟨cf, hf⟩ := hf
  obtain ⟨cg, hg⟩ := hg
  refine ⟨.prec cf cg, ?_⟩
  intro O p
  simp only [oracleEval]
  induction p.unpair.2 with
  | zero => exact hf O _
  | succ n ih =>
    change (Part.bind _ (fun z => oracleEval (PFun.lift O) cg (Nat.pair p.unpair.1 (Nat.pair n z)))) = _
    rw [ih, Part.bind_some]
    exact hg O _

lemma congr {f g : (ℕ → ℕ) → ℕ → ℕ} (h : Realizes f) (he : ∀ O x, f O x = g O x) :
    Realizes g := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun O x => (hc O x).trans (congrArg Part.some (he O x))⟩
end RiceUniform
namespace RiceUniform

lemma pure_prim {f : ℕ → ℕ} (h : Nat.Primrec f) : Realizes (fun _ => f) :=
  pure (Primrec.nat_iff.mpr h).to_comp

lemma equality_test (q a : ℕ → ℕ) (hq : Nat.Primrec q) (ha : Nat.Primrec a) :
    Realizes (fun O p => if O (q p) = a p then 1 else 0) := by
  have hc : Primrec (fun z : ℕ => if z.unpair.1 = z.unpair.2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_iff.mpr .left) (Primrec.nat_iff.mpr .right))
      (Primrec.const 1) (Primrec.const 0)
  exact congr (comp (pure hc.to_comp) (pair (comp query (pure_prim hq)) (pure_prim ha)))
    (fun O p => by simp)

def allTests (test : ℕ → ℕ → ℕ) (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => allTests test p k * test p k

lemma bounded_tests {test : (ℕ → ℕ) → ℕ → ℕ} (ht : Realizes test)
    (b : ℕ → ℕ) (hb : Nat.Primrec b) :
    Realizes (fun O p => allTests (fun p k => test O (Nat.pair p k)) p (b p)) := by
  have hpair : Realizes (fun O z => Nat.pair z.unpair.2.unpair.2
      (test O (Nat.pair z.unpair.1 z.unpair.2.unpair.1))) :=
    pair (pure_prim (Nat.Primrec.right.comp .right))
      (comp ht (pure_prim (.pair .left (Nat.Primrec.left.comp .right))))
  have hg := comp (pure_prim Nat.Primrec.mul) hpair
  have hr := prec (pure_prim (Nat.Primrec.const 1)) hg
  have hc := comp hr (pure_prim (Nat.Primrec.pair .id hb))
  apply congr hc
  intro O p
  simp only [Nat.unpair_pair, Nat.unpaired, id_eq]
  induction b p with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.rec_add_one, allTests]
    rw [ih]

lemma allTests_eq (q a : ℕ → ℕ) (O : ℕ → ℕ) (p k : ℕ) :
    allTests (fun p j => if O (q (Nat.pair p j)) = a (Nat.pair p j) then 1 else 0) p k =
      if ∀ j < k, O (q (Nat.pair p j)) = a (Nat.pair p j) then 1 else 0 := by
  induction k with
  | zero => simp [allTests]
  | succ k ih =>
    rw [allTests, ih]
    by_cases h : ∀ j < k, O (q (Nat.pair p j)) = a (Nat.pair p j)
    · by_cases he : O (q (Nat.pair p k)) = a (Nat.pair p k)
      · have hall : ∀ j < k + 1, O (q (Nat.pair p j)) = a (Nat.pair p j) := by
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact h j hj
          · exact he
        simp only [if_pos h, if_pos he, if_pos hall, mul_one]
      · have hnot : ¬ ∀ j < k + 1, O (q (Nat.pair p j)) = a (Nat.pair p j) := by
          intro hh
          exact he (hh k (Nat.lt_succ_self k))
        simp only [if_pos h, if_neg he, if_neg hnot, mul_zero]
    · have hnot : ¬ ∀ j < k + 1, O (q (Nat.pair p j)) = a (Nat.pair p j) := by
        intro hh
        exact h (fun j hj => hh j (Nat.lt_succ_of_lt hj))
      simp only [if_neg h, if_neg hnot, zero_mul]

lemma finite_query_decider (q a b : ℕ → ℕ) (hq : Nat.Primrec q)
    (ha : Nat.Primrec a) (hb : Nat.Primrec b) :
    Realizes (fun O p => if ∀ j < b p, O (q (Nat.pair p j)) = a (Nat.pair p j)
      then 1 else 0) :=
  congr (bounded_tests (equality_test q a hq ha) b hb) (fun O p => allTests_eq q a O p (b p))

#print axioms finite_query_decider
end RiceUniform
open ObfImpossibility.RiceSimulator
namespace RiceUniform

def width (p : ℕ) : ℕ := 2 ^ p.unpair.1
def queryCode (z : ℕ) : ℕ := Nat.pair (z.unpair.2 / width z.unpair.1) (z.unpair.2 % width z.unpair.1)
def answerCode (z : ℕ) : ℕ :=
  match (Denumerable.ofNat Machine z.unpair.1.unpair.2).evaln
    (queryCode z).unpair.1 (queryCode z).unpair.2 with
  | none => 0
  | some y => y + 1
def testBound (p : ℕ) : ℕ := (p.unpair.1 + 1) * width p

lemma width_prim : Nat.Primrec width :=
  (Nat.Primrec.pow.comp (.pair (.const 2) .left)).of_eq (fun p => by simp [Nat.unpaired, width])
lemma queryCode_prim : Nat.Primrec queryCode := by
  have hw := Primrec.nat_iff.mpr (width_prim.comp Nat.Primrec.left)
  have hj := Primrec.nat_iff.mpr Nat.Primrec.right
  exact .pair (Primrec.nat_iff.mp (Primrec.nat_div.comp hj hw))
    (Primrec.nat_iff.mp (Primrec.nat_mod.comp hj hw))
lemma answerCode_prim : Nat.Primrec answerCode := by
  have hq := Primrec.nat_iff.mpr queryCode_prim
  have ht := (Primrec.nat_iff.mpr Nat.Primrec.left).comp hq
  have hx := (Primrec.nat_iff.mpr Nat.Primrec.right).comp hq
  have hm := (Primrec.ofNat Machine).comp (Primrec.nat_iff.mpr (Nat.Primrec.right.comp Nat.Primrec.left))
  have hv := Nat.Partrec.Code.primrec_evaln.comp ((ht.pair hm).pair hx)
  apply Primrec.nat_iff.mp
  apply (Primrec.option_casesOn hv (Primrec.const 0) (Primrec.succ.comp Primrec.snd).to₂).of_eq
  intro z
  dsimp only
  unfold answerCode
  cases (Denumerable.ofNat Machine z.unpair.1.unpair.2).evaln
    (queryCode z).unpair.1 (queryCode z).unpair.2 <;> rfl
lemma testBound_prim : Nat.Primrec testBound :=
  (Nat.Primrec.mul.comp (.pair (Nat.Primrec.succ.comp .left) width_prim)).of_eq
    (fun p => by simp [Nat.unpaired, testBound])

lemma compatibility_code : Realizes (fun O p =>
    if ∀ j < testBound p, O (queryCode (Nat.pair p j)) = answerCode (Nat.pair p j)
    then 1 else 0) :=
  finite_query_decider queryCode answerCode testBound queryCode_prim answerCode_prim testBound_prim

lemma option_code_inj {u v : Option ℕ} :
    (match u with | none => 0 | some y => y+1) = (match v with | none => 0 | some y => y+1) ↔ u = v := by
  cases u <;> cases v <;> simp

lemma compatibility_tests (M N : Machine) (n : ℕ) :
    (∀ j < testBound (Nat.pair n (Encodable.encode N)),
      oracle M (queryCode (Nat.pair (Nat.pair n (Encodable.encode N)) j)) =
      answerCode (Nat.pair (Nat.pair n (Encodable.encode N)) j)) ↔ Compatible n N M := by
  have hw : 0 < 2 ^ n := pow_pos (by omega) n
  simp only [testBound, width, Nat.unpair_pair, queryCode, answerCode, oracle,
    Denumerable.ofNat_encode, bounded]
  constructor
  · intro h t x ht hx
    have hx' : x < 2 ^ n := Nat.size_le.mp hx
    have hj : t * 2 ^ n + x < (n + 1) * 2 ^ n := by
      calc
        t * 2 ^ n + x < t * 2 ^ n + 2 ^ n := Nat.add_lt_add_left hx' _
        _ = (t + 1) * 2 ^ n := by ring
        _ ≤ (n + 1) * 2 ^ n := Nat.mul_le_mul_right _ (Nat.add_le_add_right ht 1)
    have hd : (t * 2 ^ n + x) / 2 ^ n = t := by
      simp [Nat.add_div, Nat.mul_div_cancel, hw, Nat.div_eq_of_lt hx']
      exact Nat.mod_lt _ hw
    have hm : (t * 2 ^ n + x) % 2 ^ n = x := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hx']
    have he := h (t * 2 ^ n + x) hj
    rw [hd, hm] at he
    exact (option_code_inj.mp he).symm
  · intro h j hj
    have ht : j / 2 ^ n ≤ n := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hw).mpr hj)
    have hx : Nat.size (j % 2 ^ n) ≤ n := Nat.size_le.mpr (Nat.mod_lt _ hw)
    exact option_code_inj.mpr (h _ _ ht hx).symm

 theorem _root_.solution :
    ∃ C : FriedbergMuchnik.Program, ∀ (M N : Machine) (n : ℕ),
      (Compatible n N M → simRun C M (Nat.pair n (Encodable.encode N)) = Part.some 1) ∧
      (¬ Compatible n N M → simRun C M (Nat.pair n (Encodable.encode N)) = Part.some 0) := by
  obtain ⟨C, hC⟩ := compatibility_code
  refine ⟨C, ?_⟩
  intro M N n
  have hc := hC (oracle M) (Nat.pair n (Encodable.encode N))
  dsimp only at hc
  constructor
  · intro h
    have hp := (compatibility_tests M N n).mpr h
    simpa only [simRun, if_pos hp] using hc
  · intro h
    have hn := fun hh => h ((compatibility_tests M N n).mp hh)
    simpa only [simRun, if_neg hn] using hc
#print axioms solution
end RiceUniform
