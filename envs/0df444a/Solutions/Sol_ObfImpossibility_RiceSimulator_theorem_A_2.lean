-- Prove2me | solution 1 for ObfImpossibility.RiceSimulator.theorem_A_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T12:09:20.99939+00:00
-- url     : https://prove2.me/submissions/f8594352-99cd-4fec-a83c-35694f11ee78

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

 theorem compatibility_decidable :
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
#print axioms compatibility_decidable
end RiceUniform

namespace ObfImpossibility.RiceSimulator

/-- Fact (3), p. A:41: if `[M] ≢ [N]` then there is `n'` such that `N` is not
`n`-compatible with `M` for all `n > n'`. -/
theorem eventually_incompatible (M N : Machine) (h : fn M ≠ fn N) :
    ∃ n' : ℕ, ∀ n : ℕ, n' < n → ¬ Compatible n N M := by
  classical
  have hx : ∃ t x : ℕ, bounded N t x ≠ bounded M t x := by
    by_contra hnone
    push_neg at hnone
    apply h
    funext x
    apply Part.ext
    intro y
    change y ∈ M.eval x ↔ y ∈ N.eval x
    rw [Nat.Partrec.Code.evaln_complete, Nat.Partrec.Code.evaln_complete]
    have heq : ∀ t, M.evaln t x = N.evaln t x := fun t => (hnone t x).symm
    simp only [heq]
  obtain ⟨t, x, hneq⟩ := hx
  refine ⟨max t (Nat.size x), ?_⟩
  intro n hn hc
  exact hneq (hc t x (le_trans (le_max_left _ _) (Nat.le_of_lt hn))
    (le_trans (le_max_right _ _) (Nat.le_of_lt hn)))


end ObfImpossibility.RiceSimulator

open ObfImpossibility.RiceSimulator
namespace ObfImpossibility.RiceSimulator
lemma finite_size_pool (s : ℕ) : {N : Machine | size N = s}.Finite := by
  have hf : {N : Machine | Encodable.encode N < 2 ^ s}.Finite :=
    Set.Finite.preimage Encodable.encode_injective.injOn (Set.finite_Iio (2 ^ s))
  apply hf.subset
  intro N hN
  change Encodable.encode N < 2 ^ s
  rw [← hN]
  exact Nat.lt_size_self _

theorem stabilization (M : Machine) :
    ∃ b : ℕ, ∀ n : ℕ, b < n → ∀ N ∈ survivors n M, fn N = fn M := by
  classical
  have he : ∀ N : Machine, ∃ b : ℕ, ∀ n : ℕ, b < n → Compatible n N M → fn N = fn M := by
    intro N
    by_cases h : fn N = fn M
    · exact ⟨0, fun _ _ _ => h⟩
    · obtain ⟨b, hb⟩ := eventually_incompatible M N (Ne.symm h)
      exact ⟨b, fun n hn hc => False.elim (hb n hn hc)⟩
  choose b hb using he
  let pool := (finite_size_pool (size M)).toFinset
  refine ⟨pool.sup b, ?_⟩
  intro n hn N hN
  have hmem : N ∈ pool := (finite_size_pool (size M)).mem_toFinset.mpr hN.1
  exact hb N n (lt_of_le_of_lt (Finset.le_sup hmem) hn) hN.2
end ObfImpossibility.RiceSimulator

namespace ObfImpossibility.RiceSimulator

theorem stage_sound (T M : Machine) (n σ : ℕ) (h : StageAnswer T M n σ) :
    σ ∈ T.eval (Encodable.encode M) := by
  apply Nat.Partrec.Code.evaln_sound
  exact h M ⟨rfl, fun _ _ _ _ => rfl⟩

lemma stage_of_common_output (T M : Machine) (σ : ℕ)
    (hT : ∀ N : Machine, fn N = fn M → σ ∈ T.eval (Encodable.encode N)) :
    ∃ n : ℕ, StageAnswer T M n σ := by
  classical
  obtain ⟨b, hb⟩ := stabilization M
  have ht : ∀ N : Machine, ∃ t : ℕ, fn N = fn M → σ ∈ T.evaln t (Encodable.encode N) := by
    intro N
    by_cases he : fn N = fn M
    · obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hT N he)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => False.elim (he h)⟩
  choose t ht using ht
  let pool := (finite_size_pool (size M)).toFinset
  let n := max (b + 1) (pool.sup t)
  have hbn : b < n := lt_of_lt_of_le (Nat.lt_succ_self b) (le_max_left _ _)
  refine ⟨n, ?_⟩
  intro N hN
  have hp : N ∈ pool := (finite_size_pool (size M)).mem_toFinset.mpr hN.1
  have he : fn N = fn M := hb n hbn N hN
  exact Nat.Partrec.Code.evaln_mono
    (le_trans (Finset.le_sup hp) (le_max_right _ _)) (ht N he)

theorem termination (P : PromiseProblem) (hclosed : P.ClosedUnderFn)
    (T : Machine) (hT : Decides T P) :
    (∀ M ∈ P.yes, ∃ n : ℕ, StageAnswer T M n 1) ∧
    (∀ M ∈ P.no, ∃ n : ℕ, StageAnswer T M n 0) := by
  constructor
  · intro M hM
    apply stage_of_common_output
    intro N he
    have hN := (hclosed M N he.symm).1.mp hM
    rw [hT.1 N hN]
    exact Part.mem_some _
  · intro M hM
    apply stage_of_common_output
    intro N he
    have hN := (hclosed M N he.symm).2.mp hM
    rw [hT.2 N hN]
    exact Part.mem_some _
end ObfImpossibility.RiceSimulator

open ObfImpossibility.RiceSimulator FriedbergMuchnik
namespace RiceUniform
set_option maxHeartbeats 400000

def sizeMatch (s j : ℕ) : Prop := j < 2 ^ s ∧ (s = 0 ∨ 2 ^ (s - 1) ≤ j)
instance (s j : ℕ) : Decidable (sizeMatch s j) := inferInstanceAs (Decidable (_ ∧ _))

lemma sizeMatch_iff (s j : ℕ) : sizeMatch s j ↔ Nat.size j = s := by
  unfold sizeMatch
  constructor
  · rintro ⟨hu, hz | hl⟩
    · have := Nat.size_le.mpr hu; omega
    · have hle := Nat.size_le.mpr hu
      by_contra hne
      have hs : Nat.size j ≤ s - 1 := by omega
      have := Nat.size_le.mp hs
      omega
  · intro h
    refine ⟨Nat.size_le.mp h.le, ?_⟩
    by_cases hz : s = 0
    · exact Or.inl hz
    · right
      by_contra hl
      have := Nat.size_le.mpr (Nat.lt_of_not_ge hl)
      omega

/-- Input encodes ((size,(stage,answer)),candidate), followed by the compatibility bit. -/
def stageGate (T : Machine) (z : ℕ) : ℕ :=
  let p := z.unpair.1.unpair.1
  let j := z.unpair.1.unpair.2
  if sizeMatch p.unpair.1 j ∧ z.unpair.2 = 1 then
    if T.evaln p.unpair.2.unpair.1 j = some p.unpair.2.unpair.2 then 1 else 0
  else 1

lemma stageGate_prim (T : Machine) : Primrec (stageGate T) := by
  have hleft : Primrec (fun z : ℕ => z.unpair.1) := Primrec.nat_iff.mpr Nat.Primrec.left
  have hright : Primrec (fun z : ℕ => z.unpair.2) := Primrec.nat_iff.mpr Nat.Primrec.right
  have hp : Primrec (fun z : ℕ => z.unpair.1.unpair.1) := hleft.comp hleft
  have hj : Primrec (fun z : ℕ => z.unpair.1.unpair.2) := hright.comp hleft
  have hs := hleft.comp hp
  have hns := hright.comp hp
  have hn := hleft.comp hns
  have ha := hright.comp hns
  have hpower : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hpow := hpower.comp (Primrec.const 2) hs
  have hlow := hpower.comp (Primrec.const 2) (Primrec.nat_sub.comp hs (Primrec.const 1))
  have hsz := (Primrec.nat_lt.comp hj hpow).and
    ((Primrec.eq.comp hs (Primrec.const 0)).or (Primrec.nat_le.comp hlow hj))
  have hg := hsz.and (Primrec.eq.comp hright (Primrec.const 1))
  have hev := Nat.Partrec.Code.primrec_evaln.comp ((hn.pair (Primrec.const T)).pair hj)
  have he := Primrec.eq.comp hev (Primrec.option_some.comp ha)
  exact Primrec.ite hg (Primrec.ite he (Primrec.const 1) (Primrec.const 0)) (Primrec.const 1)

def compatibleBit (O : ℕ → ℕ) (p : ℕ) : ℕ :=
  if ∀ j < testBound p, O (queryCode (Nat.pair p j)) = answerCode (Nat.pair p j)
  then 1 else 0

def stageTest (T : Machine) (O : ℕ → ℕ) (z : ℕ) : ℕ :=
  stageGate T (Nat.pair z (compatibleBit O (Nat.pair z.unpair.1.unpair.2.unpair.1 z.unpair.2)))

lemma stageTest_realizes (T : Machine) : Realizes (stageTest T) := by
  have hp : Nat.Primrec (fun z : ℕ => Nat.pair z.unpair.1.unpair.2.unpair.1 z.unpair.2) :=
    .pair (Nat.Primrec.left.comp (Nat.Primrec.right.comp .left)) .right
  have hc : Realizes compatibleBit := compatibility_code
  have hi : Realizes (fun _ z => Nat.pair z.unpair.1.unpair.2.unpair.1 z.unpair.2) := pure_prim hp
  have hb : Realizes (fun O z => compatibleBit O (Nat.pair z.unpair.1.unpair.2.unpair.1 z.unpair.2)) := comp hc hi
  have hz : Realizes (fun _ z => z) := pure_prim .id
  have hpair : Realizes (fun O z => Nat.pair z (compatibleBit O (Nat.pair z.unpair.1.unpair.2.unpair.1 z.unpair.2))) := pair hz hb
  have hg : Realizes (fun _ => stageGate T) := pure (stageGate_prim T).to_comp
  change Realizes (fun O z => stageGate T (Nat.pair z (compatibleBit O (Nat.pair z.unpair.1.unpair.2.unpair.1 z.unpair.2))))
  exact comp hg hpair

def stageBit (T : Machine) (O : ℕ → ℕ) (p : ℕ) : ℕ :=
  allTests (fun p j => stageTest T O (Nat.pair p j)) p (2 ^ p.unpair.1)

lemma stageBit_realizes (T : Machine) : Realizes (stageBit T) :=
  bounded_tests (stageTest_realizes T) (fun p => 2 ^ p.unpair.1)
    ((Nat.Primrec.pow.comp (.pair (.const 2) .left)).of_eq (fun p => by simp [Nat.unpaired]))

lemma stageTest_binary (T : Machine) (O : ℕ → ℕ) (z : ℕ) :
    stageTest T O z = 0 ∨ stageTest T O z = 1 := by
  simp only [stageTest, stageGate]
  split <;> (try split) <;> simp

lemma allTests_one {test : ℕ → ℕ → ℕ} (p k : ℕ) :
    allTests test p k = 1 ↔ ∀ j < k, test p j = 1 := by
  induction k with
  | zero => simp [allTests]
  | succ k ih =>
    have hm (a b : ℕ) : a * b = 1 ↔ a = 1 ∧ b = 1 := by
      constructor
      · intro h
        exact ⟨Nat.eq_one_of_mul_eq_one_right h, Nat.eq_one_of_mul_eq_one_left h⟩
      · rintro ⟨rfl, rfl⟩; rfl
    rw [allTests, hm, ih]
    constructor
    · rintro ⟨h, hk⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h j hj
      · exact hk
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self _)⟩

lemma stageBit_correct (T M : Machine) (n σ : ℕ) :
    stageBit T (oracle M) (Nat.pair (size M) (Nat.pair n σ)) = 1 ↔ StageAnswer T M n σ := by
  rw [stageBit, allTests_one]
  simp only [Nat.unpair_pair]
  constructor
  · intro h N hN
    have hj : Encodable.encode N < 2 ^ size M := Nat.size_le.mp hN.1.le
    have hh := h (Encodable.encode N) hj
    have hsize := (sizeMatch_iff (size M) (Encodable.encode N)).mpr hN.1
    have hc := (compatibility_tests M N n).mpr hN.2
    have hcbit : compatibleBit (oracle M) (Nat.pair n (Encodable.encode N)) = 1 := if_pos hc
    simpa only [stageTest, stageGate, Nat.unpair_pair, hsize, hcbit, and_self, if_true, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not] using hh
  · intro h j hj
    let N := Denumerable.ofNat Machine j
    have he : Encodable.encode N = j := Denumerable.encode_ofNat _
    by_cases hs : sizeMatch (size M) j
    · have hn : size N = size M := by simpa [size, he] using (sizeMatch_iff _ _).mp hs
      by_cases hc : Compatible n N M
      · have hh := h N ⟨hn, hc⟩
        have htests := (compatibility_tests M N n).mpr hc
        rw [he] at hh htests
        simp [stageTest, stageGate, compatibleBit, Nat.unpair_pair, hs, htests, hh]
      · have htests : ¬ ∀ k < testBound (Nat.pair n j),
            oracle M (queryCode (Nat.pair (Nat.pair n j) k)) =
              answerCode (Nat.pair (Nat.pair n j) k) := by
          rw [← he]
          exact fun hh => hc ((compatibility_tests M N n).mp hh)
        simp [stageTest, stageGate, compatibleBit, Nat.unpair_pair, hs, htests]
    · simp [stageTest, stageGate, Nat.unpair_pair, hs]
end RiceUniform

open FriedbergMuchnik
namespace RiceUniform
lemma search {test : (ℕ → ℕ) → ℕ → ℕ} (ht : Realizes test) :
    ∃ C : Program, ∀ O x, (∃ n, test O (Nat.pair x n) = 0) →
      ∃ n, test O (Nat.pair x n) = 0 ∧ oracleEval (PFun.lift O) C x = Part.some n := by
  obtain ⟨c, hc⟩ := ht
  refine ⟨.mu c, ?_⟩
  intro O x hex
  let f : ℕ →. Bool := fun n => (fun m => decide (m = 0)) <$> oracleEval (PFun.lift O) c (Nat.pair x n)
  have hf : ∀ n, f n = Part.some (decide (test O (Nat.pair x n) = 0)) := by
    intro n
    simp only [f, hc]
    rfl
  obtain ⟨n, hn⟩ := hex
  have hd : (Nat.rfind f).Dom := Nat.rfind_dom.mpr ⟨n, by simp [hf, hn], by
    intro m hm
    rw [hf]
    trivial⟩
  obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hd
  have hs := Nat.rfind_spec hk
  rw [hf] at hs
  have hz : test O (Nat.pair x k) = 0 := by simpa using hs
  exact ⟨k, hz, Part.eq_some_iff.mpr hk⟩
end RiceUniform

open ObfImpossibility.RiceSimulator FriedbergMuchnik
namespace RiceUniform

def failureBit (T : Machine) (O : ℕ → ℕ) (p : ℕ) : ℕ :=
  if stageBit T O p = 1 then 0 else 1

lemma failureBit_realizes (T : Machine) : Realizes (failureBit T) := by
  have hf : Primrec (fun z : ℕ => if z = 1 then 0 else 1) :=
    Primrec.ite (Primrec.eq.comp .id (Primrec.const 1)) (Primrec.const 0) (Primrec.const 1)
  change Realizes (fun O p => if stageBit T O p = 1 then 0 else 1)
  exact comp (f := fun _ z => if z = 1 then 0 else 1) (g := stageBit T)
    (pure hf.to_comp) (stageBit_realizes T)

lemma simulator_output (T : Machine) :
    ∃ S : Program, ∀ (M : Machine) (σ : ℕ),
      T.eval (Encodable.encode M) = Part.some σ →
      (∃ n, StageAnswer T M n σ) → simRun S M (size M) = Part.some σ := by
  obtain ⟨C, hC⟩ := search (failureBit_realizes T)
  refine ⟨.comp .right C, ?_⟩
  intro M σ hT hex
  obtain ⟨n, hn⟩ := hex
  have hgood := (stageBit_correct T M n σ).mpr hn
  have he : ∃ q, failureBit T (oracle M) (Nat.pair (size M) q) = 0 :=
    ⟨Nat.pair n σ, by simp only [failureBit, hgood, if_true]⟩
  obtain ⟨q, hq, hr⟩ := hC (oracle M) (size M) he
  have hbit : stageBit T (oracle M) (Nat.pair (size M) q) = 1 := by
    simpa only [failureBit, ite_eq_left_iff, Nat.one_ne_zero, imp_false, not_not] using hq
  have hstage : StageAnswer T M q.unpair.1 q.unpair.2 :=
    (stageBit_correct T M _ _).mp (by simpa only [Nat.pair_unpair] using hbit)
  have hout := stage_sound T M _ _ hstage
  rw [hT] at hout
  have hσ : q.unpair.2 = σ := by simpa only [Part.mem_some_iff] using hout
  change Part.bind (oracleEval (PFun.lift (oracle M)) C (size M))
    (fun z => Part.some z.unpair.2) = _
  rw [hr, Part.bind_some, hσ]

end RiceUniform
namespace ObfImpossibility.RiceSimulator
 theorem _root_.solution (P : PromiseProblem) (hclosed : P.ClosedUnderFn)
    (hdec : P.IsDecidable) :
    ∃ S : FriedbergMuchnik.Program,
      (∀ M ∈ P.yes, simRun S M (size M) = Part.some 1) ∧
      (∀ M ∈ P.no, simRun S M (size M) = Part.some 0) := by
  obtain ⟨T, hT⟩ := hdec
  obtain ⟨S, hS⟩ := RiceUniform.simulator_output T
  have ht := termination P hclosed T hT
  exact ⟨S, (fun M hM => hS M 1 (hT.1 M hM) (ht.1 M hM)),
    (fun M hM => hS M 0 (hT.2 M hM) (ht.2 M hM))⟩
end ObfImpossibility.RiceSimulator
#print axioms solution

