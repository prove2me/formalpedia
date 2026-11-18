-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.oracle_false_mem_delta
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:51:52.713728+00:00
-- url     : https://prove2.me/submissions/f29a35bf-a220-4ed6-b030-c578a8199a3a

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

private def haltMachine (b : Bool) : OTM where
  k := 0
  g := 0
  δ := fun _ a c => (if b then 1 else 2, a, 1, c, 1)

private theorem haltMachine_result (b : Bool) (O : Oracle) (x : Word) :
    (haltMachine b).result O x 1 = some b := by
  cases b <;> rfl

private theorem altLen_const (lengths : List ℕ) (start : Bool) (P : Prop) :
    AvgPHETH.AltLen lengths start (fun _ => P) ↔ P := by
  induction lengths generalizing start with
  | nil => rfl
  | cons n ns ih =>
    cases start with
    | false =>
      simp only [AvgPHETH.AltLen, ih]
      constructor
      · intro h; exact h (List.replicate n false) (by simp)
      · exact fun h _ _ => h
    | true =>
      simp only [AvgPHETH.AltLen, ih]
      constructor
      · rintro ⟨w, hw, h⟩; exact h
      · intro h; exact ⟨List.replicate n false, by simp, h⟩

 theorem empty_mem_sigma (i : ℕ) : (∅ : Language) ∈ Sigma i := by
  refine ⟨haltMachine false, 1, List.replicate i 0, by simp, ?_, ?_⟩
  · intro s
    simpa using congrArg Option.isSome (haltMachine_result false (fun _ => false) s)
  · intro x
    simp only [Set.mem_empty_iff_false]
    have hres : ∀ ys : List Word,
        (haltMachine false).result (fun _ => false) (tup (x :: ys))
          ((1 : Polynomial ℕ).eval (tup (x :: ys)).length) = some true ↔ False := by
      intro ys
      simp [haltMachine_result]
    simp only [hres]
    exact (altLen_const _ true False).symm

 theorem univ_mem_sigma (i : ℕ) : (Set.univ : Language) ∈ Sigma i := by
  refine ⟨haltMachine true, 1, List.replicate i 0, by simp, ?_, ?_⟩
  · intro s
    simpa using congrArg Option.isSome (haltMachine_result true (fun _ => false) s)
  · intro x
    simp only [Set.mem_univ]
    have hres : ∀ ys : List Word,
        (haltMachine true).result (fun _ => false) (tup (x :: ys))
          ((1 : Polynomial ℕ).eval (tup (x :: ys)).length) = some true ↔ True := by
      intro ys
      simp [haltMachine_result]
    simp only [hres]
    exact (altLen_const _ true True).symm

private theorem bitOf_symOf (g : ℕ) (b : Bool) : OTM.bitOf (OTM.symOf g b) = some b := by
  cases b <;> rfl

theorem init_readBits (M : OTM) (x : Word) :
    OTM.readBits (M.init x).work (M.init x).whi = x := by
  classical
  have hmap : (List.range (x.length + 1)).map (fun j : ℕ => OTM.bitOf ((M.init x).work (j : ℤ))) =
      x.map some ++ [none] := by
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range]
      by_cases hj : j < x.length
      · rw [List.getElem_append_left (by simpa using hj), List.getElem_map]
        have hji : (j : ℤ) < x.length := by exact_mod_cast hj
        simp only [OTM.init, Int.natCast_nonneg, hji, and_self, if_true, Int.toNat_natCast]
        rw [List.getD_eq_getElem _ _ hj, bitOf_symOf]
      · have heq : j = x.length := by simp only [List.length_map, List.length_range] at hj1; omega
        subst j
        simp [OTM.init, OTM.bitOf, Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < M.g + 3 by omega)]
  unfold OTM.readBits
  change ((List.map (fun j : ℤ => OTM.bitOf ((M.init x).work j))
      ((List.range ((x.length : ℤ) + 1).toNat).flatMap (fun j : ℕ => [(j : ℤ)]))).takeWhile
      (·.isSome)).reduceOption = x
  rw [← List.map_eq_flatMap, List.map_map]
  change (((List.range ((x.length : ℤ) + 1).toNat).map (fun j : ℕ => OTM.bitOf ((M.init x).work (j : ℤ)))).takeWhile
      (·.isSome)).reduceOption = x
  have hnat : ((x.length : ℤ) + 1).toNat = x.length + 1 := by omega
  rw [hnat, hmap]
  clear hmap hnat
  induction x with
  | nil => rfl
  | cons b x ih => simpa using congrArg (List.cons b) ih

private theorem haltMachine_output (b : Bool) (O : Oracle) (x : Word) :
    (haltMachine b).output O x 1 = x := by
  change OTM.readBits (Function.update ((haltMachine b).init x).work 0
      (((haltMachine b).init x).work 0)) (max (x.length : ℤ) 0) = x
  rw [Function.update_eq_self, max_eq_left (by omega)]
  exact init_readBits (haltMachine b) x

 theorem inFP_id (i : ℕ) : InFP i (fun x => x) := by
  refine ⟨fun _ => false, haltMachine true, 1, ?_, ?_⟩
  · simpa using empty_mem_sigma i
  · intro x
    constructor
    · simpa using congrArg Option.isSome (haltMachine_result true (fun _ => false) x)
    · simpa using haltMachine_output true (fun _ => false) x

end StudentTeacher976.Adaptivity
namespace QAdvFew.PoQOracle.OTM.Precheck
theorem normal_step (N : OTM) (O : Oracle) (c : N.Cfg)
    (hh : ¬ (c.state = 1 ∨ c.state = 2)) (hq : c.state ≠ 3)
    (q : Fin (N.k + 6)) (a b : Fin (N.g + 3)) (m m' : Fin 3)
    (hd : N.δ c.state (c.work c.wh) (c.query c.qh) = (q, a, m, b, m')) :
    N.step O c =
      { state := q
        work := Function.update c.work c.wh a
        wh := c.wh + (m.val : ℤ) - 1
        query := Function.update c.query c.qh b
        qh := c.qh + (m'.val : ℤ) - 1
        wlo := min c.wlo (c.wh + (m.val : ℤ) - 1)
        whi := max c.whi (c.wh + (m.val : ℤ) - 1)
        qlo := min c.qlo (c.qh + (m'.val : ℤ) - 1)
        qhi := max c.qhi (c.qh + (m'.val : ℤ) - 1) } := by
  unfold step
  rw [if_neg hh, if_neg hq]
  dsimp only
  rw [hd]


end QAdvFew.PoQOracle.OTM.Precheck
set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

abbrev queryMachine (negate : Bool) : OTM where
  k := 0
  g := 0
  δ := fun q a b =>
    if q = 4 then (if negate then 2 else 1, a, 1, b, 1)
    else if q = 5 then (if negate then 1 else 2, a, 1, b, 1)
    else if a = 0 then (3, a, 1, b, 1)
    else (0, a, 2, a, 2)

private def partialQuery (x : List Bool) (t : ℕ) (i : ℤ) : Fin 3 :=
  if 0 ≤ i ∧ i < t then symOf 0 (x.getD i.toNat false) else 0

private def copyCfg (negate : Bool) (x : List Bool) (t : ℕ) (q : Fin 6 := 0) : (queryMachine negate).Cfg where
  state := q
  work := ((queryMachine negate).init x).work
  wh := t
  query := partialQuery x t
  qh := t
  wlo := 0
  whi := x.length
  qlo := 0
  qhi := t

private theorem copyCfg_initial (negate : Bool) (x : List Bool) : copyCfg negate x 0 = (queryMachine negate).init x := by
  simp [copyCfg, init]
  funext i
  simp [partialQuery]

private theorem partial_update (x : List Bool) (t : ℕ) :
    Function.update (partialQuery x t) (t : ℤ) (symOf 0 (x.getD t false)) = partialQuery x (t + 1) := by
  funext i
  by_cases hi : i = t
  · subst i
    simp [partialQuery]
  · rw [Function.update_of_ne hi]
    unfold partialQuery
    have heq : (0 ≤ i ∧ i < (t : ℤ)) ↔ (0 ≤ i ∧ i < (t + 1 : ℕ)) := by omega
    simp only [heq]

private theorem query_delta_bit (negate : Bool) (b : Bool) (c : Fin 3) :
    (queryMachine negate).δ 0 (symOf 0 b) c = (0, symOf 0 b, 2, symOf 0 b, 2) := by
  cases b <;> rfl

private theorem copy_step (negate : Bool) (O : Oracle) (x : List Bool) (t : ℕ) (ht : t < x.length) :
    (queryMachine negate).step O (copyCfg negate x t) = copyCfg negate x (t + 1) := by
  have hti : (t : ℤ) < x.length := by exact_mod_cast ht
  have hwork : ((queryMachine negate).init x).work (t : ℤ) = symOf 0 (x.getD t false) := by
    simp [init, hti]
  have hu : Function.update ((queryMachine negate).init x).work (t : ℤ) (symOf 0 (x.getD t false)) =
      ((queryMachine negate).init x).work := by rw [← hwork, Function.update_eq_self]
  have hh : ¬ ((copyCfg negate x t).state = 1 ∨ (copyCfg negate x t).state = 2) := by exact (by decide : ¬ ((0 : Fin 6) = 1 ∨ (0 : Fin 6) = 2))
  have hq : (copyCfg negate x t).state ≠ 3 := by exact (by decide : (0 : Fin 6) ≠ 3)
  have hd : (queryMachine negate).δ (copyCfg negate x t).state
      ((copyCfg negate x t).work (copyCfg negate x t).wh)
      ((copyCfg negate x t).query (copyCfg negate x t).qh) =
      (0, symOf 0 (x.getD t false), 2, symOf 0 (x.getD t false), 2) := by
    change (queryMachine negate).δ 0 (((queryMachine negate).init x).work (t : ℤ)) (partialQuery x t (t : ℤ)) = _
    rw [hwork, query_delta_bit]
  rw [Precheck.normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [copyCfg] at hu ⊢
  rw [hu, partial_update]
  simp (disch := omega) [copyCfg, init, min_eq_left, max_eq_left] <;> omega

private theorem copy_run (negate : Bool) (O : Oracle) (x : List Bool) (t : ℕ) (ht : t ≤ x.length) :
    (queryMachine negate).runCfg O x t = copyCfg negate x t := by
  revert ht
  induction t with
  | zero => intro ht; exact (copyCfg_initial negate x).symm
  | succ t ih =>
    intro ht
    rw [runCfg, Function.iterate_succ_apply']
    change (queryMachine negate).step O ((queryMachine negate).runCfg O x t) = _
    rw [ih (by omega)]
    exact copy_step negate O x t (by omega)

private theorem copy_finish (negate : Bool) (O : Oracle) (x : List Bool) :
    (queryMachine negate).step O (copyCfg negate x x.length) = copyCfg negate x x.length 3 := by
  have hw : ((queryMachine negate).init x).work (x.length : ℤ) = 0 := by simp [init]
  have hquery : partialQuery x x.length (x.length : ℤ) = 0 := by simp [partialQuery]
  have hu : Function.update ((queryMachine negate).init x).work (x.length : ℤ) 0 =
      ((queryMachine negate).init x).work := by rw [← hw, Function.update_eq_self]
  have hqu : Function.update (partialQuery x x.length) (x.length : ℤ) 0 = partialQuery x x.length := by
    rw [← hquery, Function.update_eq_self]
  have hh : ¬ ((copyCfg negate x x.length).state = 1 ∨ (copyCfg negate x x.length).state = 2) :=
    (by decide : ¬ ((0 : Fin 6) = 1 ∨ (0 : Fin 6) = 2))
  have hq : (copyCfg negate x x.length).state ≠ 3 := (by decide : (0 : Fin 6) ≠ 3)
  have hd : (queryMachine negate).δ (copyCfg negate x x.length).state
      ((copyCfg negate x x.length).work (copyCfg negate x x.length).wh)
      ((copyCfg negate x x.length).query (copyCfg negate x x.length).qh) = (3, 0, 1, 0, 1) := by
    change (queryMachine negate).δ 0 (((queryMachine negate).init x).work (x.length : ℤ)) (partialQuery x x.length (x.length : ℤ)) = _
    rw [hw, hquery]
    rfl
  rw [Precheck.normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [copyCfg]
  rw [hu, hqu]
  simp (disch := omega) [copyCfg, init, min_eq_left, max_eq_left] <;> omega

private theorem step_query_state (M : OTM) (O : Oracle) (c : M.Cfg) (hq : c.state = 3) :
    M.step O c = { c with state := if O (readBits c.query c.qhi) then 4 else 5 } := by
  have hh : ¬ (c.state = 1 ∨ c.state = 2) := by
    rw [hq]
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  unfold step
  rw [if_neg hh, if_pos hq]

private theorem query_finish (negate : Bool) (O : Oracle) (x : List Bool) :
    (queryMachine negate).step O (copyCfg negate x x.length 3) =
      copyCfg negate x x.length (if O x then 4 else 5) := by
  have hread : readBits (copyCfg negate x x.length 3).query (copyCfg negate x x.length 3).qhi = x := by
    change readBits ((queryMachine negate).init x).work ((queryMachine negate).init x).whi = x
    exact StudentTeacher976.Adaptivity.init_readBits _ _
  rw [step_query_state _ _ _ rfl, hread]
  rfl

private theorem query_delta_answer (negate b : Bool) (a c : Fin 3) :
    (queryMachine negate).δ (if b then 4 else 5) a c =
      (if (if negate then !b else b) then 1 else 2, a, 1, c, 1) := by
  cases negate <;> cases b <;> rfl

private theorem answer_finish (negate : Bool) (O : Oracle) (x : List Bool) (b : Bool) :
    (queryMachine negate).step O (copyCfg negate x x.length (if b then 4 else 5)) =
      copyCfg negate x x.length (if (if negate then !b else b) then 1 else 2) := by
  have hh : ¬ ((copyCfg negate x x.length (if b then 4 else 5)).state = 1 ∨
      (copyCfg negate x x.length (if b then 4 else 5)).state = 2) := by
    change ¬ ((if b then 4 else 5 : Fin 6) = 1 ∨ (if b then 4 else 5 : Fin 6) = 2)
    cases b <;> exact (by decide)
  have hq : (copyCfg negate x x.length (if b then 4 else 5)).state ≠ 3 := by
    change (if b then 4 else 5 : Fin 6) ≠ 3
    cases b <;> exact (by decide)
  rw [Precheck.normal_step _ _ _ hh hq _ _ _ _ _ (query_delta_answer negate b _ _)]
  simp (disch := omega) [copyCfg, init, Function.update_eq_self] <;> omega

 theorem queryMachine_result (negate : Bool) (O : Oracle) (x : List Bool) :
    (queryMachine negate).result O x (x.length + 3) = some (if negate then !(O x) else O x) := by
  have hrun : (queryMachine negate).runCfg O x (x.length + 3) =
      ((queryMachine negate).step O)^[3] (copyCfg negate x x.length) := by
    rw [show x.length + 3 = 3 + x.length by omega, runCfg, Function.iterate_add_apply]
    change ((queryMachine negate).step O)^[3] ((queryMachine negate).runCfg O x x.length) = _
    rw [copy_run negate O x _ (by rfl)]
  have hsteps : ((queryMachine negate).step O)^[3] (copyCfg negate x x.length) =
      copyCfg negate x x.length (if (if negate then !(O x) else O x) then 1 else 2) := by
    change (queryMachine negate).step O ((queryMachine negate).step O ((queryMachine negate).step O (copyCfg negate x x.length))) = _
    rw [copy_finish, query_finish, answer_finish]
  unfold result
  rw [hrun, hsteps]
  cases negate <;> cases hO : O x <;> rfl

end QAdvFew.PoQOracle.OTM

namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

private theorem oracle_false_impl (i : ℕ) (O : Oracle) (hO : {s | O s = true} ∈ Sigma i) :
    {s | O s = false} ∈ Delta i := by
  refine ⟨O, OTM.queryMachine true, Polynomial.X + 3, hO, ?_, ?_⟩
  · intro x
    simpa [OTM.queryMachine_result] using congrArg Option.isSome (OTM.queryMachine_result true O x)
  · intro x
    simp only [Set.mem_setOf_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
      OTM.queryMachine_result, if_true, Option.some.injEq]
    cases O x <;> simp

end StudentTeacher976.Adaptivity
open StudentTeacher976.Adaptivity QAdvFew.PoQOracle
theorem solution (i : ℕ) (O : Oracle)
    (hO : {s | O s = true} ∈ StudentTeacher976.Adaptivity.Sigma i) :
    {s | O s = false} ∈ Delta i := oracle_false_impl i O hO
