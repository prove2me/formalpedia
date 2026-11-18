-- Prove2me | solution 1 for StudentTeacher976.Adaptivity.sigma_witness_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:25:05.762742+00:00
-- url     : https://prove2.me/submissions/68fe9f61-faeb-4579-9e6d-96d94cae83f6

import Definitions.Def_StudentTeacher976_Adaptivity_Auxiliary
import Theorems.Thm_StudentTeacher976_Adaptivity_residual_quantifier_padding


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

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

private theorem halted_state (M : OTM) (O : Oracle) (x : List Bool) (t : ℕ)
    (h : (M.result O x t).isSome) :
    (M.runCfg O x t).state = 1 ∨ (M.runCfg O x t).state = 2 := by
  unfold result at h
  dsimp only at h
  split at h
  · exact Or.inl ‹_›
  · split at h
    · exact Or.inr ‹_›
    · simp at h

 theorem runCfg_stable (M : OTM) (O : Oracle) (x : List Bool) (t s : ℕ)
    (h : (M.result O x t).isSome) : M.runCfg O x (t + s) = M.runCfg O x t := by
  have hstep : M.step O (M.runCfg O x t) = M.runCfg O x t := by
    simp [step, halted_state M O x t h]
  have hiter : ∀ s, (M.step O)^[s] (M.runCfg O x t) = M.runCfg O x t := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [Function.iterate_succ_apply', ih, hstep]
  unfold runCfg
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hiter s

 theorem result_stable (M : OTM) (O : Oracle) (x : List Bool) (t s : ℕ)
    (h : (M.result O x t).isSome) : M.result O x (t + s) = M.result O x t := by
  unfold result
  rw [runCfg_stable M O x t s h]

 theorem output_stable (M : OTM) (O : Oracle) (x : List Bool) (t s : ℕ)
    (h : (M.result O x t).isSome) : M.output O x (t + s) = M.output O x t := by
  unfold output
  rw [runCfg_stable M O x t s h]

 theorem result_of_le (M : OTM) (O : Oracle) (x : List Bool) (t u : ℕ)
    (h : (M.result O x t).isSome) (htu : t ≤ u) : M.result O x u = M.result O x t := by
  rw [← Nat.add_sub_of_le htu]
  exact result_stable M O x t (u - t) h

 theorem output_of_le (M : OTM) (O : Oracle) (x : List Bool) (t u : ℕ)
    (h : (M.result O x t).isSome) (htu : t ≤ u) : M.output O x u = M.output O x t := by
  rw [← Nat.add_sub_of_le htu]
  exact output_stable M O x t (u - t) h

end QAdvFew.PoQOracle.OTM

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

private theorem bitOf_zero (g : ℕ) : bitOf (0 : Fin (g + 3)) = none := by
  simp (disch := omega) [bitOf, Fin.ext_iff, Nat.mod_eq_of_lt]

private theorem readBits_nat {g : ℕ} (tape : ℤ → Fin (g + 3)) (hi : ℤ) :
    readBits tape hi = (((List.range (hi + 1).toNat).map
      (fun j : ℕ => bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption := by
  unfold readBits
  change ((List.map (fun j : ℤ => bitOf (tape j))
      ((List.range (hi + 1).toNat).flatMap (fun j : ℕ => [(j : ℤ)]))).takeWhile
      (·.isSome)).reduceOption = _
  rw [← List.map_eq_flatMap, List.map_map]
  rfl

private theorem takeWhile_none (A B : List (Option Bool)) :
    (A ++ none :: B).takeWhile (·.isSome) = A.takeWhile (·.isSome) := by
  induction A with
  | nil => rfl
  | cons a A ih => cases a <;> simp [List.takeWhile, ih]

private theorem readBits_more {g : ℕ} (tape : ℤ → Fin (g + 3)) (n extra : ℕ)
    (hblank : tape (n : ℤ) = 0) :
    ((((List.range (n + extra)).map (fun j : ℕ => bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption) =
      ((((List.range n).map (fun j : ℕ => bitOf (tape (j : ℤ)))).takeWhile (·.isSome)).reduceOption) := by
  rw [List.range_add, List.map_append, List.map_map]
  cases extra with
  | zero => simp
  | succ e =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, Function.comp_apply, Nat.add_zero, hblank, bitOf_zero, takeWhile_none]

 theorem readBits_of_le {g : ℕ} (tape : ℤ → Fin (g + 3)) (lo hi : ℤ)
    (hlo : 0 ≤ lo) (hle : lo ≤ hi) (hblank : tape (lo + 1) = 0) :
    readBits tape hi = readBits tape lo := by
  rw [readBits_nat, readBits_nat]
  have hn : (lo + 1).toNat ≤ (hi + 1).toNat := by omega
  have heq : (hi + 1).toNat = (lo + 1).toNat + ((hi + 1).toNat - (lo + 1).toNat) := by omega
  rw [heq]
  apply readBits_more
  simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ lo + 1), Int.natCast_natAbs] using hblank

structure TapeValid {g : ℕ} (tape : ℤ → Fin (g + 3)) (head lo hi : ℤ) : Prop where
  lo_head : lo ≤ head
  head_hi : head ≤ hi
  lo_zero : lo ≤ 0
  zero_hi : 0 ≤ hi
  outside : ∀ i, i < lo ∨ hi < i → tape i = 0

 theorem TapeValid.update_move {g : ℕ} {tape : ℤ → Fin (g + 3)} {head lo hi : ℤ}
    (h : TapeValid tape head lo hi) (a : Fin (g + 3)) (newhead : ℤ) :
    TapeValid (Function.update tape head a) newhead (min lo newhead) (max hi newhead) := by
  constructor
  · exact min_le_right _ _
  · exact le_max_right _ _
  · exact le_trans (min_le_left _ _) h.lo_zero
  · exact le_trans h.zero_hi (le_max_left _ _)
  · intro i hiout
    have hiold : i < lo ∨ hi < i := by rcases hiout with hl | hr <;> omega
    have hne : i ≠ head := by rcases hiold with hl | hr <;> have := h.lo_head <;> have := h.head_hi <;> omega
    rw [Function.update_of_ne hne]
    exact h.outside i hiold

structure Valid (M : OTM) (c : M.Cfg) : Prop where
  work : TapeValid c.work c.wh c.wlo c.whi
  query : TapeValid c.query c.qh c.qlo c.qhi

 theorem valid_init (M : OTM) (x : List Bool) : Valid M (M.init x) := by
  constructor
  · constructor
    · rfl
    · dsimp [init]; omega
    · rfl
    · dsimp [init]; omega
    · intro i hi
      simp only [init] at *
      rw [if_neg (by rcases hi with h | h <;> omega)]
  · constructor
    · rfl
    · rfl
    · rfl
    · rfl
    · intro i hi; rfl

 theorem valid_step (M : OTM) (O : Oracle) (c : M.Cfg) (h : Valid M c) : Valid M (M.step O c) := by
  unfold step
  split
  · exact h
  · split
    · exact ⟨h.work, h.query⟩
    · constructor
      · exact h.work.update_move _ _
      · exact h.query.update_move _ _

 theorem valid_runCfg (M : OTM) (O : Oracle) (x : List Bool) (t : ℕ) : Valid M (M.runCfg O x t) := by
  induction t with
  | zero => exact valid_init M x
  | succ t ih =>
    rw [runCfg, Function.iterate_succ_apply']
    change Valid M (M.step O (M.runCfg O x t))
    exact valid_step M O _ ih

structure CoreEq (M : OTM) (c d : M.Cfg) : Prop where
  state : c.state = d.state
  work : c.work = d.work
  wh : c.wh = d.wh
  query : c.query = d.query
  qh : c.qh = d.qh

 theorem TapeValid.readBits_eq {g : ℕ} {tape : ℤ → Fin (g + 3)} {h h' l l' u u' : ℤ}
    (ht : TapeValid tape h l u) (ht' : TapeValid tape h' l' u') :
    readBits tape u = readBits tape u' := by
  rcases le_total u u' with hle | hle
  · exact (readBits_of_le tape u u' ht.zero_hi hle (ht.outside _ (by omega))).symm
  · exact readBits_of_le tape u' u ht'.zero_hi hle (ht'.outside _ (by omega))

 theorem coreEq_step (M : OTM) (O : Oracle) (c d : M.Cfg)
    (hc : Valid M c) (hd : Valid M d) (h : CoreEq M c d) :
    CoreEq M (M.step O c) (M.step O d) := by
  have hread : readBits c.query c.qhi = readBits d.query d.qhi := by
    have hq := hc.query
    rw [h.query] at hq
    rw [h.query]
    exact hq.readBits_eq hd.query
  unfold step
  simp only [h.state, h.work, h.wh, h.qh]
  rw [hread]
  simp only [h.query]
  split
  · exact h
  · split <;> constructor <;> rfl

 theorem valid_iterate (M : OTM) (O : Oracle) (c : M.Cfg) (t : ℕ) (hc : Valid M c) :
    Valid M ((M.step O)^[t] c) := by
  induction t with
  | zero => exact hc
  | succ t ih => rw [Function.iterate_succ_apply']; exact valid_step M O _ ih

 theorem coreEq_iterate (M : OTM) (O : Oracle) (c d : M.Cfg) (t : ℕ)
    (hc : Valid M c) (hd : Valid M d) (h : CoreEq M c d) :
    CoreEq M ((M.step O)^[t] c) ((M.step O)^[t] d) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact coreEq_step M O _ _ (valid_iterate M O c t hc) (valid_iterate M O d t hd) ih

 theorem coreEq_readBits_work (M : OTM) (c d : M.Cfg)
    (hc : Valid M c) (hd : Valid M d) (h : CoreEq M c d) :
    readBits c.work c.whi = readBits d.work d.whi := by
  have hw := hc.work
  rw [h.work] at hw ⊢
  exact hw.readBits_eq hd.work

 theorem result_of_coreEq (M : OTM) (O : Oracle) (x y : List Bool) (s t : ℕ)
    (h : CoreEq M (M.runCfg O x s) (M.runCfg O y t)) : M.result O x s = M.result O y t := by
  unfold result
  dsimp only
  rw [h.state]

 theorem output_of_coreEq (M : OTM) (O : Oracle) (x y : List Bool) (s t : ℕ)
    (h : CoreEq M (M.runCfg O x s) (M.runCfg O y t)) : M.output O x s = M.output O y t :=
  coreEq_readBits_work M _ _ (valid_runCfg M O x s) (valid_runCfg M O y t) h

end QAdvFew.PoQOracle.OTM

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM

structure Simulation (M N : OTM) where
  states : Fin (M.k + 6) ↪ Fin (N.k + 6)
  symbols : Fin (M.g + 3) ↪ Fin (N.g + 3)
  accept : states 1 = 1
  reject : states 2 = 2
  queryState : states 3 = 3
  yes : states 4 = 4
  no : states 5 = 5
  blank : symbols 0 = 0
  bitFalse : symbols 1 = 1
  bitTrue : symbols 2 = 2
  transition : ∀ q a b,
    N.δ (states q) (symbols a) (symbols b) =
      let d := M.δ q a b
      (states d.1, symbols d.2.1, d.2.2.1, symbols d.2.2.2.1, d.2.2.2.2)

namespace Simulation
variable {M N : OTM} (E : Simulation M N)

private theorem state_accept (q : Fin (M.k + 6)) : E.states q = 1 ↔ q = 1 := by
  rw [← E.accept, E.states.injective.eq_iff]
private theorem state_reject (q : Fin (M.k + 6)) : E.states q = 2 ↔ q = 2 := by
  rw [← E.reject, E.states.injective.eq_iff]
private theorem state_query (q : Fin (M.k + 6)) : E.states q = 3 ↔ q = 3 := by
  rw [← E.queryState, E.states.injective.eq_iff]

 theorem bitOf_symbols (a : Fin (M.g + 3)) : bitOf (E.symbols a) = bitOf a := by
  have h1 : E.symbols a = 1 ↔ a = 1 := by rw [← E.bitFalse, E.symbols.injective.eq_iff]
  have h2 : E.symbols a = 2 ↔ a = 2 := by rw [← E.bitTrue, E.symbols.injective.eq_iff]
  simp only [bitOf, h1, h2]

 theorem readBits_symbols (tape : ℤ → Fin (M.g + 3)) (hi : ℤ) :
    readBits (fun i => E.symbols (tape i)) hi = readBits tape hi := by
  unfold readBits
  simp only [E.bitOf_symbols]

 def cfg (c : M.Cfg) : N.Cfg where
  state := E.states c.state
  work := fun i => E.symbols (c.work i)
  wh := c.wh
  query := fun i => E.symbols (c.query i)
  qh := c.qh
  wlo := c.wlo
  whi := c.whi
  qlo := c.qlo
  qhi := c.qhi

private theorem symbols_update (tape : ℤ → Fin (M.g + 3)) (pos : ℤ) (a : Fin (M.g + 3)) :
    (fun i => E.symbols (Function.update tape pos a i)) =
      Function.update (fun i => E.symbols (tape i)) pos (E.symbols a) := by
  funext i
  by_cases h : i = pos <;> simp [Function.update, h]

 theorem cfg_step (O : Oracle) (c : M.Cfg) : E.cfg (M.step O c) = N.step O (E.cfg c) := by
  dsimp only [step, cfg]
  simp only [E.state_accept, E.state_reject, E.state_query, E.readBits_symbols]
  by_cases hh : c.state = 1 ∨ c.state = 2
  · simp only [if_pos hh]
  · simp only [if_neg hh]
    by_cases hq : c.state = 3
    · simp only [if_pos hq]
      split <;> simp only [E.yes, E.no]
    · simp only [if_neg hq, E.transition, E.symbols_update]

 theorem cfg_iterate (O : Oracle) (c : M.Cfg) (t : ℕ) :
    E.cfg ((M.step O)^[t] c) = (N.step O)^[t] (E.cfg c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', E.cfg_step, ih]

 theorem cfg_init (x : List Bool) (hstart : E.states 0 = 0) : E.cfg (M.init x) = N.init x := by
  have hsym : ∀ b, E.symbols (symOf M.g b) = symOf N.g b := by
    intro b
    cases b <;> simp only [symOf, Bool.false_eq_true, ↓reduceIte, E.bitFalse, E.bitTrue]
  dsimp only [cfg, init]
  simp only [hstart, E.blank]
  congr 1
  funext i
  split <;> simp only [hsym, E.blank]

 theorem runCfg (O : Oracle) (x : List Bool) (t : ℕ) (hstart : E.states 0 = 0) :
    E.cfg (M.runCfg O x t) = N.runCfg O x t := by
  rw [OTM.runCfg, E.cfg_iterate, E.cfg_init x hstart]
  rfl

 theorem result (O : Oracle) (x : List Bool) (t : ℕ) (hstart : E.states 0 = 0) :
    N.result O x t = M.result O x t := by
  unfold OTM.result
  rw [← E.runCfg O x t hstart]
  dsimp only [cfg]
  simp only [E.state_accept, E.state_reject]

 theorem output (O : Oracle) (x : List Bool) (t : ℕ) (hstart : E.states 0 = 0) :
    N.output O x t = M.output O x t := by
  unfold OTM.output
  rw [← E.runCfg O x t hstart]
  exact E.readBits_symbols _ _

 theorem runCfg_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : N.runCfg O x s = E.cfg (M.init y)) :
    N.runCfg O x (s + t) = E.cfg (M.runCfg O y t) := by
  unfold OTM.runCfg at *
  rw [Nat.add_comm s t, Function.iterate_add_apply, hprefix, ← E.cfg_iterate]

 theorem result_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : N.runCfg O x s = E.cfg (M.init y)) :
    N.result O x (s + t) = M.result O y t := by
  unfold OTM.result
  rw [E.runCfg_after_prefix O x y s t hprefix]
  dsimp only [cfg]
  simp only [E.state_accept, E.state_reject]

 theorem output_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : N.runCfg O x s = E.cfg (M.init y)) :
    N.output O x (s + t) = M.output O y t := by
  unfold OTM.output
  rw [E.runCfg_after_prefix O x y s t hprefix]
  exact E.readBits_symbols _ _

 theorem cfg_valid (c : M.Cfg) (h : Valid M c) : Valid N (E.cfg c) := by
  constructor
  · refine ⟨h.work.lo_head, h.work.head_hi, h.work.lo_zero, h.work.zero_hi, ?_⟩
    intro i hi
    change E.symbols (c.work i) = 0
    rw [h.work.outside i hi, E.blank]
  · refine ⟨h.query.lo_head, h.query.head_hi, h.query.lo_zero, h.query.zero_hi, ?_⟩
    intro i hi
    change E.symbols (c.query i) = 0
    rw [h.query.outside i hi, E.blank]

 theorem core_after_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : CoreEq N (N.runCfg O x s) (E.cfg (M.init y))) :
    CoreEq N (N.runCfg O x (s + t)) (E.cfg (M.runCfg O y t)) := by
  have hrun : N.runCfg O x (s + t) = (N.step O)^[t] (N.runCfg O x s) := by
    unfold OTM.runCfg
    rw [Nat.add_comm s t, Function.iterate_add_apply]
  rw [hrun]
  change CoreEq N ((N.step O)^[t] (N.runCfg O x s)) (E.cfg ((M.step O)^[t] (M.init y)))
  rw [E.cfg_iterate]
  exact coreEq_iterate N O _ _ t (valid_runCfg N O x s) (E.cfg_valid _ (valid_init M y)) hprefix

 theorem result_after_core_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : CoreEq N (N.runCfg O x s) (E.cfg (M.init y))) :
    N.result O x (s + t) = M.result O y t := by
  have hcore := E.core_after_prefix O x y s t hprefix
  unfold OTM.result
  dsimp only
  rw [hcore.state]
  dsimp only [cfg]
  simp only [E.state_accept, E.state_reject]

 theorem output_after_core_prefix (O : Oracle) (x y : List Bool) (s t : ℕ)
    (hprefix : CoreEq N (N.runCfg O x s) (E.cfg (M.init y))) :
    N.output O x (s + t) = M.output O y t := by
  have hcore := E.core_after_prefix O x y s t hprefix
  unfold OTM.output
  calc
    readBits (N.runCfg O x (s + t)).work (N.runCfg O x (s + t)).whi =
        readBits (E.cfg (M.runCfg O y t)).work (E.cfg (M.runCfg O y t)).whi :=
      coreEq_readBits_work N _ _ (valid_runCfg N O x (s + t))
        (E.cfg_valid _ (valid_runCfg M O y t)) hcore
    _ = _ := E.readBits_symbols _ _

end Simulation
end QAdvFew.PoQOracle.OTM

set_option autoImplicit false
namespace QAdvFew.PoQOracle.OTM
namespace Precheck

structure DFA where
  size : ℕ
  start : Fin size
  next : Fin size → Bool → Fin size
  accept : Fin size → Bool

def DFA.run (D : DFA) (x : List Bool) : Fin D.size := x.foldl D.next D.start

def state (M : OTM) (D : DFA) (q : Fin (M.k + 6)) : Fin ((M.k + D.size + 2) + 6) :=
  ⟨if q.val = 0 then M.k + 6 else q.val, by split <;> omega⟩

def symbol (M : OTM) (a : Fin (M.g + 3)) : Fin ((M.g + 2) + 3) := ⟨a.val, by omega⟩

def markFalse (M : OTM) : Fin ((M.g + 2) + 3) := ⟨M.g + 3, by omega⟩
def markTrue (M : OTM) : Fin ((M.g + 2) + 3) := ⟨M.g + 4, by omega⟩

def scan (M : OTM) (D : DFA) (s : Fin D.size) : Fin ((M.k + D.size + 2) + 6) :=
  ⟨M.k + 7 + s.val, by omega⟩
def reset (M : OTM) (D : DFA) : Fin ((M.k + D.size + 2) + 6) :=
  ⟨M.k + 7 + D.size, by omega⟩

def decodeState (M : OTM) (D : DFA) (q : Fin ((M.k + D.size + 2) + 6)) : Fin (M.k + 6) :=
  if h : q.val < M.k + 6 then ⟨q.val, h⟩ else 0

def decodeSymbol (M : OTM) (a : Fin ((M.g + 2) + 3)) : Fin (M.g + 3) :=
  if h : a.val < M.g + 3 then ⟨a.val, h⟩ else 0

 abbrev machine (M : OTM) (D : DFA) : OTM where
  k := M.k + D.size + 2
  g := M.g + 2
  δ := fun q a b =>
    if hstart : q.val = 0 then
      if a = 1 then (scan M D (D.next D.start false), markFalse M, 2, b, 1)
      else if a = 2 then (scan M D (D.next D.start true), markTrue M, 2, b, 1)
      else (if D.accept D.start then state M D 0 else 2, a, 1, b, 1)
    else if hsim : q.val ≤ M.k + 6 then
      let d := M.δ (decodeState M D q) (decodeSymbol M a) (decodeSymbol M b)
      (state M D d.1, symbol M d.2.1, d.2.2.1, symbol M d.2.2.2.1, d.2.2.2.2)
    else if hs : q.val < M.k + 7 + D.size then
      let s : Fin D.size := ⟨q.val - (M.k + 7), by omega⟩
      if a = 1 then (scan M D (D.next s false), a, 2, b, 1)
      else if a = 2 then (scan M D (D.next s true), a, 2, b, 1)
      else (if D.accept s then reset M D else 2, a, if D.accept s then 0 else 1, b, 1)
    else
      if a = markFalse M then (state M D 0, 1, 1, b, 1)
      else if a = markTrue M then (state M D 0, 2, 1, b, 1)
      else (reset M D, a, 0, b, 1)

 theorem state_injective (M : OTM) (D : DFA) : Function.Injective (state M D) := by
  intro q r heq
  have hval := congrArg Fin.val heq
  dsimp only [state] at hval
  apply Fin.ext
  split at hval <;> split at hval <;> omega

 theorem symbol_injective (M : OTM) : Function.Injective (symbol M) := by
  intro a b h
  have hv := congrArg (fun c : Fin ((M.g + 2) + 3) => c.val) h
  exact Fin.ext hv

 theorem decode_state (M : OTM) (D : DFA) (q : Fin (M.k + 6)) :
    decodeState M D (state M D q) = q := by
  unfold decodeState state
  by_cases hq : q.val = 0
  · apply Fin.ext
    simp [hq]
  · simp only [hq, ↓reduceIte, q.isLt, ↓reduceDIte]

 theorem decode_symbol (M : OTM) (a : Fin (M.g + 3)) : decodeSymbol M (symbol M a) = a := by
  unfold decodeSymbol symbol
  simp only [a.isLt, ↓reduceDIte]

private theorem state_number (M : OTM) (D : DFA) (n : ℕ) (hn : 0 < n) (hn6 : n < 6) :
    state M D ⟨n, by omega⟩ = ⟨n, by omega⟩ := by
  apply Fin.ext
  simp [state, Nat.ne_of_gt hn]

private theorem symbol_number (M : OTM) (n : ℕ) (hn : n < 3) :
    symbol M ⟨n, by omega⟩ = ⟨n, by omega⟩ := rfl

 theorem delta_state (M : OTM) (D : DFA) (q : Fin (M.k + 6)) (a b : Fin (M.g + 3)) :
    (machine M D).δ (state M D q) (symbol M a) (symbol M b) =
      let d := M.δ q a b
      (state M D d.1, symbol M d.2.1, d.2.2.1, symbol M d.2.2.2.1, d.2.2.2.2) := by
  have hpos : (state M D q).val ≠ 0 := by dsimp [state]; split <;> omega
  have hle : (state M D q).val ≤ M.k + 6 := by dsimp [state]; split <;> omega
  dsimp only [machine]
  rw [dif_neg hpos, dif_pos hle]
  simp only [decode_state, decode_symbol]

 def simulation (M : OTM) (D : DFA) : Simulation M (machine M D) where
  states := ⟨state M D, state_injective M D⟩
  symbols := ⟨symbol M, symbol_injective M⟩
  accept := by
    change state M D (1 : Fin (M.k + 6)) = (1 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  reject := by
    change state M D (2 : Fin (M.k + 6)) = (2 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  queryState := by
    change state M D (3 : Fin (M.k + 6)) = (3 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  yes := by
    change state M D (4 : Fin (M.k + 6)) = (4 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  no := by
    change state M D (5 : Fin (M.k + 6)) = (5 : Fin ((M.k + D.size + 2) + 6))
    apply Fin.ext
    simp (disch := omega) [state, Nat.mod_eq_of_lt]
  blank := by apply Fin.ext; rfl
  bitFalse := by
    change symbol M (1 : Fin (M.g + 3)) = (1 : Fin ((M.g + 2) + 3))
    apply Fin.ext
    simp (disch := omega) [symbol, Nat.mod_eq_of_lt]
  bitTrue := by
    change symbol M (2 : Fin (M.g + 3)) = (2 : Fin ((M.g + 2) + 3))
    apply Fin.ext
    simp (disch := omega) [symbol, Nat.mod_eq_of_lt]
  transition := by
    intro q a b
    exact delta_state M D q a b

private theorem scan_zero_ne (M : OTM) (D : DFA) (s : Fin D.size) :
    (scan M D s).val ≠ 0 := by dsimp [scan]; omega
private theorem scan_not_sim (M : OTM) (D : DFA) (s : Fin D.size) :
    ¬ (scan M D s).val ≤ M.k + 6 := by dsimp [scan]; omega
private theorem scan_in_range (M : OTM) (D : DFA) (s : Fin D.size) :
    (scan M D s).val < M.k + 7 + D.size := by dsimp [scan]; omega

 theorem delta_scan_bit (M : OTM) (D : DFA) (s : Fin D.size) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (scan M D s) (symOf (M.g + 2) b) c =
      (scan M D (D.next s b), symOf (M.g + 2) b, 2, c, 1) := by
  dsimp only [machine]
  rw [dif_neg (scan_zero_ne M D s), dif_neg (scan_not_sim M D s), dif_pos (scan_in_range M D s)]
  have heq : (⟨(scan M D s).val - (M.k + 7), by have := scan_in_range M D s; dsimp [scan] at *; omega⟩ : Fin D.size) = s := by
    apply Fin.ext
    dsimp [scan]
    omega
  rw [heq]
  cases b <;> simp (disch := omega) [symOf, Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_scan_end (M : OTM) (D : DFA) (s : Fin D.size)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (scan M D s) 0 c =
      (if D.accept s then reset M D else 2, 0, if D.accept s then 0 else 1, c, 1) := by
  dsimp only [machine]
  rw [dif_neg (scan_zero_ne M D s), dif_neg (scan_not_sim M D s), dif_pos (scan_in_range M D s)]
  have heq : (⟨(scan M D s).val - (M.k + 7), by have := scan_in_range M D s; dsimp [scan] at *; omega⟩ : Fin D.size) = s := by
    apply Fin.ext
    dsimp [scan]
    omega
  rw [heq]
  simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_start_bit (M : OTM) (D : DFA) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ 0 (symOf (M.g + 2) b) c =
      (scan M D (D.next D.start b), if b then markTrue M else markFalse M, 2, c, 1) := by
  dsimp only [machine]
  simp only [Fin.val_zero, dif_pos rfl]
  cases b <;> simp (disch := omega) [symOf, Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_start_empty (M : OTM) (D : DFA) (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ 0 0 c = (if D.accept D.start then state M D 0 else 2, 0, 1, c, 1) := by
  dsimp only [machine]
  simp only [Fin.val_zero, dif_pos rfl]
  simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_reset_bit (M : OTM) (D : DFA) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (reset M D) (symOf (M.g + 2) b) c =
      (reset M D, symOf (M.g + 2) b, 0, c, 1) := by
  have h0 : (reset M D).val ≠ 0 := by dsimp [reset]; omega
  have h1 : ¬ (reset M D).val ≤ M.k + 6 := by dsimp [reset]; omega
  have h2 : ¬ (reset M D).val < M.k + 7 + D.size := by dsimp [reset]; omega
  dsimp only [machine]
  rw [dif_neg h0, dif_neg h1, dif_neg h2]
  cases b <;> simp (disch := omega) [symOf, markFalse, markTrue, Fin.ext_iff, Nat.mod_eq_of_lt]

 theorem delta_reset_marker (M : OTM) (D : DFA) (b : Bool)
    (c : Fin ((M.g + 2) + 3)) :
    (machine M D).δ (reset M D) (if b then markTrue M else markFalse M) c =
      (state M D 0, symOf (M.g + 2) b, 1, c, 1) := by
  have h0 : (reset M D).val ≠ 0 := by dsimp [reset]; omega
  have h1 : ¬ (reset M D).val ≤ M.k + 6 := by dsimp [reset]; omega
  have h2 : ¬ (reset M D).val < M.k + 7 + D.size := by dsimp [reset]; omega
  dsimp only [machine]
  rw [dif_neg h0, dif_neg h1, dif_neg h2]
  cases b <;> simp (disch := omega) [symOf, markFalse, markTrue, Fin.ext_iff, Nat.mod_eq_of_lt]

def markedCfg (M : OTM) (D : DFA) (x : List Bool) (first : Bool)
    (q : Fin ((M.k + D.size + 2) + 6)) (head : ℕ) : (machine M D).Cfg :=
  { (machine M D).init x with
    state := q
    work := Function.update ((machine M D).init x).work 0
      (if first then markTrue M else markFalse M)
    wh := head }

private theorem marked_read (M : OTM) (D : DFA) (x : List Bool) (first : Bool)
    (q : Fin ((M.k + D.size + 2) + 6)) (t : ℕ) (ht : 0 < t) (htx : t < x.length) :
    (markedCfg M D x first q t).work (t : ℤ) = symOf (M.g + 2) (x.getD t false) := by
  dsimp only [markedCfg]
  rw [Function.update_of_ne (by omega)]
  have hti : (t : ℤ) < x.length := by exact_mod_cast htx
  simp only [init, Int.natCast_nonneg, hti, and_self, if_true, Int.toNat_natCast]

private theorem state_small_ne_scan (M : OTM) (D : DFA) (s : Fin D.size) (n : ℕ) (hn : n < 6) :
    scan M D s ≠ (⟨n, by omega⟩ : Fin ((M.k + D.size + 2) + 6)) := by
  intro heq
  have hv := congrArg Fin.val heq
  dsimp [scan] at hv
  omega

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

 theorem step_marked_scan (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (s : Fin D.size) (t : ℕ) (ht : 0 < t) (htx : t < x.length) :
    (machine M D).step O (markedCfg M D x first (scan M D s) t) =
      markedCfg M D x first (scan M D (D.next s (x.getD t false))) (t + 1) := by
  have hread := marked_read M D x first (scan M D s) t ht htx
  have hh : ¬ (scan M D s = 1 ∨ scan M D s = 2) := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : scan M D s ≠ 3 := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hu : Function.update (markedCfg M D x first (scan M D s) t).work (t : ℤ)
      (symOf (M.g + 2) (x.getD t false)) = (markedCfg M D x first (scan M D s) t).work := by
    rw [← hread, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D x first (scan M D s) t).state
      ((markedCfg M D x first (scan M D s) t).work (markedCfg M D x first (scan M D s) t).wh)
      ((markedCfg M D x first (scan M D s) t).query (markedCfg M D x first (scan M D s) t).qh) =
      (scan M D (D.next s (x.getD t false)), symOf (M.g + 2) (x.getD t false), 2, 0, 1) := by
    change (machine M D).δ (scan M D s) ((markedCfg M D x first (scan M D s) t).work (t : ℤ)) 0 = _
    rw [hread, delta_scan_bit]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  rw [hu]
  simp (disch := omega) [init, min_eq_left, max_eq_left, Function.update_eq_self] <;> omega

 theorem step_initial_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool) :
    (machine M D).step O ((machine M D).init (b :: xs)) =
      markedCfg M D (b :: xs) b (scan M D (D.next D.start b)) 1 := by
  have hh : ¬ (((machine M D).init (b :: xs)).state = 1 ∨ ((machine M D).init (b :: xs)).state = 2) := by
    change ¬ ((0 : Fin ((M.k + D.size + 2) + 6)) = 1 ∨ 0 = 2)
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hq : ((machine M D).init (b :: xs)).state ≠ 3 := by
    change (0 : Fin ((M.k + D.size + 2) + 6)) ≠ 3
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hread : ((machine M D).init (b :: xs)).work 0 = symOf (M.g + 2) b := by
    simp [init]
  have hd : (machine M D).δ ((machine M D).init (b :: xs)).state
      (((machine M D).init (b :: xs)).work ((machine M D).init (b :: xs)).wh)
      (((machine M D).init (b :: xs)).query ((machine M D).init (b :: xs)).qh) =
      (scan M D (D.next D.start b), if b then markTrue M else markFalse M, 2, 0, 1) := by
    change (machine M D).δ 0 (((machine M D).init (b :: xs)).work 0) 0 = _
    rw [hread, delta_start_bit]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  simp (disch := omega) [markedCfg, init, min_eq_left, max_eq_left, Function.update_eq_self]

 theorem scan_run_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool)
    (t : ℕ) (ht : 0 < t) (htlen : t ≤ (b :: xs).length) :
    (machine M D).runCfg O (b :: xs) t =
      markedCfg M D (b :: xs) b (scan M D (((b :: xs).take t).foldl D.next D.start)) t := by
  revert ht htlen
  induction t with
  | zero => intro ht; omega
  | succ t ih =>
    intro ht htlen
    by_cases ht0 : t = 0
    · subst t
      change (machine M D).step O ((machine M D).init (b :: xs)) = _
      simpa using step_initial_nonempty M D O b xs
    · have htp : 0 < t := by omega
      have htl : t < (b :: xs).length := by omega
      have hfold : (((b :: xs).take (t + 1)).foldl D.next D.start) =
          D.next (((b :: xs).take t).foldl D.next D.start) ((b :: xs).getD t false) := by
        rw [List.take_succ_eq_append_getElem htl, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem _ _ htl]
      rw [hfold]
      rw [OTM.runCfg, Function.iterate_succ_apply']
      change (machine M D).step O ((machine M D).runCfg O (b :: xs) t) = _
      rw [ih htp (by omega)]
      exact step_marked_scan M D O (b :: xs) b _ t htp htl

private theorem marked_end (M : OTM) (D : DFA) (x : List Bool) (first : Bool)
    (q : Fin ((M.k + D.size + 2) + 6)) (hx : 0 < x.length) :
    (markedCfg M D x first q x.length).work (x.length : ℤ) = 0 := by
  dsimp only [markedCfg]
  rw [Function.update_of_ne (by omega)]
  simp [init]

 theorem step_scan_finish (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (s : Fin D.size) (hx : 0 < x.length) (hacc : D.accept s = true) :
    (machine M D).step O (markedCfg M D x first (scan M D s) x.length) =
      markedCfg M D x first (reset M D) (x.length - 1) := by
  have hread := marked_end M D x first (scan M D s) hx
  have hh : ¬ (scan M D s = 1 ∨ scan M D s = 2) := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : scan M D s ≠ 3 := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hu : Function.update (markedCfg M D x first (scan M D s) x.length).work (x.length : ℤ) 0 =
      (markedCfg M D x first (scan M D s) x.length).work := by
    rw [← hread, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D x first (scan M D s) x.length).state
      ((markedCfg M D x first (scan M D s) x.length).work (markedCfg M D x first (scan M D s) x.length).wh)
      ((markedCfg M D x first (scan M D s) x.length).query (markedCfg M D x first (scan M D s) x.length).qh) =
      (reset M D, 0, 0, 0, 1) := by
    change (machine M D).δ (scan M D s) ((markedCfg M D x first (scan M D s) x.length).work (x.length : ℤ)) 0 = _
    rw [hread, delta_scan_end]
    simp [hacc]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  rw [hu]
  simp (disch := omega) [init, min_eq_left, max_eq_left, Function.update_eq_self] <;> omega

 theorem step_reset_walk (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (t : ℕ) (ht : 0 < t) (htx : t < x.length) :
    (machine M D).step O (markedCfg M D x first (reset M D) t) =
      markedCfg M D x first (reset M D) (t - 1) := by
  have hread := marked_read M D x first (reset M D) t ht htx
  have hh : ¬ (reset M D = 1 ∨ reset M D = 2) := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : reset M D ≠ 3 := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hu : Function.update (markedCfg M D x first (reset M D) t).work (t : ℤ)
      (symOf (M.g + 2) (x.getD t false)) = (markedCfg M D x first (reset M D) t).work := by
    rw [← hread, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D x first (reset M D) t).state
      ((markedCfg M D x first (reset M D) t).work (markedCfg M D x first (reset M D) t).wh)
      ((markedCfg M D x first (reset M D) t).query (markedCfg M D x first (reset M D) t).qh) =
      (reset M D, symOf (M.g + 2) (x.getD t false), 0, 0, 1) := by
    change (machine M D).δ (reset M D) ((markedCfg M D x first (reset M D) t).work (t : ℤ)) 0 = _
    rw [hread, delta_reset_bit]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  rw [hu]
  simp (disch := omega) [init, min_eq_left, max_eq_left, Function.update_eq_self] <;> omega

 theorem step_restore (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool) :
    (machine M D).step O (markedCfg M D (b :: xs) b (reset M D) 0) =
      { (machine M D).init (b :: xs) with state := state M D 0 } := by
  have hh : ¬ (reset M D = 1 ∨ reset M D = 2) := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : reset M D ≠ 3 := by
    simp (disch := omega) [reset, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hfirst : ((machine M D).init (b :: xs)).work 0 = symOf (M.g + 2) b := by simp [init]
  have hu : Function.update (markedCfg M D (b :: xs) b (reset M D) 0).work 0 (symOf (M.g + 2) b) =
      ((machine M D).init (b :: xs)).work := by
    dsimp only [markedCfg]
    rw [Function.update_idem, ← hfirst, Function.update_eq_self]
  have hd : (machine M D).δ (markedCfg M D (b :: xs) b (reset M D) 0).state
      ((markedCfg M D (b :: xs) b (reset M D) 0).work (markedCfg M D (b :: xs) b (reset M D) 0).wh)
      ((markedCfg M D (b :: xs) b (reset M D) 0).query (markedCfg M D (b :: xs) b (reset M D) 0).qh) =
      (state M D 0, symOf (M.g + 2) b, 1, 0, 1) := by
    change (machine M D).δ (reset M D) (Function.update ((machine M D).init (b :: xs)).work (0 : ℤ) (if b then markTrue M else markFalse M) (0 : ℤ)) 0 = _
    rw [Function.update_self, delta_reset_marker]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  dsimp only [markedCfg] at hu ⊢
  simp only [Nat.cast_zero]
  rw [hu]
  simp [init, Function.update_eq_self] <;> omega

 theorem core_initial_simulation (M : OTM) (D : DFA) (x : List Bool) :
    CoreEq (machine M D) ({ (machine M D).init x with state := state M D 0 })
      ((simulation M D).cfg (M.init x)) := by
  have hsym : ∀ b, symbol M (symOf M.g b) = symOf (M.g + 2) b := by
    intro b
    cases b <;> apply Fin.ext <;> simp (disch := omega) [symbol, symOf, Nat.mod_eq_of_lt]
  constructor
  · rfl
  · change ((machine M D).init x).work = fun i => symbol M ((M.init x).work i)
    funext i
    dsimp only [init]
    split
    · exact (hsym _).symm
    · rfl
  · rfl
  · change (fun _ : ℤ => (0 : Fin ((M.g + 2) + 3))) = fun i : ℤ => symbol M ((M.init x).query i)
    rfl
  · rfl

 theorem reset_run_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool)
    (hacc : D.accept (D.run (b :: xs)) = true) (j : ℕ) (hj : j ≤ (b :: xs).length - 1) :
    (machine M D).runCfg O (b :: xs) ((b :: xs).length + 1 + j) =
      markedCfg M D (b :: xs) b (reset M D) ((b :: xs).length - 1 - j) := by
  revert hj
  induction j with
  | zero =>
    intro hj
    simp only [Nat.add_zero, Nat.sub_zero]
    rw [OTM.runCfg, Function.iterate_succ_apply']
    change (machine M D).step O ((machine M D).runCfg O (b :: xs) (b :: xs).length) = _
    rw [scan_run_nonempty M D O b xs _ (by simp) (by rfl)]
    simp only [List.take_length]
    exact step_scan_finish M D O (b :: xs) b _ (by simp) hacc
  | succ j ih =>
    intro hj
    rw [show (b :: xs).length + 1 + (j + 1) = ((b :: xs).length + 1 + j) + 1 by omega]
    rw [OTM.runCfg, Function.iterate_succ_apply']
    change (machine M D).step O ((machine M D).runCfg O (b :: xs) ((b :: xs).length + 1 + j)) = _
    rw [ih (by omega)]
    rw [step_reset_walk M D O (b :: xs) b _ (by omega) (by omega)]
    congr 1 <;> omega

 theorem core_prefix_nonempty (M : OTM) (D : DFA) (O : Oracle) (b : Bool) (xs : List Bool)
    (hacc : D.accept (D.run (b :: xs)) = true) :
    CoreEq (machine M D) ((machine M D).runCfg O (b :: xs) (2 * (b :: xs).length + 1))
      ((simulation M D).cfg (M.init (b :: xs))) := by
  have hreset := reset_run_nonempty M D O b xs hacc ((b :: xs).length - 1) (by rfl)
  have htime : (b :: xs).length + 1 + ((b :: xs).length - 1) = 2 * (b :: xs).length := by simp; omega
  rw [htime, Nat.sub_self] at hreset
  rw [OTM.runCfg, Function.iterate_succ_apply']
  change CoreEq (machine M D) ((machine M D).step O ((machine M D).runCfg O (b :: xs) (2 * (b :: xs).length))) _
  rw [hreset, step_restore]
  exact core_initial_simulation M D (b :: xs)

 theorem step_initial_empty (M : OTM) (D : DFA) (O : Oracle) (hacc : D.accept D.start = true) :
    (machine M D).step O ((machine M D).init []) =
      { (machine M D).init [] with state := state M D 0 } := by
  have hh : ¬ (((machine M D).init []).state = 1 ∨ ((machine M D).init []).state = 2) := by
    change ¬ ((0 : Fin ((M.k + D.size + 2) + 6)) = 1 ∨ 0 = 2)
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hq : ((machine M D).init []).state ≠ 3 := by
    change (0 : Fin ((M.k + D.size + 2) + 6)) ≠ 3
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hd : (machine M D).δ ((machine M D).init []).state
      (((machine M D).init []).work ((machine M D).init []).wh)
      (((machine M D).init []).query ((machine M D).init []).qh) =
      (state M D 0, 0, 1, 0, 1) := by
    change (machine M D).δ 0 0 0 = _
    rw [delta_start_empty]
    simp [hacc]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  simp [init, Function.update_eq_self]

 theorem core_prefix (M : OTM) (D : DFA) (O : Oracle) (x : List Bool)
    (hacc : D.accept (D.run x) = true) :
    CoreEq (machine M D) ((machine M D).runCfg O x (2 * x.length + 1))
      ((simulation M D).cfg (M.init x)) := by
  cases x with
  | nil =>
    change CoreEq (machine M D) ((machine M D).step O ((machine M D).init [])) _
    rw [step_initial_empty M D O hacc]
    exact core_initial_simulation M D []
  | cons b xs => exact core_prefix_nonempty M D O b xs hacc

 theorem result_accept (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (t : ℕ)
    (hacc : D.accept (D.run x) = true) :
    (machine M D).result O x (2 * x.length + 1 + t) = M.result O x t :=
  (simulation M D).result_after_core_prefix O x x _ t (core_prefix M D O x hacc)

 theorem step_scan_reject (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (first : Bool)
    (s : Fin D.size) (hx : 0 < x.length) (hacc : D.accept s = false) :
    ((machine M D).step O (markedCfg M D x first (scan M D s) x.length)).state = 2 := by
  have hread := marked_end M D x first (scan M D s) hx
  have hh : ¬ (scan M D s = 1 ∨ scan M D s = 2) := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hq : scan M D s ≠ 3 := by
    simp (disch := omega) [scan, Fin.ext_iff, Nat.mod_eq_of_lt] <;> omega
  have hd : (machine M D).δ (markedCfg M D x first (scan M D s) x.length).state
      ((markedCfg M D x first (scan M D s) x.length).work (markedCfg M D x first (scan M D s) x.length).wh)
      ((markedCfg M D x first (scan M D s) x.length).query (markedCfg M D x first (scan M D s) x.length).qh) =
      (2, 0, 1, 0, 1) := by
    change (machine M D).δ (scan M D s) ((markedCfg M D x first (scan M D s) x.length).work (x.length : ℤ)) 0 = _
    rw [hread, delta_scan_end]
    simp [hacc]
  rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]

 theorem reject_state (M : OTM) (D : DFA) (O : Oracle) (x : List Bool)
    (hacc : D.accept (D.run x) = false) :
    ((machine M D).runCfg O x (x.length + 1)).state = 2 := by
  cases x with
  | nil =>
    change ((machine M D).step O ((machine M D).init [])).state = 2
    have hh : ¬ (((machine M D).init []).state = 1 ∨ ((machine M D).init []).state = 2) := by
      change ¬ ((0 : Fin ((M.k + D.size + 2) + 6)) = 1 ∨ 0 = 2)
      simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
    have hq : ((machine M D).init []).state ≠ 3 := by
      change (0 : Fin ((M.k + D.size + 2) + 6)) ≠ 3
      simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
    have hd : (machine M D).δ ((machine M D).init []).state
        (((machine M D).init []).work ((machine M D).init []).wh)
        (((machine M D).init []).query ((machine M D).init []).qh) = (2, 0, 1, 0, 1) := by
      change (machine M D).δ 0 0 0 = _
      rw [delta_start_empty]
      simp only [DFA.run, List.foldl_nil] at hacc
      simp [hacc]
    rw [normal_step _ _ _ hh hq _ _ _ _ _ hd]
  | cons b xs =>
    rw [OTM.runCfg, Function.iterate_succ_apply']
    change ((machine M D).step O ((machine M D).runCfg O (b :: xs) (b :: xs).length)).state = 2
    rw [scan_run_nonempty M D O b xs _ (by simp) (by rfl)]
    simp only [List.take_length]
    exact step_scan_reject M D O (b :: xs) b _ (by simp) hacc

 theorem result_reject (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (t : ℕ)
    (hacc : D.accept (D.run x) = false) :
    (machine M D).result O x (2 * x.length + 1 + t) = some false := by
  have hre : (machine M D).result O x (x.length + 1) = some false := by
    unfold result
    dsimp only
    rw [reject_state M D O x hacc]
    simp (disch := omega) [Fin.ext_iff, Nat.mod_eq_of_lt]
  have hhalt : ((machine M D).result O x (x.length + 1)).isSome := by rw [hre]; rfl
  rw [result_of_le (machine M D) O x (x.length + 1) _ hhalt (by omega), hre]

 theorem result_precheck (M : OTM) (D : DFA) (O : Oracle) (x : List Bool) (t : ℕ) :
    (machine M D).result O x (2 * x.length + 1 + t) =
      if D.accept (D.run x) then M.result O x t else some false := by
  cases hacc : D.accept (D.run x) with
  | false => simpa only [hacc, Bool.false_eq_true, if_false] using result_reject M D O x t hacc
  | true => simpa only [hacc, if_true] using result_accept M D O x t hacc

end Precheck
end QAdvFew.PoQOracle.OTM

namespace StudentTeacher976.Adaptivity
open QAdvFew.PoQOracle

 theorem delta_regular_restrict {i : ℕ} {L : Language} (hL : L ∈ Delta i)
    (D : OTM.Precheck.DFA) : L ∩ {x | D.accept (D.run x) = true} ∈ Delta i := by
  obtain ⟨O, M, clock, hO, htotal, hdec⟩ := hL
  let bound : Polynomial ℕ := (2 * Polynomial.X + 1) + clock
  have heval : ∀ n, bound.eval n = 2 * n + 1 + clock.eval n := by intro n; simp [bound]
  refine ⟨O, OTM.Precheck.machine M D, bound, hO, ?_, ?_⟩
  · intro s
    rw [heval, OTM.Precheck.result_precheck]
    split
    · exact htotal s
    · rfl
  · intro x
    rw [heval, OTM.Precheck.result_precheck]
    change (x ∈ L ∧ D.accept (D.run x) = true) ↔ _
    rw [hdec]
    cases hb : D.accept (D.run x) <;> simp

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

private def pairNext (q : Fin 8) (b : Bool) : Fin 8 :=
  match q.val with
  | 0 => if b then 1 else 2
  | 1 => 0
  | 2 => if b then 7 else 3
  | 3 => if b then 4 else 5
  | 4 => 3
  | 5 => if b then 7 else 6
  | _ => 7

 def pairDFA : OTM.Precheck.DFA where
  size := 8
  start := 0
  next := pairNext
  accept := fun q => decide (q = 6)

private def component (u : Word) : Word := u.flatMap (fun b => [true, b]) ++ [false, false]

private theorem dead_run (s : Word) : s.foldl pairNext 7 = 7 := by
  induction s with
  | nil => rfl
  | cons b s ih => simpa [pairNext] using ih

private theorem terminal_run (s : Word) : s.foldl pairNext 6 = 6 ↔ s = [] := by
  cases s with
  | nil => simp
  | cons b s => simp [pairNext, dead_run]

private theorem component_run (u rest : Word) (boundary : Bool) :
    (component u ++ rest).foldl pairNext (if boundary then 3 else 0) =
      rest.foldl pairNext (if boundary then 6 else 3) := by
  induction u with
  | nil => cases boundary <;> rfl
  | cons b u ih =>
    cases boundary <;> simpa [component, pairNext, List.append_assoc] using ih

private theorem first_component (s : Word) (boundary : Bool)
    (h : s.foldl pairNext (if boundary then 3 else 0) = 6) :
    ∃ u rest, s = component u ++ rest ∧ rest.foldl pairNext (if boundary then 6 else 3) = 6 := by
  induction s using List.twoStepInduction generalizing boundary with
  | nil => cases boundary <;> norm_num [Fin.ext_iff] at h
  | singleton b => cases boundary <;> cases b <;> norm_num [pairNext, Fin.ext_iff] at h
  | cons_cons b c rest ih ih1 =>
    cases b with
    | false =>
      cases c with
      | false =>
        refine ⟨[], rest, rfl, ?_⟩
        cases boundary <;> simpa [pairNext] using h
      | true =>
        cases boundary <;> simp [pairNext, dead_run] at h
    | true =>
      have hr : rest.foldl pairNext (if boundary then 3 else 0) = 6 := by
        cases boundary <;> simpa [pairNext] using h
      obtain ⟨u, suffix, hu, hrun⟩ := ih boundary hr
      refine ⟨c :: u, suffix, ?_, hrun⟩
      simp [component, hu, List.append_assoc]

 theorem pairDFA_spec (s : Word) : pairDFA.accept (pairDFA.run s) = true ↔ ∃ u v, s = tup [u, v] := by
  change decide (s.foldl pairNext 0 = 6) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨u, rest, hs, hr⟩ := first_component s false h
    obtain ⟨v, suffix, hv, hvend⟩ := first_component rest true hr
    have hend : suffix = [] := terminal_run suffix |>.mp hvend
    refine ⟨u, v, ?_⟩
    simp [hs, hv, hend, component, tup, List.append_assoc]
  · rintro ⟨u, v, rfl⟩
    have heq : tup [u, v] = component u ++ component v := by simp [tup, component, List.append_assoc]
    rw [heq]
    have h := component_run u (component v) false
    change (component u ++ component v).foldl pairNext 0 = 6
    simp only [Bool.false_eq_true, if_false] at h
    rw [h]
    have h' := component_run v [] true
    simpa using h'

private theorem read_component (u rest : Word) : readComponent (component u ++ rest) = some (u, rest) := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [component, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    simpa [readComponent] using congrArg (fun o => o.map (fun p : Word × Word => (b :: p.1, p.2))) ih

 theorem tup_pair_injective {x y u v : Word} (h : tup [x, y] = tup [u, v]) : x = u ∧ y = v := by
  have hcode : ∀ a b : Word, tup [a, b] = component a ++ tup [b] := by
    intro a b
    simp [tup, component, List.append_assoc]
  have hfirst := congrArg readComponent h
  rw [hcode, hcode, read_component, read_component] at hfirst
  have hpair : x = u ∧ tup [y] = tup [v] := by simpa using hfirst
  have hsingle : ∀ a : Word, tup [a] = component a ++ [] := by intro a; simp [tup, component]
  have hsecond := congrArg readComponent hpair.2
  rw [hsingle, hsingle, read_component, read_component] at hsecond
  exact ⟨hpair.1, congrArg Prod.fst (Option.some.inj hsecond)⟩

end StudentTeacher976.Adaptivity

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

 theorem oracle_false_mem_delta (i : ℕ) (O : Oracle) (hO : {s | O s = true} ∈ Sigma i) :
    {s | O s = false} ∈ Delta i := by
  refine ⟨O, OTM.queryMachine true, Polynomial.X + 3, hO, ?_, ?_⟩
  · intro x
    simpa [OTM.queryMachine_result] using congrArg Option.isSome (OTM.queryMachine_result true O x)
  · intro x
    simp only [Set.mem_setOf_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat,
      OTM.queryMachine_result, if_true, Option.some.injEq]
    cases O x <;> simp

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

 theorem sigma_one_witness (L : Language) (hL : L ∈ Sigma 1) :
    Nonempty (WitnessPresentation 0 L) := by
  obtain ⟨V, clock, ps, hps, htotal, hdec⟩ := hL
  cases ps with
  | nil => simp at hps
  | cons p ps =>
    have hnil : ps = [] := by simpa using hps
    subst ps
    let Lang : Language := {s | V.result (fun _ => false) s (clock.eval s.length) = some true}
    have hLang : Lang ∈ Delta 0 := by
      refine ⟨fun _ => false, V, clock, ?_, htotal, ?_⟩
      · simpa using empty_mem_sigma 0
      · intro x; rfl
    have hreg := delta_regular_restrict hLang pairDFA
    refine ⟨{ length := p
              test := fun x y => V.result (fun _ => false) (tup [x, y])
                (clock.eval (tup [x, y]).length) = some true
              efficient := ?_
              represents := ?_ }⟩
    · have hset : {s | ∃ x y, s = tup [x, y] ∧
          V.result (fun _ => false) (tup [x, y]) (clock.eval (tup [x, y]).length) = some true} =
          Lang ∩ {x | pairDFA.accept (pairDFA.run x) = true} := by
        ext s
        change (∃ x y, s = tup [x, y] ∧ _) ↔
          (V.result (fun _ => false) s (clock.eval s.length) = some true ∧ _)
        simp only [Set.mem_setOf_eq]
        rw [pairDFA_spec]
        constructor
        · rintro ⟨x, y, rfl, hxy⟩
          exact ⟨hxy, x, y, rfl⟩
        · rintro ⟨hV, x, y, hxy⟩
          refine ⟨x, y, hxy, ?_⟩
          rwa [← hxy]
      rw [hset]
      exact hreg
    · intro x
      simpa [AvgPHETH.AltLen] using hdec x

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity

 theorem witness_from_residual (i : ℕ) (L : Language) (p : Polynomial ℕ)
    (ps : List (Polynomial ℕ)) (V : OTM) (clock : Polynomial ℕ)
    (hLrep : ∀ x : Word, x ∈ L ↔ ∃ y : Word, y.length = p.eval x.length ∧
      AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true))
    (hres : {s | ∃ x y : Word, s = tup [x, y] ∧
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true)} ∈ Sigma i) :
    Nonempty (WitnessPresentation i L) := by
  classical
  let A : Language := {s | ∃ x y : Word, s = tup [x, y] ∧
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true)}
  let O : Oracle := fun s => decide (s ∈ A)
  have hOeq : {s | O s = true} = A := by ext s; simp [O]
  have hO : {s | O s = true} ∈ Sigma i := by rw [hOeq]; exact hres
  have hpair : ∀ x y : Word, O (tup [x, y]) = true ↔
      ¬ AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true) := by
    intro x y
    change decide (∃ a b : Word, tup [x, y] = tup [a, b] ∧ _) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, hn⟩
      obtain ⟨ha, hb⟩ := tup_pair_injective hab
      simpa [← ha, ← hb] using hn
    · intro hn; exact ⟨x, y, rfl, hn⟩
  have hfalse : ∀ x y : Word, O (tup [x, y]) = false ↔
      AvgPHETH.AltLen (ps.map fun b => b.eval x.length) false
        (fun ys => V.result (fun _ => false) (tup (x :: y :: ys))
          (clock.eval (tup (x :: y :: ys)).length) = some true) := by
    intro x y
    have hbool : O (tup [x, y]) = false ↔ ¬ O (tup [x, y]) = true := by cases O (tup [x, y]) <;> simp
    rw [hbool, hpair, not_not]
  have hreg := delta_regular_restrict (oracle_false_mem_delta i O hO) pairDFA
  refine ⟨{ length := p
            test := fun x y => O (tup [x, y]) = false
            efficient := ?_
            represents := ?_ }⟩
  · have hset : {s | ∃ x y : Word, s = tup [x, y] ∧ O (tup [x, y]) = false} =
        {s | O s = false} ∩ {s | pairDFA.accept (pairDFA.run s) = true} := by
      ext s
      change (∃ x y : Word, s = tup [x, y] ∧ _) ↔ (O s = false ∧ _)
      simp only [Set.mem_setOf_eq]
      rw [pairDFA_spec]
      constructor
      · rintro ⟨x, y, rfl, hxy⟩; exact ⟨hxy, x, y, rfl⟩
      · rintro ⟨hs, x, y, hxy⟩
        exact ⟨x, y, hxy, by rwa [← hxy]⟩
    rw [hset]
    exact hreg
  · intro x
    rw [hLrep x]
    apply exists_congr
    intro y
    exact and_congr_right fun _ => (hfalse x y).symm

end StudentTeacher976.Adaptivity

set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (L : Language)
    (hL : L ∈ StudentTeacher976.Adaptivity.Sigma (i + 1)) :
    Nonempty (WitnessPresentation i L) := by
  cases i with
  | zero => exact sigma_one_witness L hL
  | succ i =>
    obtain ⟨V, clock, ps, hps, htotal, hdec⟩ := hL
    cases ps with
    | nil => simp at hps
    | cons p ps =>
      apply witness_from_residual (i + 1) L p ps V clock
      · intro x
        simpa [AvgPHETH.AltLen] using hdec x
      · exact residual_quantifier_padding (i + 1) (by omega) V clock ps (by simpa using hps) htotal
