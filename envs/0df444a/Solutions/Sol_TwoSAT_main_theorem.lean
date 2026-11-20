-- Prove2me | solution 1 for TwoSAT.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-20T01:53:53.471599+00:00
-- url     : https://prove2.me/submissions/682b257f-7c73-42d0-8f07-532c0977d367

import Definitions.Def_YoshidaTwoSAT_QueryModel
import Mathlib.Data.List.Nodup
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_TwoSAT_exact_tester

namespace TwoSAT
def MainClaim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d,
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F)

end TwoSAT

section

namespace TwoSAT.Reduction

variable {V : Type}

/-- The second coordinate distinguishes original (false) and auxiliary (true) variables. -/
def liftLit (a : Literal V) : Literal (V × Bool) := ⟨(a.var, false), a.sign⟩

def gadget (a : Literal V) (s : Bool) : Clause (V × Bool) :=
  .pair (liftLit a) ⟨(a.var, true), s⟩

def expand : Clause V → List (Clause (V × Bool))
  | .unit a => [gadget a true, gadget a false]
  | .taut _ => []
  | .pair a b => [.pair (liftLit a) (liftLit b)]

def reduce (F : List (Clause V)) := F.flatMap expand

def restrict (t : V × Bool → Bool) (x : V) := t (x, false)

theorem clauseLoss (t : V × Bool → Bool) (c : Clause V) :
    loss t (expand c) = (if c.eval (restrict t) then 0 else 1) := by
  cases c with
  | taut => rfl
  | pair a b => simp [expand, loss, Clause.eval, Literal.eval, liftLit, restrict]
  | unit a =>
    rcases a with ⟨x, s⟩
    cases ho : t (x, false) <;> cases hz : t (x, true) <;> cases s <;>
      simp [expand, gadget, liftLit, loss, restrict, Clause.eval, Literal.eval, ho, hz]

private theorem loss_append (t : V → Bool) (F G : List (Clause V)) :
    loss t (F ++ G) = loss t F + loss t G := by
  induction F with
  | nil => simp [loss]
  | cons c cs ih => simp [loss, ih, Nat.add_assoc]

theorem loss_reduce (t : V × Bool → Bool) (F : List (Clause V)) :
    loss t (reduce F) = loss (restrict t) F := by
  induction F with
  | nil => rfl
  | cons c cs ih =>
    change loss t (expand c ++ reduce cs) = _
    simp only [loss_append, clauseLoss, ih, loss]

theorem attainableLosses (F : List (Clause V)) :
    Set.range (fun t => loss t (reduce F)) = Set.range (fun t => loss t F) := by
  ext k
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨restrict t, (loss_reduce t F).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨fun v => t v.1, loss_reduce _ F⟩

theorem distance_reduce (F : List (Clause V)) : distance (reduce F) = distance F := by
  unfold distance
  rw [attainableLosses]

theorem satisfiable_reduce (F : List (Clause V)) : Satisfiable (reduce F) ↔ Satisfiable F := by
  change 0 ∈ Set.range (fun t => loss t (reduce F)) ↔ 0 ∈ Set.range (fun t => loss t F)
  rw [attainableLosses]

theorem far_reduce (F : List (Clause V)) (ε : ℝ) (d n : ℕ)
    (h : ε * d * n ≤ distance F) :
    ε / 4 * (2 * (d : ℝ)) * (2 * (n : ℝ)) ≤ distance (reduce F) := by
  rw [distance_reduce]
  linarith only [h]

/-- Destination slots have indices (original slot, second half). -/
def slot (aux second : Bool) : Option (Clause V) → Option (Clause (V × Bool))
  | none | some (.taut _) => none
  | some (.unit a) => some (gadget a (!second))
  | some (.pair a b) =>
    if aux || second then none else some (.pair (liftLit a) (liftLit b))

/-- Each call consults one original incidence slot. -/
def reducedOracle {I : Type} (oracle : V → I → Option (Clause V))
    (v : V × Bool) (i : I × Bool) : Option (Clause (V × Bool)) :=
  slot v.2 i.2 (oracle v.1 i.1)

theorem slot_origin {aux second : Bool} {input : Option (Clause V)} {c}
    (h : slot aux second input = some c) : ∃ d, input = some d ∧ c ∈ expand d := by
  cases input with
  | none => simp [slot] at h
  | some d =>
    refine ⟨d, rfl, ?_⟩
    cases d <;> cases aux <;> cases second <;> simp_all [slot, expand]

/-- Clauses retained from a rejecting transcript can be traced back to an
unsatisfiable set of original clauses. -/
theorem unsat_origins {F : List (Clause V)} {G : List (Clause (V × Bool))}
    (origin : ∀ c ∈ G, c ∈ reduce F) (bad : ¬ Satisfiable G) : ¬ Satisfiable F := by
  intro sat
  obtain ⟨t, ht⟩ := (satisfiable_reduce F).mpr sat
  apply bad
  exact ⟨t, (loss_eq_zero_iff t G).mpr fun c hc =>
    (loss_eq_zero_iff t (reduce F)).mp ht c (origin c hc)⟩

end TwoSAT.Reduction

end

section

namespace TwoSAT.Reduction

variable {V I : Type}

/-- The tags of a replacement clause identify its source and its half-slot. -/
private def origin (c : Clause (V × Bool)) : Option (Clause V × Bool) :=
  match c with
  | .pair a b =>
    let u : Literal V := ⟨a.var.1, a.sign⟩
    if b.var.2 then some (.unit u, !b.sign)
    else some (.pair u ⟨b.var.1, b.sign⟩, false)
  | _ => none

private theorem origin_expand {c : Clause V} {e} (h : e ∈ expand c) :
    ∃ s, origin e = some (c, s) := by
  cases c with
  | taut => simp [expand] at h
  | unit a =>
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  | pair a b =>
    simp only [expand, List.mem_singleton] at h
    subst e
    exact ⟨false, rfl⟩

theorem nodup_reduce {F : List (Clause V)} (hF : F.Nodup) : (reduce F).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro c _
    cases c <;> simp [expand, gadget]
  · apply hF.imp
    intro a b hn e ha hb
    obtain ⟨i, hi⟩ := origin_expand ha
    obtain ⟨j, hj⟩ := origin_expand hb
    exact hn (congrArg Prod.fst (Option.some.inj (hi.symm.trans hj)))

private theorem slot_spec {x : V} {aux s : Bool} {c : Clause V} {e}
    (hc : c.incident x) (hs : slot aux s (some c) = some e) :
    e ∈ expand c ∧ e.incident (x, aux) ∧ origin e = some (c, s) := by
  cases c with
  | taut => simp [slot] at hs
  | unit a =>
    change x = a.var at hc
    subst x
    cases aux <;> cases s <;> simp [slot] at hs <;> subst e <;> simp [expand, Clause.incident, gadget, liftLit, origin]
  | pair a b =>
    cases aux <;> cases s <;> simp [slot] at hs
    subst e
    simpa [expand, Clause.incident, liftLit, origin] using hc

private theorem slot_exists {x : V} {aux : Bool} {c : Clause V} {e}
    (he : e ∈ expand c) (hx : e.incident (x, aux)) :
    c.incident x ∧ ∃ s, slot aux s (some c) = some e := by
  cases c with
  | taut => simp [expand] at he
  | unit a =>
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      cases aux <;> simp_all [Clause.incident, liftLit, gadget, slot]
  | pair a b =>
    simp only [expand, List.mem_singleton] at he
    subst e
    cases aux <;> simp_all [Clause.incident, liftLit, slot]

/-- Every non-null answer is an incident clause of the reduced formula. -/
theorem oracle_sound {F : List (Clause V)} {o : V → I → Option (Clause V)}
    (hs : ∀ x i c, o x i = some c → c ∈ F ∧ c.incident x)
    (v : V × Bool) (i : I × Bool) (e)
    (h : reducedOracle o v i = some e) : e ∈ reduce F ∧ e.incident v := by
  unfold reducedOracle at h
  cases hi : o v.1 i.1 with
  | none => simp [hi, slot] at h
  | some c =>
    rw [hi] at h
    obtain ⟨hm, hx⟩ := hs _ _ _ hi
    obtain ⟨he, hv, _⟩ := slot_spec hx h
    exact ⟨List.mem_flatMap.mpr ⟨c, hm, he⟩, hv⟩

/-- Each incident output clause appears exactly once at the queried variable. -/
theorem oracle_coverage {F : List (Clause V)} {o : V → I → Option (Clause V)}
    (hs : ∀ x i c, o x i = some c → c ∈ F ∧ c.incident x)
    (hc : ∀ x c, c ∈ F → c.incident x → ∃! i, o x i = some c)
    (v : V × Bool) (e) (he : e ∈ reduce F) (hv : e.incident v) :
    ∃! i, reducedOracle o v i = some e := by
  obtain ⟨c, hm, hce⟩ := List.mem_flatMap.mp he
  obtain ⟨hx, s, hslot⟩ := slot_exists hce hv
  obtain ⟨i, hi, unique⟩ := hc v.1 c hm hx
  refine ⟨(i, s), by simpa [reducedOracle, hi] using hslot, ?_⟩
  rintro ⟨j, t⟩ hj
  change slot v.2 t (o v.1 j) = some e at hj
  cases ho : o v.1 j with
  | none => simp [ho, slot] at hj
  | some d =>
    rw [ho] at hj
    have h1 := (slot_spec hx hslot).2.2
    have h2 := (slot_spec (hs _ _ _ ho).2 hj).2.2
    have hh := Option.some.inj (h2.symm.trans h1)
    have hd := congrArg Prod.fst hh
    have ht := congrArg Prod.snd hh
    exact Prod.ext (unique j (by simpa using ho.trans (congrArg some hd))) ht

end TwoSAT.Reduction

end

section

namespace TwoSAT

variable {V W : Type}

def Literal.rename (f : V → W) (a : Literal V) : Literal W := ⟨f a.var, a.sign⟩

def Clause.rename (f : V → W) : Clause V → Clause W
  | .unit a => .unit (a.rename f)
  | .taut x => .taut (f x)
  | .pair a b => .pair (a.rename f) (b.rename f)

@[simp] theorem rename_eval (f : V → W) (t : W → Bool) (c : Clause V) :
    (c.rename f).eval t = c.eval (t ∘ f) := by cases c <;> rfl

@[simp] theorem rename_loss (f : V → W) (F : List (Clause V)) (t : W → Bool) :
    loss t (F.map (Clause.rename f)) = loss (t ∘ f) F := by
  induction F with
  | nil => rfl
  | cons c cs ih => simp [loss, ih]

theorem rename_distance (e : V ≃ W) (F : List (Clause V)) :
    distance (F.map (Clause.rename e)) = distance F := by
  unfold distance
  congr 1
  ext k
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t ∘ e, (rename_loss e F t).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t ∘ e.symm, ?_⟩
    simp [Function.comp_def]

namespace Reduction

/-- Number each original variable first, then its auxiliary copy. The same
bijection labels the two sets of incidence slots. -/
def labels (n : ℕ) : (Fin n × Bool) ≃ Fin (n + n) where
  toFun v := finSumFinEquiv (if v.2 then Sum.inr v.1 else Sum.inl v.1)
  invFun i := (finSumFinEquiv.symm i).elim (fun x => (x, false)) (fun x => (x, true))
  left_inv := by rintro ⟨x, b⟩; cases b <;> simp only [Equiv.symm_apply_apply] <;> rfl
  right_inv := by
    intro i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective i
    cases y <;> simp only [Equiv.symm_apply_apply] <;> rfl

def doubledAnswer {n} (aux second : Bool) (a : Answer n) : Answer (n + n) :=
  (slot aux second a).map (Clause.rename (labels n))

def doubledOracle {n d} (o : Oracle n d) : Oracle (n + n) (d + d) :=
  fun x i =>
    let v := (labels n).symm x
    let j := (labels d).symm i
    doubledAnswer v.2 j.2 (o v.1 j.1)

private theorem rename_back (f : V ≃ W) (c : Clause V) :
    (c.rename f).rename f.symm = c := by
  cases c <;> simp [Clause.rename, Literal.rename]

theorem rename_inj (f : V ≃ W) : Function.Injective (Clause.rename f) := by
  intro a b h
  simpa only [rename_back] using congrArg (Clause.rename f.symm) h

theorem rename_incident (f : V ≃ W) (c : Clause V) (x : V) :
    (c.rename f).incident (f x) ↔ c.incident x := by
  cases c <;> simp [Clause.rename, Literal.rename, Clause.incident]

theorem expanded_pair {n d} (F : Input n d) {c} (hc : c ∈ reduce F.formula) :
    ∃ a b, c.rename (labels n) = .pair a b ∧ a.var < b.var := by
  obtain ⟨u, hu, he⟩ := List.mem_flatMap.mp hc
  have hcan := F.canonical u hu
  cases u with
  | taut => simp [expand] at he
  | unit l =>
    simp only [expand, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> refine ⟨_, _, rfl, ?_⟩ <;>
      change l.var.val < n + l.var.val <;> omega
  | pair a b =>
    simp only [expand, List.mem_singleton] at he
    subst c
    exact ⟨_, _, rfl, hcan⟩

theorem query_label {n d} (F : Input n d) (v : Fin n × Bool) (i : Fin d × Bool) :
    doubledOracle F.oracle (labels n v) (labels d i) =
      (reducedOracle F.oracle v i).map (Clause.rename (labels n)) := by
  simp [doubledOracle, doubledAnswer, reducedOracle]

def doubledInput {n d} (F : Input n d) : Input (n + n) (d + d) where
  formula := (reduce F.formula).map (Clause.rename (labels n))
  distinct := (nodup_reduce F.distinct).map (rename_inj _)
  canonical := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨a, b, hg, hlt⟩ := expanded_pair F he
    rw [hg]
    exact hlt
  oracle := doubledOracle F.oracle
  sound := by
    intro x i c h
    obtain ⟨v, rfl⟩ := (labels n).surjective x
    obtain ⟨j, rfl⟩ := (labels d).surjective i
    rw [query_label] at h
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hf, hx⟩ := oracle_sound F.sound v j e he
    exact ⟨List.mem_map.mpr ⟨e, hf, rfl⟩, (rename_incident _ _ _).mpr hx⟩
  coverage := by
    intro x c hm hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    obtain ⟨v, rfl⟩ := (labels n).surjective x
    have hv := (rename_incident _ _ _).mp hx
    obtain ⟨j, hj, hun⟩ := oracle_coverage F.sound F.coverage v e he hv
    refine ⟨labels d j, by simp [query_label, hj], ?_⟩
    intro i hi
    obtain ⟨k, rfl⟩ := (labels d).surjective i
    rw [query_label] at hi
    obtain ⟨e', h', heq⟩ := Option.map_eq_some_iff.mp hi
    have := rename_inj (labels n) heq
    subst e'
    exact congrArg (labels d) (hun k h')

theorem doubled_exact {n d} (F : Input n d) : Exact (doubledInput F) := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact expanded_pair F he

theorem doubled_distance {n d} (F : Input n d) :
    distance (doubledInput F).formula = distance F.formula :=
  (rename_distance _ _).trans (distance_reduce _)

theorem doubled_satisfiable {n d} (F : Input n d) (hs : Satisfiable F.formula) :
    Satisfiable (doubledInput F).formula := by
  obtain ⟨t, ht⟩ := (satisfiable_reduce _).mpr hs
  refine ⟨t ∘ (labels n).symm, ?_⟩
  simpa [doubledInput, Function.comp_def] using ht

/-- Compile a decision tree on the doubled incidence table into one on the
original labels, preserving the query budget in the type. -/
def simulate {n d} : {q : ℕ} → Tree (n + n) (d + d) q → Tree n d q
  | _, .leaf b => .leaf b
  | _, .ask x i next =>
    let v := (labels n).symm x
    let j := (labels d).symm i
    .ask v.1 j.1 (fun a => simulate (next (doubledAnswer v.2 j.2 a)))

theorem run_simulate {n d q} (o : Oracle n d) (tree : Tree (n + n) (d + d) q) :
    (simulate tree).run o = tree.run (doubledOracle o) := by
  induction tree with
  | leaf => rfl
  | ask x i next ih => apply ih

theorem simulate_distribution {n d q} (o : Oracle n d)
    (p : PMF (Tree (n + n) (d + d) q)) :
    (p.map simulate).map (fun t => t.run o) = p.map (fun t => t.run (doubledOracle o)) := by
  rw [PMF.map_comp]
  simp only [Function.comp_def, run_simulate]

end Reduction
end TwoSAT

end

section

namespace TwoSAT.Reduction

/-- The query-complexity assertion of §6.3 restricted to E2SAT. -/
def ExactClaim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d, Exact F →
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F)

private theorem scale_bound {n k : ℕ} (hn : 1 ≤ n) {C a : ℝ} (hC : 0 < C) :
    C * ((n + n : ℕ) : ℝ) ^ a * (1 + Real.log ((n + n : ℕ) : ℝ)) ^ k ≤
      (C * 2 ^ a * (1 + Real.log 2) ^ k) * (n : ℝ) ^ a * (1 + Real.log n) ^ k := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hlog := Real.log_nonneg hn'
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hle : 1 + (Real.log 2 + Real.log n) ≤ (1 + Real.log 2) * (1 + Real.log n) := by
    nlinarith [mul_nonneg htwo hlog]
  have hh : ((n + n : ℕ) : ℝ) = 2 * n := by push_cast; ring
  rw [hh, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le,
    Real.log_mul (by norm_num) hn0.ne']
  calc
    _ ≤ C * (2 ^ a * (n : ℝ) ^ a) * ((1 + Real.log 2) * (1 + Real.log n)) ^ k := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Section 6.4 transfers the exact-clause tester to arbitrary bounded-degree
2CNFs, including unit clauses, tautologies and arbitrary null-slot locations. -/
theorem mainClaim_of_exact (h : ExactClaim) : MainClaim := by
  intro d hd ε ν hε hν hν'
  obtain ⟨C, k, hC, H⟩ := h (d + d) (by omega) (ε / 4) ν (by positivity) hν hν'
  let a := (1 : ℝ) / 2 + ν
  refine ⟨C * 2 ^ a * (1 + Real.log 2) ^ k, k, ?_, ?_⟩
  · have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  intro n hn
  obtain ⟨q, alg, hq, htest⟩ := H (n + n) (by omega)
  refine ⟨q, alg.map simulate, hq.trans (scale_bound hn hC), ?_⟩
  intro F
  have result := htest (doubledInput F) (doubled_exact F)
  have prob : rejection (alg.map simulate) F = rejection alg (doubledInput F) :=
    congrArg (fun μ : PMF Bool => μ true) (simulate_distribution F.oracle alg)
  rw [prob]
  refine ⟨fun hs => result.1 (doubled_satisfiable F hs), ?_⟩
  intro hfar
  apply result.2
  rw [doubled_distance]
  push_cast
  linarith only [hfar]

end TwoSAT.Reduction

end

open TwoSAT in
theorem solution :
  ∀ (d : ℕ), 1 ≤ d → ∀ ε ν : ℝ, 0 < ε → 0 < ν → ν < 1 / 2 →
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ (q : ℕ) (alg : PMF (Tree n d q)),
        (q : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ν) * (1 + Real.log n) ^ k ∧
        ∀ F : Input n d,
          (Satisfiable F.formula → rejection alg F = 0) ∧
          (ε * d * n ≤ distance F.formula → (2 / 3 : ENNReal) ≤ rejection alg F) := TwoSAT.Reduction.mainClaim_of_exact TwoSAT.exact_tester
