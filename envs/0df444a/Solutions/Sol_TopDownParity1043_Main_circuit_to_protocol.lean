-- Prove2me | solution 1 for TopDownParity1043.Main.circuit_to_protocol
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:51:17.962196+00:00
-- url     : https://prove2.me/submissions/4259c8cd-62f0-4268-9572-5dd74f0ed6b7

import Mathlib
import Definitions.Def_TopDownParity1043_Main_KW

set_option autoImplicit false
open TopDownParity1043.Main
open ParityBarrier563.Trilinear

private theorem all_ofFn_true {k : ℕ} (f : Fin k → Bool) :
    (List.ofFn f).all id = true ↔ ∀ i, f i = true := by simp

private theorem any_ofFn_false {k : ℕ} (f : Fin k → Bool) :
    (List.ofFn f).any id = false ↔ ∀ i, f i = false := by simp

private theorem gate_protocol {V : Type} (k m : ℕ) (hk : k ≤ 2 ^ m)
    (f : Fin k → BoolFn V) (dep : Fin k → ℕ)
    (hP : ∀ i, ∃ P : Protocol (V → Bool) (V → Bool) V,
      P.rounds ≤ dep i ∧ P.CostBounded m ∧
        SolvesKW P {x | f i x = false} {y | f i y = true})
    (kind : GateKind) :
    ∃ P : Protocol (V → Bool) (V → Bool) V,
      P.rounds ≤ 1 + Finset.univ.sup dep ∧ P.CostBounded m ∧
        SolvesKW P
          {x | Circuit.applyGate kind (List.ofFn (fun i => f i x)) = false}
          {y | Circuit.applyGate kind (List.ofFn (fun i => f i y)) = true} := by
  classical
  by_cases hk0 : k = 0
  · subst k
    refine ⟨.leaf none, by simp [Protocol.rounds], trivial, ?_⟩
    intro x hx y hy
    cases kind <;> simp [Circuit.applyGate] at hx hy
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    choose P hdep hcost hsolve using hP
    have hdepAll : Finset.univ.sup (fun i => (P i).rounds) ≤ Finset.univ.sup dep := by
      apply Finset.sup_le
      intro i hi
      exact (hdep i).trans (Finset.le_sup hi)
    cases kind with
    | and =>
      let msg : (V → Bool) → Fin k := fun x =>
        if h : ∃ i, f i x = false then Classical.choose h else ⟨0, hkpos⟩
      refine ⟨.alice k msg P, Nat.add_le_add_left hdepAll 1, ⟨hk, hcost⟩, ?_⟩
      intro x hx y hy
      have hfalse : ∃ i, f i x = false := by
        by_contra h
        have hall : ∀ i, f i x = true := by
          intro i
          have hi : f i x ≠ false := fun hi => h ⟨i,hi⟩
          cases hix : f i x <;> simp_all
        have htrue := (all_ofFn_true (fun i => f i x)).mpr hall
        simp only [Circuit.applyGate, Set.mem_setOf_eq] at hx
        rw [htrue] at hx
        exact Bool.noConfusion hx
      have hmsg : f (msg x) x = false := by
        dsimp [msg]
        rw [dif_pos hfalse]
        exact Classical.choose_spec hfalse
      have hyall : ∀ i, f i y = true :=
        (all_ofFn_true (fun i => f i y)).mp hy
      exact hsolve (msg x) x hmsg y (hyall (msg x))
    | or =>
      let msg : (V → Bool) → Fin k := fun y =>
        if h : ∃ i, f i y = true then Classical.choose h else ⟨0, hkpos⟩
      refine ⟨.bob k msg P, Nat.add_le_add_left hdepAll 1, ⟨hk, hcost⟩, ?_⟩
      intro x hx y hy
      have htrue : ∃ i, f i y = true := by
        by_contra h
        have hall : ∀ i, f i y = false := by
          intro i
          have hi : f i y ≠ true := fun hi => h ⟨i,hi⟩
          cases hiy : f i y <;> simp_all
        have hfalse := (any_ofFn_false (fun i => f i y)).mpr hall
        simp only [Circuit.applyGate, Set.mem_setOf_eq] at hy
        rw [hfalse] at hy
        exact Bool.noConfusion hy
      have hmsg : f (msg y) y = true := by
        dsimp [msg]
        rw [dif_pos htrue]
        exact Classical.choose_spec htrue
      have hxall : ∀ i, f i x = false :=
        (any_ofFn_false (fun i => f i x)).mp hx
      exact hsolve (msg y) x (hxall (msg y)) y hmsg

private theorem prefix_protocol {V : Type} (C : Circuit V) (m : ℕ)
    (hfan : ∀ i, (C.inputs i).length ≤ 2 ^ m) :
    ∀ g : ℕ, ∀ hg : g ≤ C.size, ∀ a : Node V g,
      ∃ P : Protocol (V → Bool) (V → Bool) V,
        P.rounds ≤ Node.depth (C.gateDepthsUpTo g hg) a ∧ P.CostBounded m ∧
          SolvesKW P {x | Node.eval x (C.gateValsUpTo x g hg) a = false}
            {y | Node.eval y (C.gateValsUpTo y g hg) a = true} := by
  classical
  intro g
  induction g with
  | zero =>
    intro hg a
    cases a with
    | lit v pos =>
      refine ⟨.leaf (some v), by simp [Protocol.rounds, Node.depth], trivial, ?_⟩
      intro x hx y hy
      refine ⟨v, rfl, ?_⟩
      cases pos <;> cases hxv : x v <;> cases hyv : y v <;>
        simp_all [Node.eval]
    | const c =>
      refine ⟨.leaf none, by simp [Protocol.rounds, Node.depth], trivial, ?_⟩
      intro x hx y hy
      cases c <;> simp [Node.eval] at hx hy
    | gate j => exact Fin.elim0 j
  | succ g ih =>
    intro hg a
    have hg' : g ≤ C.size := Nat.le_of_succ_le hg
    cases a with
    | lit v pos =>
      refine ⟨.leaf (some v), by simp [Protocol.rounds, Node.depth], trivial, ?_⟩
      intro x hx y hy
      refine ⟨v, rfl, ?_⟩
      cases pos <;> cases hxv : x v <;> cases hyv : y v <;>
        simp_all [Node.eval]
    | const c =>
      refine ⟨.leaf none, by simp [Protocol.rounds, Node.depth], trivial, ?_⟩
      intro x hx y hy
      cases c <;> simp [Node.eval] at hx hy
    | gate j =>
      revert j
      apply Fin.lastCases
      · let l := C.inputs ⟨g, hg⟩
        let dep : Fin l.length → ℕ := fun i =>
          Node.depth (C.gateDepthsUpTo g hg') (l.get i)
        let f : Fin l.length → BoolFn V := fun i x =>
          Node.eval x (C.gateValsUpTo x g hg') (l.get i)
        have hchild : ∀ i, ∃ P : Protocol (V → Bool) (V → Bool) V,
            P.rounds ≤ dep i ∧ P.CostBounded m ∧
              SolvesKW P {x | f i x = false} {y | f i y = true} := by
          intro i
          exact ih hg' (l.get i)
        obtain ⟨P, hdep, hcost, hsolve⟩ :=
          gate_protocol l.length m (hfan ⟨g,hg⟩) f dep hchild (C.kind ⟨g,hg⟩)
        have hlist : ∀ x : V → Bool, List.ofFn (fun i => f i x) =
            l.map (Node.eval x (C.gateValsUpTo x g hg')) := by
          intro x
          change List.ofFn ((Node.eval x (C.gateValsUpTo x g hg')) ∘ l.get) = _
          rw [← List.map_ofFn, List.ofFn_get]
        refine ⟨P, ?_, hcost, ?_⟩
        · simp only [Node.depth, Circuit.gateDepthsUpTo, Fin.lastCases_last]
          apply hdep.trans
          apply Nat.add_le_add_left
          apply Finset.sup_le
          intro i hi
          exact List.le_max_of_le
            (List.mem_map.mpr ⟨l.get i, List.get_mem l i, rfl⟩) le_rfl
        · intro x hx y hy
          apply hsolve x
          · simpa only [hlist, l, Node.eval,
              Circuit.gateValsUpTo, Fin.lastCases_last] using hx
          · simpa only [hlist, l, Node.eval,
              Circuit.gateValsUpTo, Fin.lastCases_last] using hy
      · intro j
        obtain ⟨P, hd, hc, hs⟩ := ih hg' (.gate j)
        refine ⟨P, ?_, hc, ?_⟩
        · simpa only [Node.depth, Circuit.gateDepthsUpTo, Fin.lastCases_castSucc] using hd
        · intro x hx y hy
          apply hs x
          · simpa only [Node.eval, Circuit.gateValsUpTo, Fin.lastCases_castSucc] using hx
          · simpa only [Node.eval, Circuit.gateValsUpTo, Fin.lastCases_castSucc] using hy

theorem circuit_to_protocol {V : Type} (C : Circuit V) (d m : ℕ)
    (hd : C.depth ≤ d) (hf : maxFanIn C ≤ 2 ^ m) : HasKWProtocol C.eval d m := by
  have hfan : ∀ i, (C.inputs i).length ≤ 2 ^ m := by
    intro i
    exact (Finset.le_sup (Finset.mem_univ i)).trans hf
  obtain ⟨P, hdepth, hcost, hsolve⟩ := prefix_protocol C m hfan C.size le_rfl C.output
  exact ⟨P, hdepth.trans hd, hcost, hsolve⟩

theorem solution (n d m : ℕ) (f : BoolFn (Fin n)) :
    (∃ C : Circuit (Fin n), C.depth ≤ d ∧ maxFanIn C ≤ 2 ^ m ∧ C.Computes f) →
      HasKWProtocol f d m := by
  rintro ⟨C, hd, hf, hcomp⟩
  have heval : C.eval = f := funext hcomp
  rw [← heval]
  exact circuit_to_protocol C d m hd hf
