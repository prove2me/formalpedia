-- Prove2me | solution 1 for SemAC02.proposition_8_3_lift_unsat
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T05:58:51.611677+00:00
-- url     : https://prove2.me/submissions/49720506-97cb-4823-bba9-60cd102da1da

import Definitions.Def_SemAC02_IsGadget
import Definitions.Def_SemAC02_lift

open SemAC02

private theorem eval_rename {V W : Type} (A : Circ V) (f : V → W) (X : W → Bool) :
    (A.rename f).eval X = A.eval (fun v => X (f v)) := by
  cases A with
  | const b => simp [Circ.rename, Circ.flip, Circ.eval]
  | lit v b => simp [Circ.rename, Circ.eval]
  | and cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X
  | or cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X
  | xor cs =>
    simp only [Circ.rename, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_rename c f X

termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

private theorem eval_flip {V : Type} (A : Circ V) (X : V → Bool) :
    A.flip.eval X = A.eval (fun v => !X v) := by
  cases A with
  | const b => simp [Circ.rename, Circ.flip, Circ.eval]
  | lit v b => cases b <;> simp [Circ.flip, Circ.eval]
  | and cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X
  | or cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X
  | xor cs =>
    simp only [Circ.flip, Circ.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact eval_flip c X

termination_by A
decreasing_by all_goals simp_wf; have := List.sizeOf_lt_of_mem hc; omega

private theorem eval_orChildren {V : Type} (A : Circ V) (X : V → Bool) :
    (A.orChildren.map (fun c => c.eval X)).any id = A.eval X := by
  cases A <;> simp [Circ.orChildren, Circ.eval]

private theorem eval_andChildren {V : Type} (A : Circ V) (X : V → Bool) :
    (A.andChildren.map (fun c => c.eval X)).all id = A.eval X := by
  cases A <;> simp [Circ.andChildren, Circ.eval]

private theorem eval_liftAxiom {n m : ℕ} (g : Circ (Fin m))
    (C : LiftSAParity.Clause (Fin n))
    (α : Fin n × Bool → Fin g.andChildren.length) (X : Fin n × Fin m → Bool) :
    (liftAxiom g C α).eval X = true ↔
      ∃ l ∈ C, (gadgetH g l.2 (α l)).eval (fun j => X (l.1, j)) = true := by
  classical
  simp only [liftAxiom, Circ.eval, List.map_flatMap, List.any_flatMap]
  simp only [List.map_map, Function.comp_def, eval_rename]
  simp only [eval_orChildren, List.any_eq_true, Finset.mem_toList]

-- Decode each block by g_1. Disjointness ensures that a block accepted by g_0 decodes to 0.
theorem solution {d n m : ℕ} (hd : 2 ≤ d) (g : Circ (Fin m)) (hg : IsGadget d g)
    (F : LiftSAParity.CNF (Fin n)) (hF : ¬ LiftSAParity.Satisfiable F) :
    ¬ ∃ X : Fin n × Fin m → Bool, ∀ A ∈ lift g F, A.eval X = true := by
  classical
  intro ⟨X, hX⟩
  let a : Fin n → Bool := fun i => g.eval (fun j => !X (i, j))
  apply hF
  refine ⟨a, ?_⟩
  intro C hC hfalse
  have hbad : ∀ l : Fin n × Bool, l ∈ C →
      ∃ j : Fin g.andChildren.length,
        (gadgetH g l.2 j).eval (fun k => X (l.1, k)) = false := by
    intro l hl
    have hn : (if l.2 then g.eval (fun j => !X (l.1, j))
        else g.eval (fun j => X (l.1, j))) = false := by
      have hne := hfalse l hl
      cases hb : l.2 with
      | false =>
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        have ha : a l.1 = true := by simpa [hb] using hne
        have hdis := hg.2.2.2.2.2 (fun j => X (l.1, j))
        cases he : g.eval (fun j => X (l.1, j)) with
        | false => rfl
        | true => exact False.elim (hdis ⟨he, ha⟩)
      | true =>
        simpa [hb, a] using hne
    have hall : ¬ ∀ j : Fin g.andChildren.length,
        (gadgetH g l.2 j).eval (fun k => X (l.1, k)) = true := by
      intro h
      have hgval : (if l.2 then g.eval (fun j => !X (l.1, j))
          else g.eval (fun j => X (l.1, j))) = true := by
        cases hb : l.2 <;>
          simp only [gadgetH, hb, Bool.false_eq_true, ↓reduceIte, eval_flip] at h
        all_goals simp only [hb, Bool.false_eq_true, ↓reduceIte]
        all_goals
          rw [← eval_andChildren]
          simp only [List.all_eq_true, List.mem_map]
          intro b hb'
          obtain ⟨c, hc, rfl⟩ := hb'
          obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
          rw [← hj]
          exact h j
      simp [hn] at hgval
    obtain ⟨j, hj⟩ := not_forall.mp hall
    exact ⟨j, by simpa using hj⟩
  obtain ⟨cs, hcs, hroot⟩ := hg.2.2.2.1
  have hlen : 0 < g.andChildren.length := by
    rw [hroot]
    simpa [Circ.andChildren] using List.length_pos_iff.mpr hcs
  let α : Fin n × Bool → Fin g.andChildren.length := fun l =>
    if h : l ∈ C then Classical.choose (hbad l h) else ⟨0, hlen⟩
  have hmem : liftAxiom g C α ∈ lift g F := by
    simp only [lift, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨C, hC, α, rfl⟩
  obtain ⟨l, hl, htrue⟩ := (eval_liftAxiom g C α X).mp (hX _ hmem)
  have hf : (gadgetH g l.2 (α l)).eval (fun k => X (l.1, k)) = false := by
    simpa [α, hl] using Classical.choose_spec (hbad l hl)
  simp [hf] at htrue
