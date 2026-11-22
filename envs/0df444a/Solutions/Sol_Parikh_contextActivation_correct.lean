-- Prove2me | solution 1 for Parikh.contextActivation_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T09:51:58.84821+00:00
-- url     : https://prove2.me/submissions/8369cbd5-b04f-472a-9f2d-daad8eee236c

module
public import Definitions.Def_LeanPool_Parikh_ActivationAlgorithm
public import Definitions.Def_LeanPool_Parikh_BoundedFamilySupport
public import Definitions.Def_LeanPool_Parikh_CompilerSupport

set_option autoImplicit true
@[expose] public section
public section
open Parikh
namespace Parikh
theorem _root_.solution {T : Type*} (g : ContextFreeGrammar T)
    [DecidableEq g.NT] [DecidableEq (ParseTree T g.NT)]
    (B : ParseTree T g.NT) (D : List (ParseTree T g.NT))
    (hD : ∀ C ∈ D, ∃ A, Cycle g C A) :
    contextActivation g B D = true ↔ ContextsActivatable g B D.toFinset := by
  have hroot (C : ParseTree T g.NT) (A : g.NT) (h : Cycle g C A) :
      ParseTree.rootLabel g.initial C = A := by
    unfold ParseTree.rootLabel
    rw [h.2.1]
  have hcycles : ∀ C ∈ D.toFinset, Cycle g C (ParseTree.rootLabel g.initial C) := by
    intro C hC
    obtain ⟨A, ha⟩ := hD C (List.mem_toFinset.mp hC)
    simpa only [hroot C A ha] using ha
  have hsupport (C : ParseTree T g.NT) :
      (C.productionLabels.toFinset : Set g.NT) = C.support := by
    ext A
    simp [ParseTree.support]
  rw [contextActivation, (activationTest g.NT (ParseTree T g.NT)).correct]
  simp only [hsupport]
  constructor
  · rintro ⟨order, hn, hm, ho⟩
    exact ⟨order, hn, hm, ParseTree.rootLabel g.initial, hcycles, ho⟩
  · rintro ⟨order, hn, hm, roots, hc, ho⟩
    refine ⟨order, hn, hm, ?_⟩
    have heq : ∀ C ∈ order, ParseTree.rootLabel g.initial C = roots C :=
      fun C hC => hroot C (roots C) (hc C ((hm C).mp hC))
    have hcongr : ∀ (U : Set g.NT) (cs : List (ParseTree T g.NT)),
        (∀ c ∈ cs, ParseTree.rootLabel g.initial c = roots c) →
        (ActivationOrder roots ParseTree.support U cs ↔
          ActivationOrder (ParseTree.rootLabel g.initial) ParseTree.support U cs) := by
      intro U cs he
      induction cs generalizing U with
      | nil => rfl
      | cons c cs ih =>
        simp only [ActivationOrder, he c (by simp)]
        rw [ih (U ∪ c.support) (fun d hd => he d (by simp [hd]))]
    exact (hcongr _ order heq).mp ho
end Parikh
