-- Prove2me | solution 1 for ObfImpossibility.RiceNoSize.Z_profile
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T13:40:18.658934+00:00
-- url     : https://prove2.me/submissions/3ac10ed0-4224-45af-b25a-03479374575e

import Mathlib
import Definitions.Def_ObfImpossibility_RiceNoSize_ProofObjects

open ObfImpossibility.RiceNoSize Turing
namespace RiceZero

def cfg (L : ListBlank Bool) (x : ℕ) : TM0.Cfg Bool (Fin 1) :=
  ⟨0,Tape.mk' L (ListBlank.mk (List.replicate x true))⟩

lemma step_zero (L : ListBlank Bool) : TM0.step Z.δ (cfg L 0) = none := by
  simp [TM0.step,Z,cfg]

lemma step_succ (L : ListBlank Bool) (x : ℕ) :
    TM0.step Z.δ (cfg L (x+1)) = some (cfg (L.cons true) x) := by
  simp [TM0.step,Z,cfg,List.replicate_succ]

lemma output_zero (L : ListBlank Bool) : output (cfg L 0) = 0 := by
  simp only [output,cfg,Tape.mk'_right₀]
  rfl

lemma profile (t x : ℕ) (L : ListBlank Bool) :
    runFor Z t (cfg L x) = if t < x then none else some 0 := by
  induction t generalizing x L with
  | zero =>
    cases x with
    | zero => simp [runFor,step_zero]; exact output_zero L
    | succ x => simp [runFor,step_succ]
  | succ t ih =>
    cases x with
    | zero => simp [runFor,step_zero]; exact output_zero L
    | succ x => simpa [runFor,step_succ] using ih x (L.cons true)

lemma reaches (x : ℕ) (L : ListBlank Bool) :
    ∃ L', StateTransition.Reaches (TM0.step Z.δ) (cfg L x) (cfg L' 0) := by
  induction x generalizing L with
  | zero => exact ⟨L,Relation.ReflTransGen.refl⟩
  | succ x ih =>
    obtain ⟨L',h⟩ := ih (L.cons true)
    exact ⟨L',Relation.ReflTransGen.head (step_succ L x) h⟩

lemma fn_zero (x : ℕ) : fn Z x = Part.some 0 := by
  obtain ⟨L,hreach⟩ := reaches x (ListBlank.mk [])
  have hm : cfg L 0 ∈ StateTransition.eval (TM0.step Z.δ) (TM0.init (input x)) :=
    StateTransition.mem_eval.mpr ⟨hreach,step_zero L⟩
  apply Part.eq_some_iff.mpr
  unfold fn TM0.eval
  apply (Part.mem_map_iff _).mpr
  refine ⟨(cfg L 0).Tape.right₀,?_,?_⟩
  · exact (Part.mem_map_iff _).mpr ⟨cfg L 0,hm,rfl⟩
  · exact output_zero L

end RiceZero

theorem solution :
    (∀ t x : ℕ, bounded Z t x = if t < x then none else some 0) ∧ Z ∈ PiN := by
  constructor
  · intro t x
    exact RiceZero.profile t x (ListBlank.mk [])
  · constructor
    · intro x
      rw [RiceZero.fn_zero]
      trivial
    · exact RiceZero.fn_zero

#print axioms solution
