-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_SmoothOnAdditive_main__f00fdea2d781
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:01:21.243238+00:00
-- url     : https://prove2.me/submissions/40348927-5551-4949-be24-8329ca00e66b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers
private lemma smOn_zero {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : Set E) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun _ : E => (0 : V)) := by
  intro a _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
private lemma smOn_add {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f g : E → V}
    (hf : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A f) (hg : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A g) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun x => f x + g x) := by
  intro a ha
  obtain ⟨U1, F1, hU1, ha1, hF1, he1⟩ := hf a ha
  obtain ⟨U2, F2, hU2, ha2, hF2, he2⟩ := hg a ha
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨ha1, ha2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), ?_⟩
  intro x hx hxA
  simp only [he1 x hx.1 hxA, he2 x hx.2 hxA]
end UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers
end

set_option autoImplicit false

open UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers
namespace UpperTheory.Reformulated.B.SmoothOnAdditive.main
theorem _root_.solution.{u_1, u_2, u_3} :
    ∀ {E : Type u_1} {V : Type u_2} {ι : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
      [inst_2 : NormedAddCommGroup V] [inst_3 : NormedSpace ℝ V] {A : Set E} {f : ι → E → V} (s : Finset ι),
      (∀ i ∈ s, UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (f i)) → UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A fun (a : E) ↦ ∑ i ∈ s, f i a := by
  intro E V ι _ _ _ _ A f s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (smOn_zero (V := V) A)
  | insert j s hj ih =>
    intro h
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := smOn_add h1 h2
    simpa [Finset.sum_insert hj] using this
end UpperTheory.Reformulated.B.SmoothOnAdditive.main
