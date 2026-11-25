-- Prove2me | solution 1 for P2M_Bl_general_b_fact_left______goal1_a57afc021d90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:57.19383+00:00
-- url     : https://prove2.me/submissions/8547a539-a6a6-42d3-9bfb-97fc3ae89a0f

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.general_b_fact_left'''''
private lemma aux {O A I : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Fintype I] [DecidableEq I] {B : I → Type} [(i : I) → AddCommGroup (B i)]
    [(i : I) → Module O (B i)] (ε : (i : I) → B i →ₗ[O] A)
    (T : (i : I) → Set (B i)) (S : Submodule O A)
    (hS : ∀ F : (i : I) → B i, (∀ i, F i ∈ T i) → ∏ i, ε i (F i) ∈ S) :
    ∀ s : Finset I, ∀ F : (i : I) → B i, (∀ i ∈ s, F i ∈ Submodule.span O (T i)) →
      (∀ i ∉ s, F i ∈ T i) → ∏ i, ε i (F i) ∈ S := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro F _ h2
    exact hS F (fun i => h2 i (Finset.notMem_empty i))
  | insert j s hj ih =>
    intro F h1 h2
    have key : ∀ x : B j, ∏ i, ε i (Function.update F j x i)
        = ε j x * ∏ i ∈ Finset.univ \ {j}, ε i (F i) := by
      intro x
      have e : (fun i => ε i (Function.update F j x i))
          = Function.update (fun k => ε k (F k)) j (ε j x) := by
        funext i
        exact Function.apply_update (fun k => (ε k : B k → A)) F j x i
      rw [e, Finset.prod_update_of_mem (Finset.mem_univ j)]
    have hT : T j ⊆ (S.comap ((LinearMap.mulRight O (∏ i ∈ Finset.univ \ {j}, ε i (F i))).comp (ε j)) :
        Set (B j)) := by
      intro x hx
      show (LinearMap.mulRight O (∏ i ∈ Finset.univ \ {j}, ε i (F i))) (ε j x) ∈ S
      rw [LinearMap.mulRight_apply, ← key x]
      apply ih (Function.update F j x)
      · intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij]
        exact h1 i (Finset.mem_insert_of_mem hi)
      · intro i hi
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self]
          exact hx
        · rw [Function.update_of_ne hij]
          exact h2 i (by simp [hij, hi])
    have hmem := Submodule.span_le.mpr hT (h1 j (Finset.mem_insert_self j s))
    have k := key (F j)
    rw [Function.update_eq_self] at k
    rw [k]
    exact hmem
end Bl.general_b_fact_left'''''
end

set_option autoImplicit false
open Bl Bl.general_b_fact_left'''''
namespace Bl.general_b_fact_left'''''
theorem _root_.solution :
  ∀ {O A I : Type} [inst : CommRing.{0} O] [inst_1 : CommRing.{0} A] [inst_2 : Algebra.{0, 0} O A]
  [inst_3 : Fintype.{0} I] [DecidableEq.{1} I] {B : I → Type} [inst_5 : (i : I) → AddCommGroup.{0} (B i)]
  [inst_6 : (i : I) → Module.{0, 0} O (B i)] (ε : (i : I) → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} O) (B i) A)
  (T : (i : I) → Set.{0} (B i)),
  Eq.{1}
    (Submodule.span.{0, 0} O
      (Set.ofPred.{0} fun (X : A) ↦
        Exists.{1} fun (F : (i : I) → B i) ↦
          And (∀ (i : I), Membership.mem.{0, 0} (Submodule.span.{0, 0} O (T i)) (F i))
            (Eq.{1} X (Finset.prod.{0, 0} Finset.univ.{0} fun (i : I) ↦ DFunLike.coe.{1, 1, 1} (ε i) (F i)))))
    (Submodule.span.{0, 0} O
      (Set.ofPred.{0} fun (X : A) ↦
        Exists.{1} fun (F : (i : I) → B i) ↦
          And (∀ (i : I), Membership.mem.{0, 0} (T i) (F i))
            (Eq.{1} X (Finset.prod.{0, 0} Finset.univ.{0} fun (i : I) ↦ DFunLike.coe.{1, 1, 1} (ε i) (F i))))) := by
  intro O A I _ _ _ _ _ B _ _ ε T
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro X ⟨F, hF, rfl⟩
    exact aux ε T _ (fun G hG => Submodule.subset_span
      (show ∃ H : (i : I) → B i, (∀ i, H i ∈ T i) ∧ ∏ i, ε i (G i) = ∏ i, ε i (H i) from
        ⟨G, hG, rfl⟩)) Finset.univ F
      (fun i _ => hF i) (fun i hi => absurd (Finset.mem_univ i) hi)
  · apply Submodule.span_mono
    rintro X ⟨F, hF, rfl⟩
    exact (show ∃ G : (i : I) → B i, (∀ i, G i ∈ Submodule.span O (T i)) ∧ _ from
      ⟨F, fun i => Submodule.subset_span (hF i), rfl⟩)
end Bl.general_b_fact_left'''''
