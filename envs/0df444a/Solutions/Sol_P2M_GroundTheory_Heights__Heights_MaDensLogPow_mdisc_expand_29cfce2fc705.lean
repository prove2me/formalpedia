-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_mdisc_expand_29cfce2fc705
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:24:14.379365+00:00
-- url     : https://prove2.me/submissions/da9842cc-84cf-4604-9aac-f5a393ed3544

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensLogPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLogPow
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_update_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLogPow
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLogPow
theorem _root_.solution (α β : ℂ) (H G : Matrix (Fin D) (Fin D) ℂ)
    (hG : ∀ (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (i j : Fin D), i ≠ j → A i = G → A j = G →
      mdisc A = 0) :
    ∀ (s : Finset (Fin D)) (C : Fin D → Matrix (Fin D) (Fin D) ℂ), (∀ i ∈ s, C i = H) →
      mdisc (fun i => if i ∈ s then α • H + β • G else C i) =
        α ^ s.card * mdisc C + α ^ (s.card - 1) * β * ∑ i ∈ s, mdisc (Function.update C i G) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro C _; simp
  | insert j s hj ih =>
    intro C hC
    have hCj : C j = H := hC j (Finset.mem_insert_self j s)
    have hCs : ∀ i ∈ s, C i = H := fun i hi => hC i (Finset.mem_insert_of_mem hi)
    have e1 : (fun i => if i ∈ insert j s then α • H + β • G else C i) =
        Function.update (fun i => if i ∈ s then α • H + β • G else C i) j (α • H + β • G) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have e2 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j H =
        (fun i => if i ∈ s then α • H + β • G else C i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj, hCj]
      · simp [Function.update_of_ne hij]
    have e3 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j G =
        (fun i => if i ∈ s then α • H + β • G else Function.update C j G i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [Function.update_of_ne hij]
    have hCs' : ∀ i ∈ s, Function.update C j G i = H := fun i hi => by
      rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; exact hCs i hi
    have hz : ∀ i ∈ s, mdisc (Function.update (Function.update C j G) i G) = 0 := fun i hi =>
      hG _ i j (by rintro rfl; exact hj hi) (by simp)
        (by rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; simp)
    rw [e1, mdisc_update_add, mdisc_update_smul, mdisc_update_smul, e2, e3, ih C hCs,
      ih _ hCs', Finset.sum_eq_zero hz, Finset.card_insert_of_notMem hj, Finset.sum_insert hj]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0, Finset.card_eq_zero.mp h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring
end GroundTheory.Heights₂.Heights.MaDensLogPow
