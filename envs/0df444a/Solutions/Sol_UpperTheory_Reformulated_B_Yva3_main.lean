-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yva3.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:33:00.985869+00:00
-- url     : https://prove2.me/submissions/3be9898a-b988-4e3f-86ce-24a60273ef28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTailFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.Yva3.Helpers
private lemma key {α ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) (u : Finset (ι → α)) :
    ∑ ξ ∈ u, ∏ i, f (ξ i) ≤ ∏ _i : ι, ∑' x, f x := by
  have h1 : ∑ ξ ∈ u, ∏ i, f (ξ i)
      ≤ ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ξ hξ
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hξ
    · intro ξ _ _
      exact Finset.prod_nonneg fun i _ => h0 (ξ i)
  have h2 : ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i)
      = ∏ i, ∑ x ∈ u.image (fun η => η i), f x :=
    by rw [Finset.prod_univ_sum]
  have h3 : ∏ i, ∑ x ∈ u.image (fun η => η i), f x ≤ ∏ _i : ι, ∑' x, f x := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg fun x _ => h0 x
    · intro i _
      exact hf.sum_le_tsum _ (fun x _ => h0 x)
  exact h1.trans (h2.le.trans h3)
private lemma summ {α ι : Type} [Fintype ι] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) : Summable fun (ξ : ι → α) ↦ ∏ i : ι, f (ξ i) := by
  classical
  exact summable_of_sum_le (fun ξ => Finset.prod_nonneg fun i _ => h0 (ξ i)) (key hf h0)
end UpperTheory.Reformulated.B.Yva3.Helpers
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yva3
theorem _root_.solution :
    ∀ {k : Type} [inst : Field k] [NumberField k] {ι : Type} [inst : Fintype ι] {f : k → ℝ},
      Summable f → (∀ (a : k), (0 : ℝ) ≤ f a) → Summable fun (ξ : ι → k) ↦ ∏ i : ι, f (ξ i) := by
  intro k _ _ ι _ f hf h0
  exact UpperTheory.Reformulated.B.Yva3.Helpers.summ hf h0
end UpperTheory.Reformulated.B.Yva3
