-- Prove2me | solution 1 for ReciprocityTheory.Cheb.fibre_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:43:00.200144+00:00
-- url     : https://prove2.me/submissions/790ac946-e5a4-4135-8f2e-a48cff900159

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {α β : Type*} (π : α → β) (f : α → ℝ) (h : β → ℝ) (n : ℕ) (hf0 : ∀ a, 0 ≤ f a)
    (hfh : ∀ a, f a ≤ h (π a)) (hh0 : ∀ b, 0 ≤ h b) (hh : Summable h)
    (hfib : ∀ b, {a | π a = b}.Finite ∧ {a | π a = b}.ncard ≤ n) :
    Summable f ∧ ∑' a, f a ≤ n * ∑' b, h b := by
  classical
  have key : ∀ u : Finset α, ∑ a ∈ u, f a ≤ n * ∑' b, h b := by
    intro u
    calc ∑ a ∈ u, f a ≤ ∑ a ∈ u, h (π a) := Finset.sum_le_sum fun a _ => hfh a
      _ = ∑ b ∈ u.image π, ∑ a ∈ u.filter (fun a => π a = b), h (π a) :=
          (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha) _).symm
      _ ≤ ∑ b ∈ u.image π, (n : ℝ) * h b := by
          refine Finset.sum_le_sum fun b _ => ?_
          have e : ∑ a ∈ u.filter (fun a => π a = b), h (π a)
              = ∑ a ∈ u.filter (fun a => π a = b), h b :=
            Finset.sum_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]
          rw [e, Finset.sum_const, nsmul_eq_mul]
          have hc : (u.filter (fun a => π a = b)).card ≤ n := by
            have := Set.ncard_le_ncard (s := ((u.filter (fun a => π a = b) : Finset α) : Set α))
              (t := {a | π a = b}) (fun a ha => (Finset.mem_filter.1 ha).2) (hfib b).1
            rw [Set.ncard_coe_finset] at this
            exact this.trans (hfib b).2
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hh0 b)
      _ = n * ∑ b ∈ u.image π, h b := (Finset.mul_sum _ _ _).symm
      _ ≤ n * ∑' b, h b :=
          mul_le_mul_of_nonneg_left (hh.sum_le_tsum _ fun b _ => hh0 b) (Nat.cast_nonneg n)
  have hs : Summable f := summable_of_sum_le (fun a => hf0 a) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩
end ReciprocityTheory.Cheb
