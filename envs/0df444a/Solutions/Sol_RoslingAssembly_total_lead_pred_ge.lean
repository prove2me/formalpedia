-- Prove2me | solution 1 for RoslingAssembly.total_lead_pred_ge
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:04:46.268216+00:00
-- url     : https://prove2.me/submissions/422cc7fc-0180-47e3-9fe2-e107cf998f01

import Mathlib
import Definitions.Def_RoslingAssembly_Network_B
import Definitions.Def_RoslingAssembly_Network_M

open RoslingAssembly in
theorem solution {N : ℕ} (net : Network N) (ℓ : Fin N → ℕ) (i : Fin N) :
    ∀ k ∈ net.B i, net.M ℓ i + ℓ k ≤ net.M ℓ k := by
  classical
  intro k hk
  have hik : Relation.TransGen (fun a b => net.s a = some b) k i := by
    unfold Network.B at hk
    have h2 := (Finset.mem_filter.mp hk).2
    unfold Network.A at h2
    exact (Finset.mem_filter.mp h2).2
  have dec : ∀ a b, Relation.TransGen (fun a b => net.s a = some b) a b → b < a := by
    intro a b h
    induction h with
    | single h => exact net.s_lt _ _ h
    | tail _ h ih => exact lt_trans (net.s_lt _ _ h) ih
  have hnot : i ∉ net.A i := by
    intro h
    unfold Network.A at h
    exact lt_irrefl _ (dec _ _ (Finset.mem_filter.mp h).2)
  have hsub : insert i (net.A i) ⊆ net.A k := by
    intro x hx
    rw [Finset.mem_insert] at hx
    unfold Network.A
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | hx
    · exact hik
    · unfold Network.A at hx
      exact hik.trans (Finset.mem_filter.mp hx).2
  unfold Network.M
  have h := Finset.sum_le_sum_of_subset (f := ℓ) hsub
  rw [Finset.sum_insert hnot] at h
  omega
