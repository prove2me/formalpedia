-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.schedule_usage_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:42:54.738081+00:00
-- url     : https://prove2.me/submissions/f86c6f1c-6445-441b-a306-77e7e1353bfa

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

set_option autoImplicit false

theorem p2m_9d63d571_card_filter_Icc_le (p : ℕ → Prop) [DecidablePred p] (a b : ℕ) (_h : a ≤ b) :
    ((Finset.Icc 1 b).filter p).card ≤ ((Finset.Icc 1 a).filter p).card + (b - a) := by
  have hsub : Finset.Icc 1 b ⊆ Finset.Icc 1 a ∪ Finset.Ioc a b := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc] at hx ⊢
    omega
  calc ((Finset.Icc 1 b).filter p).card
      ≤ ((Finset.Icc 1 a ∪ Finset.Ioc a b).filter p).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hsub)
    _ = ((Finset.Icc 1 a).filter p ∪ (Finset.Ioc a b).filter p).card := by
        rw [Finset.filter_union]
    _ ≤ ((Finset.Icc 1 a).filter p).card + ((Finset.Ioc a b).filter p).card :=
        Finset.card_union_le _ _
    _ ≤ ((Finset.Icc 1 a).filter p).card + (Finset.Ioc a b).card := by
        have := Finset.card_filter_le (Finset.Ioc a b) p
        omega
    _ = ((Finset.Icc 1 a).filter p).card + (b - a) := by
        rw [Nat.card_Ioc]

open ProcessingNetworks.PacketNetworks in
theorem solution
    {I J : ℕ} {Ω : Type*} (dat : PacketNetworkData I J) (P : PacketPrimitives I J Ω)
    (z : Fin I → ℕ) (s : Fin J → ℕ) (ω : Ω) (τ1 τ2 : ℕ) (h : τ1 ≤ τ2) :
    Tproc dat P z s τ2 ω - Tproc dat P z s τ1 ω ≤ (τ2 - τ1 : ℝ) := by
  unfold Tproc
  have key := p2m_9d63d571_card_filter_Icc_le (fun ℓ => policySched dat P z ℓ ω = s) τ1 τ2 h
  have key' : ((((Finset.Icc 1 τ2).filter (fun ℓ => policySched dat P z ℓ ω = s)).card : ℕ) : ℝ)
      ≤ ((((Finset.Icc 1 τ1).filter (fun ℓ => policySched dat P z ℓ ω = s)).card : ℕ) : ℝ)
        + ((τ2 - τ1 : ℕ) : ℝ) := by exact_mod_cast key
  rw [Nat.cast_sub h] at key'
  linarith

