-- Prove2me | solution 1 for PriceOfStability.Harmonic.rosenthal_potential_change
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:16:03.771232+00:00
-- url     : https://prove2.me/submissions/49b91f38-3e06-4b1b-9707-b5292d4ee979

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum


namespace PriceOfStability.Harmonic

lemma load_split {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (A : ι → Finset E) (i : ι) (e : E) :
    (load A e : ℝ) = (if e ∈ A i then 1 else 0) +
      ∑ j ∈ ({i}ᶜ : Finset ι), (if e ∈ A j then (1:ℝ) else 0) := by
  unfold load
  rw [Finset.card_filter]
  push_cast
  rw [← Fintype.sum_eq_add_sum_compl i (fun j => if e ∈ A j then (1:ℝ) else 0)]

lemma load_update_rel {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (S : ι → Finset E) (i : ι) (T : Finset E) (e : E) :
    (load (Function.update S i T) e : ℝ) + (if e ∈ S i then 1 else 0) =
      (load S e : ℝ) + (if e ∈ T then 1 else 0) := by
  rw [load_split (Function.update S i T) i e, load_split S i e]
  have : ∑ j ∈ ({i}ᶜ : Finset ι), (if e ∈ Function.update S i T j then (1:ℝ) else 0)
      = ∑ j ∈ ({i}ᶜ : Finset ι), (if e ∈ S j then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have : j ≠ i := by simpa using hj
    rw [Function.update_of_ne this]
  rw [this]
  simp only [Function.update_self]
  ring

lemma rpc_core {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S : ι → Finset E) (i : ι) (T : Finset E) :
    potential G (Function.update S i T) - potential G S =
      cost G (Function.update S i T) i - cost G S i := by
  unfold potential cost
  simp only [Function.update_self]
  rw [← Finset.sum_sub_distrib]
  have key : ∀ e, (∑ x ∈ Finset.Icc 1 (load (Function.update S i T) e), G.latency e x)
      - ∑ x ∈ Finset.Icc 1 (load S e), G.latency e x
      = (if e ∈ T then G.latency e (load (Function.update S i T) e) else 0)
        - (if e ∈ S i then G.latency e (load S e) else 0) := by
    intro e
    have h := load_update_rel S i T e
    by_cases h1 : e ∈ S i <;> by_cases h2 : e ∈ T <;> simp only [h1, h2, if_true, if_false] at h ⊢
    · have : load (Function.update S i T) e = load S e := by exact_mod_cast (show ((load (Function.update S i T) e : ℕ) : ℝ) = load S e by linarith)
      rw [this]; ring
    · have : load S e = load (Function.update S i T) e + 1 := by exact_mod_cast (show ((load S e : ℕ) : ℝ) = load (Function.update S i T) e + 1 by linarith)
      rw [this, Finset.sum_Icc_succ_top (by omega)]; ring
    · have : load (Function.update S i T) e = load S e + 1 := by exact_mod_cast (show ((load (Function.update S i T) e : ℕ) : ℝ) = load S e + 1 by linarith)
      rw [this, Finset.sum_Icc_succ_top (by omega)]; ring
    · have : load (Function.update S i T) e = load S e := by exact_mod_cast (show ((load (Function.update S i T) e : ℕ) : ℝ) = load S e by linarith)
      rw [this]; ring
  rw [Finset.sum_congr rfl (fun e _ => key e), Finset.sum_sub_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter]
  simp

end PriceOfStability.Harmonic

open PriceOfStability.Harmonic
open CongestionPoA.AsymSum

theorem solution {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (G : CongestionGame ι E) (S : ι → Finset E) (i : ι) (T : Finset E) :
    potential G (Function.update S i T) - potential G S =
      cost G (Function.update S i T) i - cost G S i := by
  exact rpc_core G S i T
