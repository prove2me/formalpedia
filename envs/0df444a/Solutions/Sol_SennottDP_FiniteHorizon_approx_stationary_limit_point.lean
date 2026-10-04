-- Prove2me | solution 1 for SennottDP.FiniteHorizon.approx_stationary_limit_point
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:35:11.157218+00:00
-- url     : https://prove2.me/submissions/0a0d63bb-71a2-4ea3-a2e3-18daa501ea04

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion
import Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq

open scoped ENNReal NNReal Topology
open Filter

open SennottDP.FiniteHorizon in
theorem solution {S Act : Type} [Countable S] (M : MDC S Act)
    (AS : M.ApproxSeq) (e : ℕ → S → Act) (he : AS.IsStationarySeq e) :
    ∃ f : M.Stationary, M.IsApproxLimitPoint e f := by
  classical
  let _ : ∀ i, TopologicalSpace (M.A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (M.A i) := fun _ => ⟨rfl⟩
  let d : ∀ i, M.A i := fun i => ⟨(M.A_nonempty i).choose, (M.A_nonempty i).choose_spec⟩
  let x : ℕ → (∀ i, M.A i) := fun r i => if h : e r i ∈ M.A i then ⟨e r i, h⟩ else d i
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  refine ⟨⟨fun i => (a i).1, fun i => (a i).2⟩, φ, hφ, fun i => ?_⟩
  have h1 := (continuous_apply i).continuousAt.tendsto.comp hlim
  rw [nhds_discrete, tendsto_pure] at h1
  obtain ⟨N₁, hN₁0, hN₁⟩ := AS.SN_spec.2.2 i
  have h2 : ∀ᶠ k in atTop, N₁ ≤ φ k :=
    (hφ.tendsto_atTop).eventually (eventually_ge_atTop N₁)
  filter_upwards [h1, h2] with k hk hk2
  have hmem : e (φ k) i ∈ M.A i :=
    he (φ k) (le_trans hN₁0 hk2) i (AS.SN_spec.2.1 N₁ (φ k) hN₁0 hk2 hN₁)
  have : x (φ k) i = a i := hk
  simp only [x, dif_pos hmem] at this
  exact congrArg Subtype.val this
