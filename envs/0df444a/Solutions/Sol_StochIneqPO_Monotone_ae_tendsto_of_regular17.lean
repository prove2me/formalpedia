-- Prove2me | solution 1 for StochIneqPO.Monotone.ae_tendsto_of_regular17
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:35:32.933442+00:00
-- url     : https://prove2.me/submissions/cdadf6ad-f131-4d37-9e52-507b8186806e

import Mathlib
import Definitions.Def_StochIneqPO_Monotone_Regular17
import Definitions.Def_StochIneqPO_Monotone_ConvergenceModes



namespace StochIneqPO.Monotone

open MeasureTheory Filter Topology

theorem regular17_tendsto_of_subseq {E : Type*} [TopologicalSpace E] [PartialOrder E]
    (h17 : Regular17 E) (f : ℕ → E) (hf : Monotone f) (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : E)
    (hz : Tendsto (fun k => f (φ k)) atTop (𝓝 z)) : Tendsto f atTop (𝓝 z) := by
  by_contra hcon
  obtain ⟨U, hU, hfreq⟩ := (Filter.not_tendsto_iff_exists_frequently_notMem).1 hcon
  have h1 : ∀ N : ℕ, ∃ m, N + 1 ≤ m ∧ f m ∉ U := by
    intro N
    have := (Filter.frequently_atTop.1 hfreq) (N + 1)
    obtain ⟨m, hm, hm'⟩ := this
    exact ⟨m, hm, hm'⟩
  choose g hg1 hg2 using h1
  let b : ℕ → ℕ := fun k => Nat.rec (g 0) (fun _ bk => g (φ bk)) k
  have hb0 : b 0 = g 0 := rfl
  have hbs : ∀ k, b (k + 1) = g (φ (b k)) := fun k => rfl
  have hbbad : ∀ k, f (b k) ∉ U := by
    intro k
    cases k with
    | zero => rw [hb0]; exact hg2 0
    | succ k => rw [hbs]; exact hg2 _
  have hbstep : ∀ k, φ (b k) + 1 ≤ b (k + 1) := by
    intro k; rw [hbs]; exact hg1 _
  have hφid : ∀ n, n ≤ φ n := fun n => hφ.id_le n
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro k
    have := hφid (b k)
    have := hbstep k
    omega
  have hx : Tendsto (fun k => f (φ (b k))) atTop (𝓝 z) :=
    hz.comp hbmono.tendsto_atTop
  have hy := h17 (fun k => f (φ (b k))) (fun k => f (b (k + 1))) z
    (fun n => ⟨hf (by have := hbstep n; omega), hf (by have := hφid (b (n + 1)); omega)⟩) hx
  exact hbbad 0 (by
    have := hy
    exact absurd this (by
      intro hy'
      have hev := hy'.eventually hU
      obtain ⟨n, hn⟩ := hev.exists
      exact hbbad (n + 1) hn))

theorem ae_tendsto_of_regular17_core {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : Regular17 E)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (Y : Ω → E) (hY : Measurable Y) (hXY : TendstoInMeasure μ X atTop Y) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => X i ω) atTop (𝓝 (Y ω)) := by
  obtain ⟨ns, hns, hae⟩ := hXY.exists_seq_tendsto_ae
  filter_upwards [hae] with ω hω
  exact regular17_tendsto_of_subseq h17 (fun i => X i ω) (hmono ω) ns hns (Y ω) hω

end StochIneqPO.Monotone

open StochIneqPO.Monotone
open MeasureTheory Filter Topology

theorem solution {E : Type*} [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PartialOrder E] [OrderClosedTopology E]
    (h17 : Regular17 E)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ i, Measurable (X i)) (hmono : ∀ ω, Monotone fun i => X i ω)
    (Y : Ω → E) (hY : Measurable Y) (hXY : TendstoInMeasure μ X atTop Y) :
    ∀ᵐ ω ∂μ, Tendsto (fun i => X i ω) atTop (𝓝 (Y ω)) := by
  exact ae_tendsto_of_regular17_core h17 μ X hX hmono Y hY hXY
