-- Prove2me | solution 1 for PolymerEndpoint.Atomic.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:28:10.975977+00:00
-- url     : https://prove2.me/submissions/7270a922-c2e9-434d-9d2f-4910c875bb68

import Mathlib

set_option autoImplicit false

open Filter
open scoped Topology

theorem solution {𝒳 : Type*} [MetricSpace 𝒳] [CompactSpace 𝒳]
    (F : ℕ → 𝒳 → ℝ) (G : 𝒳 → ℝ)
    (hmono : Monotone F)
    (hF : ∀ n, LowerSemicontinuous (F n))
    (hG : UpperSemicontinuous G)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    TendstoUniformly F G atTop := by
  have hle : ∀ n x, F n x ≤ G x := fun n x =>
    ge_of_tendsto (hlim x) (eventually_atTop.2 ⟨n, fun m hm => hmono hm x⟩)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let U : ℕ → Set 𝒳 := fun n => {x | -ε < F n x - G x}
  have hUo : ∀ n, IsOpen (U n) := by
    intro n
    have : LowerSemicontinuous (fun x => F n x - G x) := by
      have h2 : LowerSemicontinuous (fun x => -G x) := hG.neg
      simpa [sub_eq_add_neg] using (hF n).add h2
    exact this.isOpen_preimage (-ε)
  have hcov : (Set.univ : Set 𝒳) ⊆ ⋃ n, U n := by
    intro x _
    have := (hlim x).eventually (Ioi_mem_nhds (show G x - ε < G x by linarith))
    obtain ⟨n, hn⟩ := this.exists
    exact Set.mem_iUnion.2 ⟨n, by simp only [U, Set.mem_setOf_eq]; have hn' : G x - ε < F n x := hn; linarith⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · intro x hx
      simp only [U, Set.mem_setOf_eq] at hx ⊢
      have := hmono (le_max_left i j) x
      linarith
    · intro x hx
      simp only [U, Set.mem_setOf_eq] at hx ⊢
      have := hmono (le_max_right i j) x
      linarith
  obtain ⟨N, hN⟩ := isCompact_univ.elim_directed_cover U hUo hcov hdir
  refine eventually_atTop.2 ⟨N, fun n hn x => ?_⟩
  have h1 : -ε < F N x - G x := hN (Set.mem_univ x)
  have h2 := hmono hn x
  have h3 := hle n x
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
