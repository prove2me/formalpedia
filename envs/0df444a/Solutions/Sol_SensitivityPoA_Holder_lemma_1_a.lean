-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_1_a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:29:14.077973+00:00
-- url     : https://prove2.me/submissions/ab52c9c7-4cc7-4202-b15f-5fc7a6a77652

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_Holder_Setting

set_option autoImplicit false
open KellyStochasticNetworks
open SensitivityPoA.Holder

section
variable {N : Network}

lemma poa_path_decomp (Γ : Game N) (f x y : Fin N.R → ℝ) :
    ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A x j - linkFlow N.A y j) =
      ∑ r, pathCost Γ f r * (x r - y r) := by
  unfold pathCost linkFlow
  have : ∀ j, Γ.τ j (∑ r, N.A j r * f r) * ((∑ r, N.A j r * x r) - ∑ r, N.A j r * y r) =
      ∑ r, Γ.τ j (∑ r, N.A j r * f r) * N.A j r * (x r - y r) := by
    intro j
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  simp only [this]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => by rw [Finset.sum_mul])

lemma poa_cost_eq (Γ : Game N) (f : Fin N.R → ℝ) :
    cost Γ f = ∑ r, f r * pathCost Γ f r := by
  have := poa_path_decomp Γ f f (fun _ => 0)
  simp only [sub_zero] at this
  unfold cost
  have h2 : ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j) =
      ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A (fun _ => (0:ℝ)) j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [linkFlow]; ring
  rw [h2, this]
  exact Finset.sum_congr rfl (fun r _ => by ring)

end

theorem solution (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ε : ℝ) (hε : 0 < ε) (f : Fin N.R → ℝ) (hf : IsApproxWE Γ ε f) :
    (∀ k : Fin N.Sd,
      0 ≤ (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
          - Γ.d k * minPathCost Γ f k ∧
      (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
          - Γ.d k * minPathCost Γ f k ≤ ε) ∧
    (∑ k, Γ.d k * minPathCost Γ f k ≤ cost Γ f ∧
      cost Γ f ≤ (∑ k, Γ.d k * minPathCost Γ f k) + ε) := by
  obtain ⟨hflow, happrox⟩ := hf
  obtain ⟨hnn, hsum⟩ := hflow
  have hex : ∀ k, ∃ r0, N.s r0 = k ∧ ∀ r, N.s r = k → pathCost Γ f r0 ≤ pathCost Γ f r := by
    intro k
    have hne : (Finset.univ.filter (fun r => N.s r = k)).Nonempty :=
      Finset.card_pos.mp (hN.2.2.2 k)
    obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image _ (pathCost Γ f) hne
    exact ⟨r0, (Finset.mem_filter.mp hr0).2, fun r hr =>
      hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)⟩
  choose rs hrs_s hrs_min using hex
  have hminval : ∀ k, minPathCost Γ f k = pathCost Γ f (rs k) := by
    intro k
    unfold minPathCost
    apply IsLeast.csInf_eq
    refine ⟨⟨rs k, hrs_s k, rfl⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hrs_min k r hr
  obtain ⟨g, hg⟩ : ∃ g : Finset (Fin N.Sd) → Fin N.R → ℝ, ∀ T r, g T r =
      if N.s r ∈ T then (if r = rs (N.s r) then Γ.d (N.s r) else 0) else f r := ⟨_, fun _ _ => rfl⟩
  have hg_flow : ∀ T, IsFlow Γ (g T) := by
    intro T
    refine ⟨fun r => ?_, fun σ => ?_⟩
    · rw [hg]
      split_ifs
      · exact hΓ.2 _
      · exact le_rfl
      · exact hnn r
    · by_cases hσ : σ ∈ T
      · have : ∀ r ∈ Finset.univ.filter (fun r => N.s r = σ), g T r = if r = rs σ then Γ.d σ else 0 := by
          intro r hr
          have hrk : N.s r = σ := (Finset.mem_filter.mp hr).2
          rw [hg, hrk, if_pos hσ]
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
        simp [hrs_s σ]
      · have : ∀ r ∈ Finset.univ.filter (fun r => N.s r = σ), g T r = f r := by
          intro r hr
          have hrk : N.s r = σ := (Finset.mem_filter.mp hr).2
          rw [hg, hrk, if_neg hσ]
        rw [Finset.sum_congr rfl this]
        exact hsum σ
  have hT : ∀ T : Finset (Fin N.Sd), ∑ r, pathCost Γ f r * (f r - g T r) =
      ∑ k ∈ T, ((∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
        - Γ.d k * minPathCost Γ f k) := by
    intro T
    rw [← Finset.sum_fiberwise Finset.univ N.s]
    have hk : ∀ k, (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ f r * (f r - g T r)) =
        if k ∈ T then ((∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
          - Γ.d k * minPathCost Γ f k) else 0 := by
      intro k
      by_cases hkT : k ∈ T
      · rw [if_pos hkT]
        have h1 : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ f r * (f r - g T r) =
            f r * pathCost Γ f r - (if r = rs k then pathCost Γ f r * Γ.d k else 0) := by
          intro r hr
          have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
          rw [hg, hrk, if_pos hkT]
          split_ifs <;> ring
        rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_ite_eq']
        simp [hrs_s k, hminval k, mul_comm]
      · rw [if_neg hkT]
        refine Finset.sum_eq_zero (fun r hr => ?_)
        have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
        rw [hg, hrk, if_neg hkT]; ring
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_ite_mem, Finset.univ_inter]
  have hlow : ∀ k, 0 ≤ (∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * pathCost Γ f r)
          - Γ.d k * minPathCost Γ f k := by
    intro k
    have : Γ.d k * minPathCost Γ f k = ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), f r * minPathCost Γ f k := by
      rw [← hsum k, Finset.sum_mul]
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg (fun r hr => ?_)
    have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
    rw [hminval k, ← mul_sub]
    exact mul_nonneg (hnn r) (sub_nonneg.mpr (hrs_min k r hrk))
  have happ : ∀ T, ∑ r, pathCost Γ f r * (f r - g T r) ≤ ε := by
    intro T
    rw [← poa_path_decomp]
    exact happrox (g T) (hg_flow T)
  refine ⟨fun k => ⟨hlow k, ?_⟩, ?_, ?_⟩
  · have := happ {k}
    rw [hT, Finset.sum_singleton] at this
    exact this
  · rw [poa_cost_eq, ← Finset.sum_fiberwise Finset.univ N.s (fun r => f r * pathCost Γ f r)]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have := hlow k
    linarith
  · have := happ Finset.univ
    rw [hT] at this
    rw [poa_cost_eq, ← Finset.sum_fiberwise Finset.univ N.s (fun r => f r * pathCost Γ f r)]
    rw [Finset.sum_sub_distrib] at this
    linarith
