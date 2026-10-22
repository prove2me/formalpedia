-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_1_c
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:34:44.080582+00:00
-- url     : https://prove2.me/submissions/363da00c-933f-4ff8-8acf-2cba9f2db54d

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



lemma poa_basic_of_standing (N : Network) (hN : N.Standing) : N.Basic :=
  ⟨hN.1, hN.2.1, hN.2.2.1, fun k => lt_of_lt_of_le (by norm_num) (hN.2.2.2.2 k)⟩

lemma poa_lf_nonneg (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin N.J) :
    0 ≤ linkFlow N.A x j := by
  unfold linkFlow
  refine Finset.sum_nonneg (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> [simp; simpa using hx r]


lemma poa_lf_le (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin N.J) :
    linkFlow N.A x j ≤ ∑ r, x r := by
  unfold linkFlow
  refine Finset.sum_le_sum (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> simp [hx r]

lemma poa_sum_flow (N : Network) {Γ : Game N} {x : Fin N.R → ℝ} (hx : IsFlow Γ x) :
    ∑ r, x r = totalDemand Γ.d := by
  unfold totalDemand
  rw [← Finset.sum_fiberwise Finset.univ N.s x]
  exact Finset.sum_congr rfl (fun k _ => hx.2 k)

lemma poa_wardrop_ineq (N : Network) (hN : N.Basic) (Γ : Game N) (ftil g : Fin N.R → ℝ)
    (hftil : IsWE Γ ftil) (hg : IsFlow Γ g) :
    0 ≤ ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A g j - linkFlow N.A ftil j) := by
  obtain ⟨⟨hgnn, hgsum⟩, hwe⟩ := hftil
  obtain ⟨hfnn, hfsum⟩ := hg
  rw [poa_path_decomp]
  rw [← Finset.sum_fiberwise Finset.univ N.s]
  refine Finset.sum_nonneg (fun k _ => ?_)
  have hne : (Finset.univ.filter (fun r => N.s r = k)).Nonempty :=
    Finset.card_pos.mp (hN.2.2.2 k)
  obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image _ (pathCost Γ ftil) hne
  have hr0k : N.s r0 = k := (Finset.mem_filter.mp hr0).2
  have hA : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * ftil r =
      pathCost Γ ftil r0 * ftil r := by
    intro r hr
    have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
    rcases (hgnn r).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · have h1 := hwe r r0 (by rw [hrk, hr0k]) h0
      have h2 := hmin r hr
      have : pathCost Γ ftil r = pathCost Γ ftil r0 := le_antisymm (by simpa [pathCost] using h1) h2
      rw [this]
  have hB : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r0 * g r ≤
      pathCost Γ ftil r * g r := fun r hr =>
    mul_le_mul_of_nonneg_right (hmin r hr) (hfnn r)
  have hs1 := hfsum k
  have hs2 := hgsum k
  have e1 : ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * (g r - ftil r) =
      ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * g r -
        ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * ftil r := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e1, Finset.sum_congr rfl hA, ← Finset.mul_sum, hs2]
  have := Finset.sum_le_sum hB
  rw [← Finset.mul_sum, hs1] at this
  linarith

lemma poa_mono_int (h : ℝ → ℝ) (hc : ContinuousOn h (Set.Ici 0)) (hm : MonotoneOn h (Set.Ici 0))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    h a * (b - a) ≤ ∫ u in a..b, h u ∧ ∫ u in a..b, h u ≤ h b * (b - a) := by
  have hint : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → IntervalIntegrable h MeasureTheory.volume x y := by
    intro x y hx hy
    refine ContinuousOn.intervalIntegrable (hc.mono ?_)
    intro z hz
    rw [Set.mem_uIcc] at hz
    simp only [Set.mem_Ici]
    rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → h x * (y - x) ≤ ∫ u in x..y, h u ∧ ∫ u in x..y, h u ≤ h y * (y - x) := by
    intro x y hx hxy
    have hy : 0 ≤ y := hx.trans hxy
    constructor
    · have := intervalIntegral.integral_mono_on hxy (intervalIntegrable_const (c := h x))
        (hint x y hx hy) (fun u hu => hm (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hu.1)) hu.1)
      simpa [mul_comm] using this
    · have := intervalIntegral.integral_mono_on hxy (hint x y hx hy)
        (intervalIntegrable_const (c := h y)) (fun u hu => hm (Set.mem_Ici.mpr (hx.trans hu.1)) (Set.mem_Ici.mpr hy) hu.2)
      simpa [mul_comm] using this
  rcases le_total a b with hab | hab
  · exact key a b ha hab
  · obtain ⟨k1, k2⟩ := key b a hb hab
    rw [intervalIntegral.integral_symm]
    constructor <;> nlinarith


lemma poa_min_exists (N : Network) (hN : N.Basic) (Γ : Game N) (f : Fin N.R → ℝ) (k : Fin N.Sd) :
    ∃ r0, N.s r0 = k ∧ minPathCost Γ f k = pathCost Γ f r0 ∧
      ∀ r, N.s r = k → pathCost Γ f r0 ≤ pathCost Γ f r := by
  have hne : (Finset.univ.filter (fun r => N.s r = k)).Nonempty :=
    Finset.card_pos.mp (hN.2.2.2 k)
  obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image _ (pathCost Γ f) hne
  have hr0k : N.s r0 = k := (Finset.mem_filter.mp hr0).2
  have hm : ∀ r, N.s r = k → pathCost Γ f r0 ≤ pathCost Γ f r := fun r hr =>
    hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
  refine ⟨r0, hr0k, ?_, hm⟩
  unfold minPathCost
  apply IsLeast.csInf_eq
  refine ⟨⟨r0, hr0k, rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact hm r hr

lemma poa_we_cost (N : Network) (hN : N.Basic) (Γ : Game N) (ftil : Fin N.R → ℝ) (hWE : IsWE Γ ftil) :
    cost Γ ftil = ∑ k, Γ.d k * minPathCost Γ ftil k := by
  obtain ⟨⟨hgnn, hgsum⟩, hwe⟩ := hWE
  rw [poa_cost_eq, ← Finset.sum_fiberwise Finset.univ N.s (fun r => ftil r * pathCost Γ ftil r)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  obtain ⟨r0, hr0k, hmv, hmin⟩ := poa_min_exists N hN Γ ftil k
  have hA : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), ftil r * pathCost Γ ftil r =
      ftil r * pathCost Γ ftil r0 := by
    intro r hr
    have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
    rcases (hgnn r).eq_or_lt with h0 | h0
    · rw [← h0]; ring
    · have h1 := hwe r r0 (by rw [hrk, hr0k]) h0
      have h2 := hmin r hrk
      have : pathCost Γ ftil r = pathCost Γ ftil r0 := le_antisymm (by simpa [pathCost] using h1) h2
      rw [this]
  rw [Finset.sum_congr rfl hA, ← Finset.sum_mul, hgsum k, hmv]

theorem lem1a (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
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

theorem lem1b (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ε : ℝ) (hε : 0 < ε) (f ftil : Fin N.R → ℝ) (hf : IsApproxWE Γ ε f) (hftil : IsWE Γ ftil) :
    (0 ≤ ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j) ∧
      ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j)
        ≤ potential Γ f - potential Γ ftil ∧
      potential Γ f - potential Γ ftil
        ≤ ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j) ∧
      ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j) ≤ ε) ∧
    (0 ≤ ∑ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)|
          * |linkFlow N.A f j - linkFlow N.A ftil j| ∧
      ∑ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)|
          * |linkFlow N.A f j - linkFlow N.A ftil j| ≤ ε) := by
  obtain ⟨hflow, happrox⟩ := hf
  obtain ⟨⟨hfnn, hfsum⟩, hfsum'⟩ := And.intro hflow hflow
  obtain ⟨⟨hgnn, hgsum⟩, hwe⟩ := hftil
  have hP3 : ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j) ≤ ε :=
    happrox ftil ⟨hgnn, hgsum⟩
  -- (1) nonnegativity from equilibrium
  have hP1 : 0 ≤ ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j) := by
    rw [poa_path_decomp]
    rw [← Finset.sum_fiberwise Finset.univ N.s]
    refine Finset.sum_nonneg (fun k _ => ?_)
    have hne : (Finset.univ.filter (fun r => N.s r = k)).Nonempty :=
      Finset.card_pos.mp (hN.2.2.2 k)
    obtain ⟨r0, hr0, hmin⟩ := Finset.exists_min_image _ (pathCost Γ ftil) hne
    have hr0k : N.s r0 = k := (Finset.mem_filter.mp hr0).2
    have hA : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * ftil r =
        pathCost Γ ftil r0 * ftil r := by
      intro r hr
      have hrk : N.s r = k := (Finset.mem_filter.mp hr).2
      rcases (hgnn r).eq_or_lt with h0 | h0
      · rw [← h0]; ring
      · have h1 := hwe r r0 (by rw [hrk, hr0k]) h0
        have h2 := hmin r hr
        have : pathCost Γ ftil r = pathCost Γ ftil r0 := le_antisymm (by simpa [pathCost] using h1) h2
        rw [this]
    have hB : ∀ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r0 * f r ≤
        pathCost Γ ftil r * f r := fun r hr =>
      mul_le_mul_of_nonneg_right (hmin r hr) (hfnn r)
    have hs1 := hfsum k
    have hs2 := hgsum k
    have e1 : ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * (f r - ftil r) =
        ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * f r -
          ∑ r ∈ Finset.univ.filter (fun r => N.s r = k), pathCost Γ ftil r * ftil r := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [e1, Finset.sum_congr rfl hA, ← Finset.mul_sum, hs2]
    have := Finset.sum_le_sum hB
    rw [← Finset.mul_sum, hs1] at this
    linarith
  -- (2) potential inequalities termwise
  have hmono : ∀ j, MonotoneOn (Γ.τ j) (Set.Ici 0) := fun j => (hΓ.1 j).2.1
  have hcont : ∀ j, ContinuousOn (Γ.τ j) (Set.Ici 0) := fun j => (hΓ.1 j).1
  have hy : ∀ j, 0 ≤ linkFlow N.A f j := poa_lf_nonneg N hN f hfnn
  have hyt : ∀ j, 0 ≤ linkFlow N.A ftil j := poa_lf_nonneg N hN ftil hgnn
  have hpot : ∀ j, (∫ u in (0:ℝ)..(linkFlow N.A f j), Γ.τ j u) - (∫ u in (0:ℝ)..(linkFlow N.A ftil j), Γ.τ j u) =
      ∫ u in (linkFlow N.A ftil j)..(linkFlow N.A f j), Γ.τ j u := by
    intro j
    have hint : ∀ x : ℝ, 0 ≤ x → IntervalIntegrable (Γ.τ j) MeasureTheory.volume 0 x := by
      intro x hx
      refine ContinuousOn.intervalIntegrable ((hcont j).mono ?_)
      intro z hz
      rw [Set.mem_uIcc] at hz
      simp only [Set.mem_Ici]
      rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    rw [intervalIntegral.integral_interval_sub_left (hint _ (hy j)) (hint _ (hyt j))]
  have hP2a : ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j) ≤
      potential Γ f - potential Γ ftil := by
    unfold potential wardropObjective
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [hpot j]
    exact (poa_mono_int _ (hcont j) (hmono j) _ _ (hyt j) (hy j)).1
  have hP2b : potential Γ f - potential Γ ftil ≤
      ∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j) := by
    unfold potential wardropObjective
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [hpot j]
    exact (poa_mono_int _ (hcont j) (hmono j) _ _ (hyt j) (hy j)).2
  refine ⟨⟨hP1, hP2a, hP2b, hP3⟩, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · have hterm : ∀ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)| *
        |linkFlow N.A f j - linkFlow N.A ftil j| =
        (Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)) * (linkFlow N.A f j - linkFlow N.A ftil j) := by
      intro j
      rw [← abs_mul]
      apply abs_of_nonneg
      rcases le_total (linkFlow N.A ftil j) (linkFlow N.A f j) with h | h
      · exact mul_nonneg (sub_nonneg.mpr (hmono j (Set.mem_Ici.mpr (hyt j)) (Set.mem_Ici.mpr (hy j)) h))
          (sub_nonneg.mpr h)
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (hmono j (Set.mem_Ici.mpr (hy j)) (Set.mem_Ici.mpr (hyt j)) h))
          (sub_nonpos.mpr h)
    simp only [hterm]
    have : ∑ j, (Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)) * (linkFlow N.A f j - linkFlow N.A ftil j) =
        (∑ j, Γ.τ j (linkFlow N.A f j) * (linkFlow N.A f j - linkFlow N.A ftil j)) -
          ∑ j, Γ.τ j (linkFlow N.A ftil j) * (linkFlow N.A f j - linkFlow N.A ftil j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]
    linarith

theorem solution (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
    (ε : ℝ) (hε : 0 < ε) (f ftil : Fin N.R → ℝ) (hf : IsApproxWE Γ ε f) (hftil : IsWE Γ ftil)
    (M : ℝ) (hM0 : 0 < M) (hM : ∀ j, LipOnIcc (Γ.τ j) (totalDemand Γ.d) M) :
    (∀ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)| ≤ Real.sqrt (M * ε)) ∧
    (∀ k, |minPathCost Γ ftil k - minPathCost Γ f k| ≤ (N.J : ℝ) * Real.sqrt (M * ε)) ∧
    |cost Γ f - cost Γ ftil| ≤ (N.J : ℝ) * Real.sqrt (M * ε) * totalDemand Γ.d + ε := by
  have h1b := lem1b N hN Γ hΓ ε hε f ftil hf hftil
  have h1a := lem1a N hN Γ hΓ ε hε f hf
  have hflowf : IsFlow Γ f := hf.1
  have hflowt : IsFlow Γ ftil := ⟨hftil.1.1, hftil.1.2⟩
  set T := totalDemand Γ.d with hT
  have hyf : ∀ j, 0 ≤ linkFlow N.A f j ∧ linkFlow N.A f j ≤ T := fun j =>
    ⟨poa_lf_nonneg N hN f hflowf.1 j, (poa_lf_le N hN f hflowf.1 j).trans (poa_sum_flow N hflowf).le⟩
  have hyt : ∀ j, 0 ≤ linkFlow N.A ftil j ∧ linkFlow N.A ftil j ≤ T := fun j =>
    ⟨poa_lf_nonneg N hN ftil hflowt.1 j, (poa_lf_le N hN ftil hflowt.1 j).trans (poa_sum_flow N hflowt).le⟩
  set s := Real.sqrt (M * ε) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- (1)
  have harc : ∀ j, |Γ.τ j (linkFlow N.A f j) - Γ.τ j (linkFlow N.A ftil j)| ≤ s := by
    intro j
    have hsum := h1b.2.2
    set a : Fin N.J → ℝ := fun i => |Γ.τ i (linkFlow N.A f i) - Γ.τ i (linkFlow N.A ftil i)| with ha
    set b : Fin N.J → ℝ := fun i => |linkFlow N.A f i - linkFlow N.A ftil i| with hb
    have hab : a j * b j ≤ ε := by
      have : a j * b j ≤ ∑ i, a i * b i :=
        Finset.single_le_sum (f := fun i => a i * b i) (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
      exact this.trans h1b.2.2
    have hlip : a j ≤ M * b j := hM j _ ⟨(hyf j).1, (hyf j).2⟩ _ ⟨(hyt j).1, (hyt j).2⟩
    have h2 : a j ^ 2 ≤ M * ε := by
      have := mul_le_mul_of_nonneg_left hlip (abs_nonneg _ : 0 ≤ a j)
      nlinarith [this, hab, hM0]
    exact Real.le_sqrt_of_sq_le h2
  -- (2)
  have hmin : ∀ k, |minPathCost Γ ftil k - minPathCost Γ f k| ≤ (N.J : ℝ) * s := by
    intro k
    have hpc : ∀ r, |pathCost Γ f r - pathCost Γ ftil r| ≤ (N.J : ℝ) * s := by
      intro r
      unfold pathCost
      rw [← Finset.sum_sub_distrib]
      calc |∑ j, (Γ.τ j (linkFlow N.A f j) * N.A j r - Γ.τ j (linkFlow N.A ftil j) * N.A j r)|
          ≤ ∑ j, |Γ.τ j (linkFlow N.A f j) * N.A j r - Γ.τ j (linkFlow N.A ftil j) * N.A j r| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin N.J, s := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [← sub_mul, abs_mul]
            rcases hN.1 j r with h | h <;> rw [h]
            · simpa using hs0
            · simpa using harc j
        _ = (N.J : ℝ) * s := by simp
    obtain ⟨r1, hr1k, hm1, hmin1⟩ := poa_min_exists N hN Γ f k
    obtain ⟨r2, hr2k, hm2, hmin2⟩ := poa_min_exists N hN Γ ftil k
    rw [hm1, hm2, abs_le]
    have e1 := abs_le.mp (hpc r1)
    have e2 := abs_le.mp (hpc r2)
    have e3 := hmin1 r2 hr2k
    have e4 := hmin2 r1 hr1k
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  -- (3)
  have hdnn : ∀ k, 0 ≤ Γ.d k := hΓ.2
  have hcwe := poa_we_cost N hN Γ ftil hftil
  have hdsum : ∑ k, Γ.d k = T := rfl
  have hsumd : ∑ k, Γ.d k * |minPathCost Γ ftil k - minPathCost Γ f k| ≤ (N.J : ℝ) * s * T := by
    calc ∑ k, Γ.d k * |minPathCost Γ ftil k - minPathCost Γ f k| ≤ ∑ k, Γ.d k * ((N.J : ℝ) * s) :=
          Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hmin k) (hdnn k))
      _ = (N.J : ℝ) * s * T := by rw [← Finset.sum_mul, hdsum]; ring
  have hlo : ∑ k, Γ.d k * minPathCost Γ ftil k - ∑ k, Γ.d k * minPathCost Γ f k ≤ (N.J : ℝ) * s * T := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hsumd
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left (le_abs_self _) (hdnn k)
  have hhi : ∑ k, Γ.d k * minPathCost Γ f k - ∑ k, Γ.d k * minPathCost Γ ftil k ≤ (N.J : ℝ) * s * T := by
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hsumd
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hdnn k)
    rw [abs_sub_comm]; exact le_abs_self _
  have hJ : 0 ≤ (N.J : ℝ) * s * T := by
    have : 0 ≤ T := by rw [hT]; exact Finset.sum_nonneg (fun k _ => hdnn k)
    positivity
  refine ⟨harc, hmin, ?_⟩
  rw [abs_le]
  constructor
  · rw [hcwe] at *
    linarith [h1a.2.1]
  · rw [hcwe]
    linarith [h1a.2.2]
