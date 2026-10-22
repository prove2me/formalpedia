-- Prove2me | solution 1 for SensitivityPoA.Holder.lemma_1_b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:55.860154+00:00
-- url     : https://prove2.me/submissions/4f5dbc91-74f7-47d2-a392-a0545600c804

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

lemma poa_lf_nonneg (N : Network) (hN : N.Basic) (x : Fin N.R → ℝ) (hx : ∀ r, 0 ≤ x r) (j : Fin N.J) :
    0 ≤ linkFlow N.A x j := by
  unfold linkFlow
  refine Finset.sum_nonneg (fun r _ => ?_)
  rcases hN.1 j r with h | h <;> rw [h] <;> [simp; simpa using hx r]

theorem solution (N : Network) (hN : N.Basic) (Γ : Game N) (hΓ : Γ.IsGeneralized)
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
