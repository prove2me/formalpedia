-- Prove2me | solution 1 for ServiceParts.Allocation.eppen_schrage_balance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T16:26:31.609735+00:00
-- url     : https://prove2.me/submissions/e180b5ea-667f-4c1c-a755-9a8395df8037

import Mathlib
import Definitions.Def_ServiceParts_Allocation_PoolingSystem

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
lemma es65_stdNormalCdf_strictMono : StrictMono ServiceParts.Allocation.stdNormalCdf := by
  intro a b hab
  unfold ServiceParts.Allocation.stdNormalCdf
  by_contra hle
  rw [not_lt] at hle
  have h := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at h
  have h0 : gaussianReal 0 1 (Set.Ioc a b) = 0 := by
    rw [h]; exact ENNReal.ofReal_eq_zero.mpr (by linarith)
  have hv : (volume : Measure ℝ) (Set.Ioc a b) = 0 :=
    gaussianReal_absolutelyContinuous' 0 one_ne_zero h0
  rw [Real.volume_Ioc] at hv
  have : 0 < b - a := by linarith
  exact absurd hv (by simpa using this)

open ServiceParts.Allocation in
theorem solution {m : ℕ} (A : ℕ) (hA : 0 < A) (μ σ : Fin m → ℝ)
    (hσ : ∀ j, 0 < σ j) (I dPrev dNow : Fin m → ℝ) (hbal : InBalance A μ σ I)
    (hcond : ∀ i, (∑ j ∈ Finset.univ.erase i, dNow j) + dNow i * (1 - (∑ j, σ j) / σ i)
      ≤ ∑ j, dPrev j) :
    ∃ x : Fin m → ℝ, (∀ j, 0 ≤ x j) ∧ ∑ j, x j = ∑ j, dPrev j ∧
      InBalance A μ σ (fun j => I j + x j - dNow j) := by
  rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨j0⟩⟩
  · refine ⟨fun _ => 0, fun j => (IsEmpty.false j).elim, by simp, 0, fun j => (IsEmpty.false j).elim⟩
  obtain ⟨p, hp⟩ := hbal
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr (by exact_mod_cast hA)
  have hS : 0 < ∑ j, σ j := Finset.sum_pos (fun j _ => hσ j) ⟨j0, Finset.mem_univ _⟩
  set c := (I j0 - A * μ j0) / (Real.sqrt A * σ j0) with hc
  have hargs : ∀ j, (I j - A * μ j) / (Real.sqrt A * σ j) = c := by
    intro j
    exact es65_stdNormalCdf_strictMono.injective ((hp j).trans (hp j0).symm)
  have hI : ∀ j, I j - A * μ j = c * (Real.sqrt A * σ j) := by
    intro j
    have hpos : 0 < Real.sqrt A * σ j := mul_pos hsA (hσ j)
    rw [← hargs j, div_mul_cancel₀ _ hpos.ne']
  set K := ((∑ j, dPrev j) - ∑ j, dNow j) / ∑ j, σ j with hK
  refine ⟨fun j => dNow j + σ j * K, ?_, ?_, ?_⟩
  · intro i
    have h1 := hcond i
    have h2 := Finset.add_sum_erase Finset.univ dNow (Finset.mem_univ i)
    have hσi := hσ i
    have e : dNow i * (1 - (∑ j, σ j) / σ i) = dNow i - dNow i * (∑ j, σ j) / σ i := by ring
    rw [e] at h1
    have h3 : (∑ j, dNow j) - (∑ j, dPrev j) ≤ dNow i * (∑ j, σ j) / σ i := by linarith
    have h4 : σ i * ((∑ j, dNow j) - (∑ j, dPrev j)) ≤ dNow i * (∑ j, σ j) := by
      rw [le_div_iff₀ hσi] at h3; linarith
    show 0 ≤ dNow i + σ i * K
    have e2 : dNow i + σ i * K = (dNow i * (∑ j, σ j) + σ i * ((∑ j, dPrev j) - ∑ j, dNow j)) / ∑ j, σ j := by
      rw [hK, eq_div_iff hS.ne']; field_simp
    rw [e2]
    apply div_nonneg _ hS.le
    linarith
  · simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hK]; field_simp; ring
  · refine ⟨stdNormalCdf (c + K / Real.sqrt A), fun j => ?_⟩
    congr 1
    have hpos : 0 < Real.sqrt A * σ j := mul_pos hsA (hσ j)
    have e : I j + (dNow j + σ j * K) - dNow j - A * μ j = c * (Real.sqrt A * σ j) + σ j * K := by
      have := hI j; linarith
    rw [e]
    have := hσ j
    field_simp

