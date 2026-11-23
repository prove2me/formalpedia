-- Prove2me | solution 1 for RiskBargaining.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:35:38.733367+00:00
-- url     : https://prove2.me/submissions/31634dcc-135e-4475-b443-b900024264fd

import Mathlib
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_z
import Definitions.Def_RiskBargaining_Instance_Attained

set_option autoImplicit false

open MeasureTheory RiskBargaining
open scoped ENNReal

namespace RiskBargaining.Prop2Proof

theorem lp_const_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) :
    Lp.const p μ (0 : ℝ) = 0 := by
  apply Lp.ext_iff.mpr
  refine (Lp.coeFn_const p μ (0 : ℝ)).trans ?_
  exact (Lp.coeFn_zero ℝ p μ).symm

theorem lp_const_add {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) (a b : ℝ) :
    Lp.const p μ a + Lp.const p μ b = Lp.const p μ (a + b) := by
  apply Lp.ext_iff.mpr
  refine (Lp.coeFn_add _ _).trans ?_
  refine ((Lp.coeFn_const p μ a).add (Lp.coeFn_const p μ b)).trans ?_
  exact (Lp.coeFn_const p μ (a + b)).symm

theorem sum_lp_const {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) (s : Finset ι) (c : ι → ℝ) :
    ∑ i ∈ s, Lp.const p μ (c i) = Lp.const p μ (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [lp_const_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, lp_const_add]

end RiskBargaining.Prop2Proof

open RiskBargaining.Prop2Proof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [Nonempty ι] (I : Instance μ p X ι) (hI : I.Attained) :
    I.U = {u | (∀ i, I.v i ≤ u i) ∧ ∑ i, u i ≤ I.z} ∧ IsGreatest I.totals I.z := by
  classical
  obtain ⟨z₀, hz₀⟩ := hI
  have hz_eq : I.z = z₀ :=
    le_antisymm (csSup_le ⟨z₀, hz₀.1⟩ hz₀.2) (le_csSup ⟨z₀, hz₀.2⟩ hz₀.1)
  have hgreat : IsGreatest I.totals I.z := hz_eq ▸ hz₀
  refine ⟨?_, hgreat⟩
  ext u
  simp only [Instance.U, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, L, hsum, huv⟩
    exact ⟨fun i => (huv i).1, hgreat.2 ⟨u, L, x, rfl, hsum, huv⟩⟩
  · rintro ⟨hvu, hsum_le⟩
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    obtain ⟨ustar, Lstar, xstar, hz_sum, hL_sum, huv_star⟩ := hgreat.1
    let c : ι → ℝ := fun i =>
      if i = i₀ then -∑ j ∈ Finset.univ.erase i₀, (u j - I.A j (Lstar j))
      else u i - I.A i (Lstar i)
    have hc_sum : ∑ i : ι, c i = 0 := by
      rw [← Finset.add_sum_erase Finset.univ c (Finset.mem_univ i₀)]
      have her : ∑ j ∈ Finset.univ.erase i₀, c j =
          ∑ j ∈ Finset.univ.erase i₀, (u j - I.A j (Lstar j)) :=
        Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)
      simp only [c, ite_true] at *
      rw [her]
      ring
    let L' : ι → Lp ℝ p μ := fun i => Lstar i + Lp.const p μ (c i)
    have hL'_sum : ∑ i : ι, L' i = I.M xstar := by
      simp only [L', Finset.sum_add_distrib, hL_sum, sum_lp_const, hc_sum, lp_const_zero, add_zero]
    refine ⟨xstar, L', hL'_sum, fun i => ⟨hvu i, ?_⟩⟩
    rw [(I.coherent i).translation (Lstar i) (c i)]
    by_cases hi : i = i₀
    · subst hi
      simp only [c, ite_true]
      have hA_ge_z : I.z ≤ ∑ j : ι, I.A j (Lstar j) := by
        rw [hz_sum]
        exact Finset.sum_le_sum fun j _ => (huv_star j).2
      have hsplit_u : u i + ∑ j ∈ Finset.univ.erase i, u j = ∑ j : ι, u j :=
        Finset.add_sum_erase Finset.univ u (Finset.mem_univ i)
      have hsplit_A : I.A i (Lstar i) + ∑ j ∈ Finset.univ.erase i, I.A j (Lstar j) =
          ∑ j : ι, I.A j (Lstar j) :=
        Finset.add_sum_erase Finset.univ (fun j => I.A j (Lstar j)) (Finset.mem_univ i)
      rw [Finset.sum_sub_distrib]
      linarith
    · simp only [c, if_neg hi]
      linarith
