-- Prove2me | solution 1 for RiskBargaining.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:39:22.640794+00:00
-- url     : https://prove2.me/submissions/4c761a7c-6003-45c3-8cdb-d48c96ac4db4

import Mathlib
import Definitions.Def_RiskBargaining_Instance_z
import Definitions.Def_RiskBargaining_Instance_Admissible

set_option autoImplicit false

open MeasureTheory RiskBargaining
open scoped ENNReal

namespace RiskBargaining.Lemma5Proof

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

theorem isGreatest_z {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] {I : Instance μ p X ι} (hAtt : I.Attained) :
    IsGreatest I.totals I.z := by
  obtain ⟨z₀, hz₀⟩ := hAtt
  have hz_eq : I.z = z₀ :=
    le_antisymm (csSup_le ⟨z₀, hz₀.1⟩ hz₀.2) (le_csSup ⟨z₀, hz₀.2⟩ hz₀.1)
  exact hz_eq ▸ hz₀

theorem mem_totals_of_sum_v_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {ι : Type*} [Fintype ι] [Nonempty ι] (I : Instance μ p X ι)
    (x : X) (L : ι → Lp ℝ p μ) (hL : ∑ i, L i = I.M x)
    (hv : ∑ i, I.v i ≤ ∑ i, I.A i (L i)) :
    (∑ i, I.A i (L i)) ∈ I.totals := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let c : ι → ℝ := fun i =>
    if i = i₀ then -∑ j ∈ Finset.univ.erase i₀, (I.v j - I.A j (L j))
    else I.v i - I.A i (L i)
  have hc_sum : ∑ i : ι, c i = 0 := by
    rw [← Finset.add_sum_erase Finset.univ c (Finset.mem_univ i₀)]
    have her : ∑ j ∈ Finset.univ.erase i₀, c j =
        ∑ j ∈ Finset.univ.erase i₀, (I.v j - I.A j (L j)) :=
      Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)
    simp only [c, ite_true] at *
    rw [her]
    ring
  let L' : ι → Lp ℝ p μ := fun i => L i + Lp.const p μ (c i)
  have hL'_sum : ∑ i : ι, L' i = I.M x := by
    simp only [L', Finset.sum_add_distrib, hL, sum_lp_const, hc_sum, lp_const_zero, add_zero]
  let u : ι → ℝ := fun i => I.A i (L' i)
  have hu_sum : ∑ i : ι, I.A i (L i) = ∑ i : ι, u i := by
    have hu_eq : ∀ i, u i = I.A i (L i) + c i :=
      fun i => (I.coherent i).translation (L i) (c i)
    simp_rw [hu_eq]
    rw [Finset.sum_add_distrib, hc_sum, add_zero]
  refine ⟨u, L', x, hu_sum, hL'_sum, fun i => ⟨?_, le_rfl⟩⟩
  change I.v i ≤ I.A i (L' i)
  rw [(I.coherent i).translation (L i) (c i)]
  by_cases hi : i = i₀
  · subst hi
    simp only [c, ite_true]
    have hsplit_v : I.v i + ∑ j ∈ Finset.univ.erase i, I.v j = ∑ j : ι, I.v j :=
      Finset.add_sum_erase Finset.univ I.v (Finset.mem_univ i)
    have hsplit_A : I.A i (L i) + ∑ j ∈ Finset.univ.erase i, I.A j (L j) =
        ∑ j : ι, I.A j (L j) :=
      Finset.add_sum_erase Finset.univ (fun j => I.A j (L j)) (Finset.mem_univ i)
    rw [Finset.sum_sub_distrib]
    linarith
  · simp only [c, if_neg hi]
    linarith

theorem sum_A_le_z {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [Nonempty ι] {I : Instance μ p X ι} (hAtt : I.Attained)
    (x : X) (L : ι → Lp ℝ p μ) (hL : ∑ i, L i = I.M x) :
    ∑ i, I.A i (L i) ≤ I.z := by
  have hgreat := isGreatest_z hAtt
  obtain ⟨ustar, _, _, hz_sum, _, huv_star⟩ := hgreat.1
  have hv_le_z : ∑ i, I.v i ≤ I.z := by
    rw [hz_sum]
    exact Finset.sum_le_sum fun i _ => (huv_star i).1
  by_contra hgt
  push Not at hgt
  have hmem := mem_totals_of_sum_v_le I x L hL (hv_le_z.trans hgt.le)
  exact not_le_of_gt hgt (hgreat.2 hmem)

end RiskBargaining.Lemma5Proof

open RiskBargaining.Lemma5Proof in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} [Fintype ι] [Nonempty ι] (I I' : Instance μ p X ι)
    (hM : I'.M = I.M) (hA : I'.A = I.A) :
    (I.Admissible → (∀ i, 0 < I'.v i) → ∑ i, I'.v i ≤ I.z → I'.Admissible ∧ I'.z = I.z) ∧
      (I.Admissible → I'.Admissible → I'.z = I.z) := by
  constructor
  · intro hI hv' hsum_v'
    have hgreat := isGreatest_z hI.2
    obtain ⟨ustar, Lstar, xstar, hz_sum, hL_sum, huv_star⟩ := hgreat.1
    have hA_ge : I.z ≤ ∑ i, I.A i (Lstar i) := by
      rw [hz_sum]
      exact Finset.sum_le_sum fun i _ => (huv_star i).2
    have hA_le : ∑ i, I.A i (Lstar i) ≤ I.z := sum_A_le_z hI.2 xstar Lstar hL_sum
    have hA_eq : ∑ i, I'.A i (Lstar i) = I.z := by
      rw [hA]; exact le_antisymm hA_le hA_ge
    have hL'_sum : ∑ i, Lstar i = I'.M xstar := by rw [hM]; exact hL_sum
    have hz_mem' : I.z ∈ I'.totals := by
      rw [← hA_eq]
      exact mem_totals_of_sum_v_le I' xstar Lstar hL'_sum (hA_eq.symm ▸ hsum_v')
    have hz_ub' : ∀ t ∈ I'.totals, t ≤ I.z := by
      rintro t ⟨u', L', x', rfl, hL', huv'⟩
      have h1 : ∑ i, u' i ≤ ∑ i, I'.A i (L' i) := Finset.sum_le_sum fun i _ => (huv' i).2
      rw [hA] at h1
      rw [hM] at hL'
      exact h1.trans (sum_A_le_z hI.2 x' L' hL')
    have hgreat' : IsGreatest I'.totals I.z := ⟨hz_mem', hz_ub'⟩
    have hz'_eq : I'.z = I.z :=
      le_antisymm (csSup_le ⟨I.z, hgreat'.1⟩ hgreat'.2) (le_csSup ⟨I.z, hgreat'.2⟩ hgreat'.1)
    exact ⟨⟨hv', ⟨I.z, hgreat'⟩⟩, hz'_eq⟩
  · intro hI hI'
    obtain ⟨ustar, Lstar, xstar, hz_sum, hL_sum, huv_star⟩ := (isGreatest_z hI.2).1
    obtain ⟨ustar', Lstar', xstar', hz'_sum, hL'_sum, huv_star'⟩ := (isGreatest_z hI'.2).1
    have hle1 : I.z ≤ I'.z := by
      have h1 : I.z ≤ ∑ i, I.A i (Lstar i) := by
        rw [hz_sum]; exact Finset.sum_le_sum fun i _ => (huv_star i).2
      have h2 : ∑ i, I'.A i (Lstar i) ≤ I'.z :=
        sum_A_le_z hI'.2 xstar Lstar (by rw [hM]; exact hL_sum)
      rw [hA] at h2
      exact h1.trans h2
    have hle2 : I'.z ≤ I.z := by
      have h1 : I'.z ≤ ∑ i, I'.A i (Lstar' i) := by
        rw [hz'_sum]; exact Finset.sum_le_sum fun i _ => (huv_star' i).2
      have h2 : ∑ i, I.A i (Lstar' i) ≤ I.z :=
        sum_A_le_z hI.2 xstar' Lstar' (by rw [← hM]; exact hL'_sum)
      rw [← hA] at h2
      exact h1.trans h2
    exact le_antisymm hle2 hle1
