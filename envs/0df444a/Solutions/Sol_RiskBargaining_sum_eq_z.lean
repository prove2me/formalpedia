-- Prove2me | solution 1 for RiskBargaining.sum_eq_z
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:24:06.312028+00:00
-- url     : https://prove2.me/submissions/67d916e0-086c-4a05-bb4a-a6e74fef41d5

import Mathlib
import Definitions.Def_RiskBargaining_IsBargainingSolution
import Definitions.Def_RiskBargaining_PAR
import Definitions.Def_RiskBargaining_Instance_z

open MeasureTheory
open scoped ENNReal

open RiskBargaining in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (F : Rule μ p X) (hF : IsBargainingSolution F) (hPAR : PAR F)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι)
    (hI : I.Admissible) :
    ∑ i, F ι I i = I.z := by
  obtain ⟨hv, z0, hz0⟩ := hI
  have hadm : I.Admissible := ⟨hv, z0, hz0⟩
  have hz : I.z = z0 := hz0.csSup_eq
  rw [hz]
  obtain ⟨x, L, hL, hb⟩ := hF ι I hadm
  have hmem : ∑ i, F ι I i ∈ I.totals := ⟨F ι I, L, x, rfl, hL, hb⟩
  refine le_antisymm (hz0.2 hmem) ?_
  by_contra hlt
  push_neg at hlt
  obtain ⟨u, Ls, xs, hu, hLs, hbs⟩ := hz0.1
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set δ : ℝ := (z0 - ∑ i, F ι I i) / Fintype.card ι with hδ
  have hδpos : 0 < δ := div_pos (by linarith) hn
  set c : ι → ℝ := fun i => F ι I i + δ - u i with hc
  have hnδ : (Fintype.card ι : ℝ) * δ = z0 - ∑ i, F ι I i := by
    rw [hδ]; field_simp
  have hcsum : ∑ i, c i = 0 := by
    simp only [hc, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    linarith [hu]
  have hu' : (fun i => F ι I i + δ) ∈ I.U := by
    refine ⟨xs, fun i => Ls i + Lp.const p μ (c i), ?_, fun i => ⟨?_, ?_⟩⟩
    · rw [Finset.sum_add_distrib, ← map_sum, hcsum, map_zero, add_zero, hLs]
    · show I.v i ≤ F ι I i + δ
      linarith [(hb i).1]
    · show F ι I i + δ ≤ I.A i (Ls i + Lp.const p μ (c i))
      rw [(I.coherent i).translation]
      have := (hbs i).2
      simp only [hc]
      linarith
  obtain ⟨j, hj⟩ := hPAR ι I hadm _ hu' ⟨Classical.arbitrary ι,
    show F ι I _ < F ι I _ + δ by linarith⟩
  have hj' : F ι I j + δ < F ι I j := hj
  linarith
