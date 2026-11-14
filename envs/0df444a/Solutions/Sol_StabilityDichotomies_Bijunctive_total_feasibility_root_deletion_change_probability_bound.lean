-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.total_feasibility_root_deletion_change_probability_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:55:26.285039+00:00
-- url     : https://prove2.me/submissions/24f7823d-fc8a-470c-bb2b-33c61c65fb60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StabilityDichotomies_Bijunctive_outside_first_mask_root_deletion_change_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_inside_first_mask_root_deletion_change_bound
import Theorems.Thm_StabilityDichotomies_Bijunctive_bijunctive_seed_is_probability
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (hI : Satisfiable I) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := bijunctiveSeedMeasure rep I ε
    let G := fun (j : Fin I.constraints.card) (z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
    let F := fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
    let Fminus := fun (j : Fin I.constraints.card) (z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)) =>
      thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
    let mid := fun j z v => decide (literalScore rep (G j z) (F z) z.2.2 (v,false) < literalScore rep (G j z) (F z) z.2.2 (v,true))
    let last := fun j z v => decide (literalScore rep (G j z) (Fminus j z) z.2.2 (v,false) < literalScore rep (G j z) (Fminus j z) z.2.2 (v,true))
    (∑ j : Fin I.constraints.card, ∑ v : V, (μ {z | mid j z v ≠ last j z v}).toReal) ≤
      (2 / ε) * ((maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)) := by
  classical
  let Ω := (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ)
  let μ : Measure Ω := bijunctiveSeedMeasure rep I ε
  let G := fun (j : Fin I.constraints.card) (z : Ω) => thinnedInstance I (fun i => decide (z.1 i ≤ 1 - ε / 2) && decide (i ≠ j))
  let F := fun z : Ω => thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1))
  let Fminus := fun (j : Fin I.constraints.card) (z : Ω) => thinnedInstance I (fun i => decide (z.1 i ≤ z.2.1) && decide (i ≠ j))
  let mid := fun j z v => decide (literalScore rep (G j z) (F z) z.2.2 (v,false) < literalScore rep (G j z) (F z) z.2.2 (v,true))
  let last := fun j z v => decide (literalScore rep (G j z) (Fminus j z) z.2.2 (v,false) < literalScore rep (G j z) (Fminus j z) z.2.2 (v,true))
  let R := fun j v => {z : Ω | mid j z v ≠ last j z v}
  let B := fun j v => {z : Ω | mid j z v ≠ last j z v ∧ ¬ (z.1 j ≤ 1 - ε / 2)}
  let C := fun j v => {z : Ω | mid j z v ≠ last j z v ∧ z.1 j ≤ 1 - ε / 2}
  let D : ℝ := (maxArity Γ * I.constraints.card : ℕ) * (harmonic (Fintype.card (Literal V)) : ℝ)
  haveI : IsProbabilityMeasure μ := bijunctive_seed_is_probability rep I ε hε
  have hpiece (j : Fin I.constraints.card) (v : V) : μ.real (R j v) ≤ μ.real (B j v) + μ.real (C j v) := by
    have hs : R j v ⊆ B j v ∪ C j v := by
      intro z hz
      by_cases h : z.1 j ≤ 1 - ε / 2
      · exact Or.inr ⟨hz,h⟩
      · exact Or.inl ⟨hz,h⟩
    exact (measureReal_mono hs).trans (measureReal_union_le _ _)
  have hb : (∑ j, ∑ v, μ.real (B j v)) ≤ D := outside_first_mask_root_deletion_change_bound rep I hI ε hε hε1
  have hc : (∑ j, ∑ v, μ.real (C j v)) ≤ ((2 - ε) / ε) * D := inside_first_mask_root_deletion_change_bound rep I hI ε hε hε1
  change (∑ j, ∑ v, μ.real (R j v)) ≤ (2 / ε) * D
  calc
    _ ≤ ∑ j, ∑ v, (μ.real (B j v) + μ.real (C j v)) := Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun v _ => hpiece j v))
    _ = (∑ j, ∑ v, μ.real (B j v)) + (∑ j, ∑ v, μ.real (C j v)) := by simp only [Finset.sum_add_distrib]
    _ ≤ D + ((2 - ε) / ε) * D := add_le_add hb hc
    _ = (2 / ε) * D := by field_simp; ring
