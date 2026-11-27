-- Prove2me | solution 1 for TradingPostNSW.Leontief.Supplement.theorem_D_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:55.75085+00:00
-- url     : https://prove2.me/submissions/978a9eb8-cd05-433f-816c-0c6a06a65010

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

open TradingPostNSW
open TradingPostNSW.Leontief
open TradingPostNSW.Leontief.Supplement

theorem solution : LeontiefPurityFails := by
  classical
  let a : Fin 2 → ℝ := fun j => if j = 0 then 1 else 0
  let c : Fin 2 → ℝ := fun _ => 1 / 2
  have ha (i : Fin 2) : Strategy feeRefutationInstance i a := by
    constructor
    · intro j
      fin_cases j <;> norm_num [a, feeRefutationInstance]
    · norm_num [a, feeRefutationInstance, Fin.sum_univ_two]
  have hc (i : Fin 2) : Strategy feeRefutationInstance i c := by
    constructor
    · intro j
      norm_num [c, feeRefutationInstance]
    · norm_num [c, feeRefutationInstance, Fin.sum_univ_two]
  let μ : MeasureTheory.Measure (Fin 2 → ℝ) :=
    (1 / 2 : ENNReal) • MeasureTheory.Measure.dirac a +
      (1 / 2 : ENNReal) • MeasureTheory.Measure.dirac c
  have hμ : MeasureTheory.IsProbabilityMeasure μ := by
    constructor
    simpa [μ, MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply] using
      ENNReal.inv_two_add_inv_two
  let ν : MeasureTheory.ProbabilityMeasure (Fin 2 → ℝ) := ⟨μ, hμ⟩
  let σ : Fin 2 → MeasureTheory.ProbabilityMeasure (Fin 2 → ℝ) := fun _ => ν
  have hadm (i : Fin 2) : ∀ᵐ b ∂(σ i : MeasureTheory.Measure (Fin 2 → ℝ)),
      Strategy feeRefutationInstance i b := by
    change ∀ᵐ b ∂μ, Strategy feeRefutationInstance i b
    rw [MeasureTheory.ae_add_measure_iff]
    constructor
    · apply MeasureTheory.Measure.ae_smul_measure
      simpa using ha i
    · apply MeasureTheory.Measure.ae_smul_measure
      simpa using hc i
  have hz (i : Fin 2) (s : Fin 2 → Fin 2 → ℝ)
      (hs : Strategy feeRefutationInstance i (s i)) :
      u feeRefutationInstance i (tpAlloc 2 s i) = 0 := by
    have halloc : tpAlloc 2 s i = fun _ => 0 := by
      funext j
      have hb : s i j ≤ 1 := (hs.1 j).2
      have hlt : ¬ (2 : ℝ) ≤ s i j := by linarith
      simp [tpAlloc, effBid, hlt]
    rw [halloc]
    simp [u, D, feeRefutationInstance]
  have hzAE (τ : Fin 2 → MeasureTheory.ProbabilityMeasure (Fin 2 → ℝ))
      (hτ : ∀ i, ∀ᵐ b ∂(τ i : MeasureTheory.Measure (Fin 2 → ℝ)),
        Strategy feeRefutationInstance i b) (i : Fin 2) :
      (fun s => u feeRefutationInstance i (tpAlloc 2 s i)) =ᵐ[joint τ] 0 := by
    have hi : ∀ᵐ s ∂joint τ, Strategy feeRefutationInstance i (s i) :=
      MeasureTheory.Measure.tendsto_eval_ae_ae.eventually (hτ i)
    exact hi.mono fun s hs => hz i s hs
  change Standing feeRefutationInstance ∧ PerfectCompetition feeRefutationInstance ∧ _
  refine ⟨?_, ?_, σ, ?_, ?_⟩
  · constructor
    · decide
    · intro i j; norm_num [feeRefutationInstance]
    · intro i; norm_num [feeRefutationInstance]
    · intro i; simp [D, feeRefutationInstance]
  · intro j
    exact ⟨0, 1, by decide, by norm_num [feeRefutationInstance],
      by norm_num [feeRefutationInstance]⟩
  · refine ⟨hadm, ?_, ?_⟩
    · intro i
      exact (MeasureTheory.integrable_zero _ _ _).congr (hzAE σ hadm i).symm
    · intro i b' hb'
      have hτ : ∀ k, ∀ᵐ b ∂(Function.update σ i (pureBid b') k :
          MeasureTheory.Measure (Fin 2 → ℝ)), Strategy feeRefutationInstance k b := by
        intro k
        by_cases hk : k = i
        · subst k
          simp only [Function.update_self]
          change ∀ᵐ b ∂MeasureTheory.Measure.dirac b', Strategy feeRefutationInstance i b
          simpa using hb'
        · simpa [Function.update_of_ne hk] using hadm k
      refine ⟨(MeasureTheory.integrable_zero _ _ _).congr
        (hzAE (Function.update σ i (pureBid b')) hτ i).symm, ?_⟩
      unfold expPay
      rw [MeasureTheory.integral_congr_ae (hzAE _ hτ i),
        MeasureTheory.integral_congr_ae (hzAE _ hadm i)]
      simp
  · intro hp
    obtain ⟨b, hb⟩ := hp 0
    have hmeasure := congrArg (fun p : MeasureTheory.ProbabilityMeasure (Fin 2 → ℝ) =>
      (p : MeasureTheory.Measure (Fin 2 → ℝ)) {a}) hb
    have hca : c ≠ a := by
      intro h
      have := congrFun h 0
      norm_num [a, c] at this
    by_cases hba : b = a
    · subst b
      norm_num [σ, ν, μ, pureBid, MeasureTheory.Measure.add_apply,
        MeasureTheory.Measure.smul_apply, hca] at hmeasure
    · norm_num [σ, ν, μ, pureBid, MeasureTheory.Measure.add_apply,
        MeasureTheory.Measure.smul_apply, hca, hba] at hmeasure
