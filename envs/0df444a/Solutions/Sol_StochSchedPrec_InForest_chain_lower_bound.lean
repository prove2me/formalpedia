-- Prove2me | solution 1 for StochSchedPrec.InForest.chain_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:36:17.976262+00:00
-- url     : https://prove2.me/submissions/60e27c21-716b-4502-b345-9014a632ae4f

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_Graham
open MeasureTheory ProbabilityTheory

open StochSchedPrec.InForest in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (hPint : ∀ j, Integrable (P j) Pr)
    (σ : (V → ℝ) → (V → ℝ)) (hσ : ∀ p, IsNonneg p → IsFeasibleSchedule A m p (σ p))
    (crit : (V → ℝ) → V → Option V) (hcrit : ∀ p, IsNonneg p → IsCritSelector A p (σ p) (crit p))
    (hℓmeas : ∀ j, AEMeasurable
      (fun ω => chainLen (crit (fun k => P k ω)) (fun k => P k ω) j) Pr) :
    (∀ p, IsNonneg p → ∀ S' : V → ℝ, IsFeasibleSchedule A m p S' →
        ∀ j, chainLen (crit p) p j ≤ S' j + p j) ∧
      ∀ pol : (V → ℝ) → (V → ℝ), IsComparator A m P Pr pol → ∀ j,
        ∫ ω, chainLen (crit (fun k => P k ω)) (fun k => P k ω) j ∂Pr ≤
          ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr := by
  have part1 : ∀ p, IsNonneg p → ∀ S' : V → ℝ, IsFeasibleSchedule A m p S' →
      ∀ j, chainLen (crit p) p j ≤ S' j + p j := by
    intro p hp S' hS'
    have htg : ∀ i j, Relation.TransGen A i j → S' i + p i ≤ S' j := by
      intro i j h
      induction h with
      | single hab => exact hS'.2.1 _ _ hab
      | @tail b c _ hbc ih =>
        have := hS'.2.1 b c hbc
        have := hp b
        linarith
    have haux : ∀ n j, chainLenAux (crit p) p n j ≤ S' j + p j := by
      intro n
      induction n with
      | zero =>
        intro j
        show p j ≤ S' j + p j
        linarith [hS'.1 j]
      | succ n ih =>
        intro j
        rcases h : crit p j with _ | i
        · simp only [chainLenAux, h]
          linarith [hS'.1 j]
        · simp only [chainLenAux, h]
          have hT := ((hcrit p hp j).1 i h).1
          have := htg i j hT
          have := ih i
          linarith
    intro j
    exact haux _ j
  refine ⟨part1, fun pol hpol j => ?_⟩
  have hnn : ∀ p, IsNonneg p → ∀ n j, 0 ≤ chainLenAux (crit p) p n j := by
    intro p hp n
    induction n with
    | zero => intro j; exact hp j
    | succ n ih =>
      intro j
      rcases h : crit p j with _ | i
      · simp only [chainLenAux, h]; exact hp j
      · simp only [chainLenAux, h]; linarith [hp j, ih i]
  have hpω : ∀ ω, IsNonneg (fun k => P k ω) := fun ω k => hP.2.1 k ω
  refine integral_mono_of_nonneg (ae_of_all _ fun ω => hnn _ (hpω ω) _ j) (hpol.2 j)
    (ae_of_all _ fun ω => ?_)
  exact part1 _ (hpω ω) _ (hpol.1.1 _ (hpω ω)) j
