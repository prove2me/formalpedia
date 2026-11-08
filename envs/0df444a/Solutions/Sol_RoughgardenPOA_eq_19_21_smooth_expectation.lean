-- Prove2me | solution 1 for RoughgardenPOA.eq_19_21_smooth_expectation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:07:39.419325+00:00
-- url     : https://prove2.me/submissions/6cb4f462-f323-437e-adf9-8bbb6f7a83e6

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_IsSmooth

open MeasureTheory

open RoughgardenPOA in
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) (hsm : IsSmooth C lam mu)
    (σ : MeasureTheory.Measure (∀ i, S i)) [MeasureTheory.IsProbabilityMeasure σ]
    (sStar : ∀ i, S i)
    (hC : ∀ i, MeasureTheory.Integrable (C i) σ)
    (hdev : ∀ i, MeasureTheory.Integrable (fun s => C i (Function.update s i (sStar i))) σ) :
    ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ ≤
      lam * objective C sStar + mu * ∫ s, objective C s ∂σ := by
  have hsum : Integrable (fun s => ∑ i, C i (Function.update s i (sStar i))) σ :=
    integrable_finsetSum _ (fun i _ => hdev i)
  have hobj : Integrable (fun s => objective C s) σ := by
    unfold objective
    exact integrable_finsetSum _ (fun i _ => hC i)
  have hrhs : Integrable (fun s => lam * objective C sStar + mu * objective C s) σ :=
    (integrable_const _).add (hobj.const_mul mu)
  have e1 : ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ
      = ∫ s, ∑ i, C i (Function.update s i (sStar i)) ∂σ :=
    (integral_finsetSum _ (fun i _ => hdev i)).symm
  have e2 : ∫ s, (lam * objective C sStar + mu * objective C s) ∂σ
      = lam * objective C sStar + mu * ∫ s, objective C s ∂σ := by
    rw [integral_add (integrable_const _) (hobj.const_mul mu),
      integral_const_mul mu (objective C)]
    simp
  rw [e1, ← e2]
  exact integral_mono hsum hrhs (fun s => hsm s sStar)
