-- Prove2me | solution 1 for RoughgardenPOA.theorem_3_2_fixed_pair
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:23:05.461772+00:00
-- url     : https://prove2.me/submissions/481e9363-b050-43d0-8046-08b7ae614d20

import Mathlib
import Definitions.Def_RoughgardenPOA_objective
import Definitions.Def_RoughgardenPOA_IsSmooth
import Definitions.Def_RoughgardenPOA_IsCCE

open RoughgardenPOA in
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) (hsm : IsSmooth C lam mu) (hmu : mu < 1)
    (σ : MeasureTheory.Measure (∀ i, S i)) (hσ : IsCCE C σ) (sStar : ∀ i, S i) :
    ∫ s, objective C s ∂σ ≤ lam / (1 - mu) * objective C sStar := by
  obtain ⟨hprob, hint, hint2, hcce⟩ := hσ
  haveI := hprob
  have hobj : ∫ s, objective C s ∂σ = ∑ i, ∫ s, C i s ∂σ := by
    unfold objective
    exact MeasureTheory.integral_finsetSum _ (fun i _ => hint i)
  have hdev : ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ =
      ∫ s, ∑ i, C i (Function.update s i (sStar i)) ∂σ :=
    (MeasureTheory.integral_finsetSum _ (fun i _ => hint2 i (sStar i))).symm
  have hobjint : MeasureTheory.Integrable (fun s => objective C s) σ := by
    unfold objective
    exact MeasureTheory.integrable_finsetSum _ (fun i _ => hint i)
  have hsmooth : ∫ s, ∑ i, C i (Function.update s i (sStar i)) ∂σ ≤
      ∫ s, (lam * objective C sStar + mu * objective C s) ∂σ := by
    apply MeasureTheory.integral_mono
    · exact MeasureTheory.integrable_finsetSum _ (fun i _ => hint2 i (sStar i))
    · exact (MeasureTheory.integrable_const _).add (hobjint.const_mul mu)
    · intro s
      exact hsm s sStar
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _) (hobjint.const_mul mu),
    MeasureTheory.integral_const, MeasureTheory.integral_const_mul] at hsmooth
  simp only [MeasureTheory.probReal_univ, one_smul] at hsmooth
  have h1 : ∫ s, objective C s ∂σ ≤ lam * objective C sStar + mu * ∫ s, objective C s ∂σ := by
    calc ∫ s, objective C s ∂σ = ∑ i, ∫ s, C i s ∂σ := hobj
      _ ≤ ∑ i, ∫ s, C i (Function.update s i (sStar i)) ∂σ :=
          Finset.sum_le_sum (fun i _ => hcce i (sStar i))
      _ = _ := hdev
      _ ≤ _ := hsmooth
  have hpos : 0 < 1 - mu := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  linarith
