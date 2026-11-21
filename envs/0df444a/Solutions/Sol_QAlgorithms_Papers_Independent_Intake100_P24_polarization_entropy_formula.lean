-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P24.polarization_entropy_formula
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T15:00:15.373466+00:00
-- url     : https://prove2.me/submissions/dec90a9b-e3b1-45ca-85ac-361b17f9081d

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩


theorem AuxPE_mode_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ modeEntropy x := by
  unfold modeEntropy
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · have h1 : Real.log x ≤ Real.log (x + 1) := Real.log_le_log h (by linarith)
    have h2 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
    nlinarith

theorem _root_.solution (kB : ℝ) (hkB : 0 < kB)
    (S : PolarizationMatrix) (alpha : JonesVector) (hS : S.PosSemidef)
    (hCov : (S - jonesOuter alpha).PosSemidef) :
    polarizationEntropy kB S alpha hCov =
      let A := S - jonesOuter alpha
      ENNReal.ofReal (kB *
        (((A + 1) * cfc Real.log (A + 1) - A * cfc Real.log A).trace.re)) := by
  show _ = ENNReal.ofReal (kB * ((((S - jonesOuter alpha) + 1) * cfc Real.log ((S - jonesOuter alpha) + 1)
    - (S - jonesOuter alpha) * cfc Real.log (S - jonesOuter alpha)).trace.re))
  unfold polarizationEntropy
  have hA := hCov.isHermitian
  set A := S - jonesOuter alpha with hAd
  have hsa : IsSelfAdjoint A := hA
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f => hfin.continuousOn f
  have hc' : ∀ (g f : ℝ → ℝ), ContinuousOn g (f '' spectrum ℝ A) :=
    fun g f => (hfin.image f).continuousOn g
  have e1 : cfc (fun x : ℝ => x + 1) A = A + 1 := by
    rw [cfc_add_const (1 : ℝ) (fun x => x) A (hc _), cfc_id' ℝ A, map_one]
  have e2 : cfc Real.log (A + 1) = cfc (fun x => Real.log (x + 1)) A := by
    rw [← e1]; exact (cfc_comp' Real.log (fun x => x + 1) A (hc' _ _) (hc _)).symm
  have e3 : (A + 1) * cfc Real.log (A + 1) = cfc (fun x => (x + 1) * Real.log (x + 1)) A := by
    rw [e2, ← e1, cfc_mul (fun x : ℝ => x + 1) (fun x => Real.log (x + 1)) A (hc _) (hc _)]
  have e4 : A * cfc Real.log A = cfc (fun x => x * Real.log x) A := by
    have := cfc_mul (fun x : ℝ => x) Real.log A (hc _) (hc _)
    rw [cfc_id' ℝ A] at this
    exact this.symm
  have e5 : (A + 1) * cfc Real.log (A + 1) - A * cfc Real.log A = cfc modeEntropy A := by
    rw [e3, e4, ← cfc_sub _ _ A (hc _) (hc _)]
    rfl
  have htr : ((A + 1) * cfc Real.log (A + 1) - A * cfc Real.log A).trace.re =
      ∑ i, modeEntropy (hA.eigenvalues i) := by
    rw [e5, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
    simp
  rw [htr, ENNReal.ofReal_mul hkB.le, ENNReal.ofReal_sum_of_nonneg]
  intro i _
  exact AuxPE_mode_nonneg _ (hCov.eigenvalues_nonneg i)

end QAlgorithms.Papers.Independent.Intake100.P24

end
