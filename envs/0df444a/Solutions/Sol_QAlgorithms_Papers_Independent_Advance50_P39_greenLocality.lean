-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P39.greenLocality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T11:13:07.923141+00:00
-- url     : https://prove2.me/submissions/02990837-2074-4177-85f1-0f67e701df84

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P39
noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix ComplexOrder Topology Matrix.Norms.L2Operator

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich semigroupEvolution)

namespace QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

theorem s109_greenLocality {n : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (B : Superoperator n) (hpopulation : ∀ X i, (B X) i i = 0) :
    greenContribution D B rho0 = 0 := by
  unfold greenContribution recombinationHamiltonian
  set Y := B (Ring.inverse (transportGenerator D) rho0) with hY
  have h : (referenceInverse D Y).trace = 0 := by
    unfold Matrix.trace
    apply Finset.sum_eq_zero
    intro i _
    simp [referenceInverse, Matrix.diag, hY, hpopulation]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, h]
  simp

end QAlgorithms.Papers.Independent.Advance50.P39

open QAlgorithms.Papers.Independent.Advance50.P39

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {n : ℕ} (D : TransportData n)
    (rho0 : SiteMatrix n) (hstate : QAlgorithms.IsDensityMatrix rho0)
    (B : Superoperator n) (hpopulation : ∀ X i, (B X) i i = 0) :
    greenContribution D B rho0 = 0 :=
  s109_greenLocality D rho0 hstate B hpopulation

end
