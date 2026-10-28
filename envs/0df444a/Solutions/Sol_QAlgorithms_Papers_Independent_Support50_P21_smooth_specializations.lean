-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P21.smooth_specializations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:28:03.050462+00:00
-- url     : https://prove2.me/submissions/ee127e89-0f04-4ab1-8b92-d34ec960e172

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Support50 QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- PDF pp.4,7: literal smooth substitutions, retaining the original marginals
and the paper's rank-based max convention. These are definitional identities. -/
theorem solution (eps : ℝ) (heps : 0 ≤ eps)
    (rho : Mat I) (hrho : IsDensityMatrix rho)
    (rhoAB : Mat (I × J)) (hAB : IsDensityMatrix rhoAB)
    (sigmaB : Mat J) (hB : IsDensityMatrix sigmaB) :
    smoothHMin eps rho = -traceSmoothMax eps rho 1 ∧
    smoothHMax eps rho = -traceSmoothMin eps rho 1 ∧
    smoothConditionalMin eps rhoAB sigmaB =
      -traceSmoothMax eps rhoAB (Matrix.kronecker (1 : Mat I) sigmaB) ∧
    smoothConditionalMax eps rhoAB sigmaB =
      -traceSmoothMin eps rhoAB (Matrix.kronecker (1 : Mat I) sigmaB) ∧
    smoothMutualMin eps rhoAB =
      traceSmoothMin eps rhoAB (Matrix.kronecker (traceRight rhoAB) (traceLeft rhoAB)) ∧
    smoothMutualMax eps rhoAB =
      traceSmoothMax eps rhoAB (Matrix.kronecker (traceRight rhoAB) (traceLeft rhoAB)) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Statements


end

