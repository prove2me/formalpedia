-- Prove2me | solution 1 for PI.OddDualWeyl.Hom.det_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:44.337798+00:00
-- url     : https://prove2.me/submissions/df9f775c-dc6c-450e-95bb-f0777eb16f52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightMultiplicity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl
open PI.OddDualWeyl.Hom
variable {R : Type} [CommRing R] {k : ℕ}
variable {wt : Fin k × Fin k → ℤ} {δ : ℤ}
namespace PI.OddDualWeyl.Hom
theorem _root_.solution {M' : Type*} [AddCommMonoid M'] {w : Fin k × Fin k → M'} {s : ℕ}
    (N : Matrix (Fin s) (Fin s) (MvPolynomial (Fin k × Fin k) R)) (r : Fin s → M')
    (h : ∀ p q, IsWeightedHomogeneous w (N p q) (r p)) :
    IsWeightedHomogeneous w N.det (∑ p, r p) := by
  rw [Matrix.det_apply, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hprod : (∏ i, N (σ i) i) ∈ weightedHomogeneousSubmodule R w (∑ p, r p) := by
    rw [mem_weightedHomogeneousSubmodule]
    have := IsWeightedHomogeneous.prod Finset.univ (fun i => N (σ i) i) (fun i => r (σ i))
      (fun i _ => h (σ i) i)
    rwa [Equiv.sum_comp σ r] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rw [Units.neg_smul, one_smul]
    exact Submodule.neg_mem _ hprod
end PI.OddDualWeyl.Hom
