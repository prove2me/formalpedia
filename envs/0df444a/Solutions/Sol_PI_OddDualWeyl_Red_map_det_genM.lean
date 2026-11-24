-- Prove2me | solution 1 for PI.OddDualWeyl.Red.map_det_genM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:54.158817+00:00
-- url     : https://prove2.me/submissions/173b75b9-8cc5-4c5d-b475-de1b85532dd5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial Matrix
noncomputable section
namespace PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
private theorem genM_map_mvPolynomial_map {S : Type*} [CommRing S] (ψ : R →+* S) :
    (PI.OddDualWeyl.genM R k).map (MvPolynomial.map ψ) = PI.OddDualWeyl.genM S k := by
  ext i j
  simp [PI.OddDualWeyl.genM]
section Field
variable {K : Type*} [Field K] {k : ℕ}
end Field
end PI.OddDualWeyl.Red
namespace PI.OddDualWeyl
open Red
end PI.OddDualWeyl
end
end

set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution {S : Type*} [CommRing S] (ψ : R →+* S) :
    map ψ (genM R k).det = (genM S k).det := by
  have h := RingHom.map_det (MvPolynomial.map ψ) (PI.OddDualWeyl.genM R k)
  rw [RingHom.mapMatrix_apply, genM_map_mvPolynomial_map] at h
  exact h
end PI.OddDualWeyl.Red
