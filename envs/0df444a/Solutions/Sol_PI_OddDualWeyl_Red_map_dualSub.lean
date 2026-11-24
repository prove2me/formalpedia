-- Prove2me | solution 1 for PI.OddDualWeyl.Red.map_dualSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:07.28594+00:00
-- url     : https://prove2.me/submissions/c05f3f32-38e9-4a48-96f8-75e352f5dfc1

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
private theorem dualM_map_mvPolynomial_map {S : Type*} [CommRing S] (ψ : R →+* S) :
    (PI.OddDualWeyl.dualM R k).map (MvPolynomial.map ψ) = PI.OddDualWeyl.dualM S k := by
  refine Matrix.ext fun i j => ?_
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.map ψ) (PI.OddDualWeyl.genM R k)) (Fin.rev j)) i
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, genM_map_mvPolynomial_map] at h
  simpa [PI.OddDualWeyl.dualM] using h
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
theorem _root_.solution {S : Type*} [CommRing S] (ψ : R →+* S) (q : MvPolynomial (Fin k × Fin k) R) :
    map ψ (dualSub R k q) = dualSub S k (map ψ q) := by
  have h : (MvPolynomial.map ψ).comp (PI.OddDualWeyl.dualSub R k).toRingHom =
      (PI.OddDualWeyl.dualSub S k).toRingHom.comp (MvPolynomial.map ψ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [PI.OddDualWeyl.dualSub]
    · intro v
      have h1 := congrFun (congrFun (dualM_map_mvPolynomial_map (k := k) ψ) v.1) v.2
      simp only [Matrix.map_apply] at h1
      simp [PI.OddDualWeyl.dualSub, h1]
  simpa using DFunLike.congr_fun h q
end PI.OddDualWeyl.Red
