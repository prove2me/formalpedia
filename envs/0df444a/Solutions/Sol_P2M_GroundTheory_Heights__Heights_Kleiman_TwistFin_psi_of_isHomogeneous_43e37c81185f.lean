-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_of_isHomogeneous_43e37c81185f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:56.601506+00:00
-- url     : https://prove2.me/submissions/7083e78a-1bb6-4087-ad15-264184444693

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_algebraMap_LA_e2e747c45c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coneGen_of_isHomogeneous_d90e26b2f3c5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution {h : Sy S r} {b : ℕ} (hh : h.IsHomogeneous b) :
    psi η S h = single ((0 : ℤ), (b : ℤ)) (aeval η h) := by
  have key : (psi η S).toRingHom = (kapU (Ω := Ω)).toRingHom.comp (coneGen (S := S) η).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change psi η S (C a) = kapU ((coneGen (S := S) η) (C a))
      rw [psi, aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, kapU,
        Polynomial.aeval_C, coe_algebraMap, Function.comp_apply, algebraMap_LA, Algebra.algebraMap_self,
        RingHom.id_apply]
      rfl
    · intro j
      change psi η S (X j) = kapU (coneGen η (X j))
      rw [psi_X, coneGen, aeval_X, kapU, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, coe_algebraMap,
        Function.comp_apply, single_mul_single]
      simp
  have := congrArg (fun g => g h) key
  change psi η S h = kapU (coneGen (S := S) η h) at this
  rw [this, coneGen_of_isHomogeneous η hh, kapU, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    coe_algebraMap, Function.comp_apply, single_pow, single_mul_single]
  simp [MvPolynomial.aeval_def]
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
