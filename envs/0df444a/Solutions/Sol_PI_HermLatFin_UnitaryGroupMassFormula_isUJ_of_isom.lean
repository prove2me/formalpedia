-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.isUJ_of_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:24.94924+00:00
-- url     : https://prove2.me/submissions/390dd215-5071-4252-8d79-8e80b3389f0b

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HformTracePos
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hform_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexOrder
noncomputable section
open PI PI.HermLatFin PI.HermLatFin.UnitaryGroupMassFormula
variable {E : Type} [Field E] [NumberField E]
variable [StarRing E] {n : ℕ}
namespace PI.HermLatFin.UnitaryGroupMassFormula
theorem _root_.solution (σ : E →+* E) (hst : ∀ a : E, star a = σ a)
    (J : Matrix (Fin n) (Fin n) E) (g : (Fin n → E) →ₗ[E] (Fin n → E))
    (hg : ∀ x y, hform J (g x) (g y) = hform J x y) :
    IsUJ σ J (LinearMap.toMatrix' g) := by
  ext a b
  have h := hg (Pi.single a 1) (Pi.single b 1)
  rw [hform_apply, hform_apply] at h
  simp only [← LinearMap.toMatrix'_apply, hst] at h
  have hr : ∑ i, ∑ j, σ ((Pi.single a 1 : Fin n → E) i) * J i j * (Pi.single b 1 : Fin n → E) j = J a b := by
    simp [Pi.single_apply, apply_ite σ]
  rw [hr] at h
  rw [← h]
  simp only [IsUJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end PI.HermLatFin.UnitaryGroupMassFormula
