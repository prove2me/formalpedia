-- Prove2me | solution 1 for PI.HermLatFin.UnitaryGroupMassFormula.hform_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:18.576858+00:00
-- url     : https://prove2.me/submissions/43f6e196-a819-4729-8224-94fbb3e94f8c

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
theorem _root_.solution (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, star (J i j) = J j i) :
    (hform J).IsSymm := by
  refine LinearMap.IsSymm.mk fun x y => ?_
  simp only [hform_apply, starRingEnd_apply, star_sum, star_mul', star_star, hJ, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end PI.HermLatFin.UnitaryGroupMassFormula
