-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.den_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:47.822427+00:00
-- url     : https://prove2.me/submissions/fbef8001-7013-4ac5-9a96-cceafe6798a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :
    ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g l j ∈ Oh F E := by
  classical
  choose mf hmf hmO using fun p : Fin M × Fin M => den (g p.1 p.2)
  refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
  rw [hq, mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _
end PI.UnitaryGroupMassFormula.UJClassFin
