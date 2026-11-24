-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.low_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:55:40.636964+00:00
-- url     : https://prove2.me/submissions/31a1387f-657a-4f89-b009-a7b8d81ed8fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_single_mem


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
theorem _root_.solution (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {w : Fin M → Af F ⊗[F] E} (hw : ∀ i, w i ∈ Oh F E) : k • w ∈ latHat F E L := by
  rw [← Finset.univ_sum_single (k • w)]
  exact AddSubgroup.sum_mem _ fun i _ => single_mem L hk (hw i) i
end PI.UnitaryGroupMassFormula.UJClassFin
