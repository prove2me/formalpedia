-- Prove2me | solution 1 for PI.LocLatEq.W.core_smem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:06.037999+00:00
-- url     : https://prove2.me/submissions/cdbe64ab-25ed-4983-89c9-f9f1356e1dcd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreFgOfLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
namespace PI.LocLatEq.W
theorem _root_.solution (A : LocAt F E sig p) {n : ℕ} (S : Submodule A.O (Fin n → A.Ep)) {o : A.Ep}
    (ho : o ∈ A.O) {x : Fin n → A.Ep} (hx : x ∈ S) : o • x ∈ S :=
  S.smul_mem (⟨o, ho⟩ : A.O) hx
end PI.LocLatEq.W
