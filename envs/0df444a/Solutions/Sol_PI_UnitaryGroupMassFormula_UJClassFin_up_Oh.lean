-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.up_Oh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:58:21.042742+00:00
-- url     : https://prove2.me/submissions/c881a23a-de74-47e7-b57f-8d59b0583cc4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_nsmul_tmul_F
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh


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
theorem _root_.solution (L : Set (Fin M → E)) {u : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    {w : Fin M → Af F ⊗[F] E} (hw : w ∈ latHat F E L) (i : Fin M) : u • w i ∈ Oh F E := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    show u • (a ⊗ₜ[F] x i) ∈ Oh F E
    rw [nsmul_tmul_F]
    exact tmul_mem_Oh ha (hu x hx i)
  | zero => show u • (0 : Af F ⊗[F] E) ∈ Oh F E; rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h1 h2 => show u • (w i + w' i) ∈ Oh F E; rw [smul_add]; exact add_mem h1 h2
  | neg w _ h1 => show u • (-w i) ∈ Oh F E; rw [smul_neg]; exact neg_mem h1
end PI.UnitaryGroupMassFormula.UJClassFin
