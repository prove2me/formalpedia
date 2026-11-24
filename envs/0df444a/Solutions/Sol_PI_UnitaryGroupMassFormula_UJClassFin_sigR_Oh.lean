-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.sigR_Oh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:37:23.95779+00:00
-- url     : https://prove2.me/submissions/b288708b-b109-491e-81a2-c29599c1f436

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_int_sigma
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}
variable (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution {z : Af F ⊗[F] E} (hz : z ∈ Oh F E) : sigR (Af F) σ z ∈ Oh F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, e, he, rfl⟩ := hz
    have e1 : sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [e1]
    exact tmul_mem_Oh ha (by simpa using int_sigma (σ : E →+* E) he)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1
end PI.UnitaryGroupMassFormula.UJClassFin
