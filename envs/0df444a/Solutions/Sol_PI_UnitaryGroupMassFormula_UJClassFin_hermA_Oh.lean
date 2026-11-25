-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.hermA_Oh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:59:09.91752+00:00
-- url     : https://prove2.me/submissions/38804138-31dd-4230-98db-51fd8e0f7560

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_incl_mem_Oh
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_sigR_Oh
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_Oh_mul
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
theorem _root_.solution {u dJ : ℕ} (hJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j)) {X Y : Fin M → Af F ⊗[F] E}
    (hX : ∀ i, u • X i ∈ Oh F E) (hY : ∀ i, u • Y i ∈ Oh F E) :
    (u * u * dJ) • hermA σ J X Y ∈ Oh F E := by
  have : (u * u * dJ) • hermA σ J X Y = ∑ i, ∑ j,
      sigR (Af F) σ (u • X i) * (inclR (Af F) ((dJ : E) * J i j) * (u • Y j)) := by
    simp only [hermA, dotProduct, Matrix.mulVec, JR, Matrix.map_apply, Finset.mul_sum, Finset.smul_sum,
      map_nsmul, map_mul, map_natCast, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ =>
    Oh_mul (sigR_Oh σ (hX i)) (Oh_mul (incl_mem_Oh (hJ i j)) (hY j))
end PI.UnitaryGroupMassFormula.UJClassFin
