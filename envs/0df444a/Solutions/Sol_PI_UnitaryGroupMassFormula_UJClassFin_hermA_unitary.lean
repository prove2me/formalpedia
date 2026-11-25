-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.hermA_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:44:27.267882+00:00
-- url     : https://prove2.me/submissions/d36919b1-6c85-46b6-bbe3-d5e3bccf7d4f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermASingleLeft
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
theorem _root_.solution (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hg : cT (sigR (Af F) σ) g * JR (Af F) J * g = JR (Af F) J) (X Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (g.mulVec X) (g.mulVec Y) = hermA σ J X Y := by
  have h1 : (fun i => sigR (Af F) σ ((g.mulVec X) i)) =
      (g.map (sigR (Af F) σ)).mulVec (fun i => sigR (Af F) σ (X i)) := by
    funext i
    exact RingHom.map_mulVec _ g X i
  have e : (g.map (sigR (Af F) σ))ᵀ * (JR (Af F) J * g) = JR (Af F) J := by
    rw [← Matrix.mul_assoc]; exact hg
  unfold hermA
  rw [h1, ← Matrix.vecMul_transpose (g.map (sigR (Af F) σ)), ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, e]
end PI.UnitaryGroupMassFormula.UJClassFin
