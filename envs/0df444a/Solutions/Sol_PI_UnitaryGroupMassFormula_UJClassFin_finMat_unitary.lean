-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.finMat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:31.283049+00:00
-- url     : https://prove2.me/submissions/78717064-69e4-4364-b889-493c8c7cd30f

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
theorem _root_.solution (h : HA (AF F) σ J) :
    cT (sigR (Af F) σ) (finMat σ J h) * JR (Af F) J * finMat σ J h = JR (Af F) J := by
  have hm : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  let φ := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
  have hφs : ∀ z, φ (sigR (AF F) σ z) = sigR (Af F) σ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hφJ : (JR (AF F) J).map φ = JR (Af F) J := by
    ext i j
    simp [φ, JR, inclR, Algebra.TensorProduct.map_tmul]
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      (cT (sigR (AF F) σ) X).map φ = cT (sigR (Af F) σ) (X.map φ) := by
    intro X
    ext i j
    simp [cT, hφs]
  have := congrArg (fun X => X.map φ) hm
  simp only [mapAlg_mul, hcT, hφJ] at this
  exact this
end PI.UnitaryGroupMassFormula.UJClassFin
