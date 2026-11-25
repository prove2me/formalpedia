-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.patch_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:45:21.77654+00:00
-- url     : https://prove2.me/submissions/4efef3b7-4033-4d4c-91a6-74ba607d1bde

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_finMat_patch_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_map_mulVec_vinc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Matrix
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (e : ι → AF F ⊗[F] E) (he : ∀ i j, e i * e j = if i = j then e i else 0)
    (hs : ∑ i, e i = 1) (hσe : ∀ i, sigR (AF F) σ (e i) = e i) (γ : ι → GL (Fin M) E)
    (hγ : ∀ i, γ i ∈ UJ (σ : E →+* E) J) (x : Fin M → E) :
    (finMat σ J (patchHA σ J e he hs hσe γ hγ)⁻¹).mulVec (PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) x) =
      ∑ i, finE F E (e i) • PI.UnitaryGroupMassFormula.UJClassFin.vinc (F := F) (((γ i)⁻¹ : GL (Fin M) E).val.mulVec x) := by
  rw [finMat_patch_inv, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mulVec, PI.UnitaryGroupMassFormula.UJClassFin.map_mulVec_vinc]
end PI.UnitaryGroupMassFormula.UJClassMass
