-- Prove2me | solution 1 for PI.FJMX.leadT_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:01.103073+00:00
-- url     : https://prove2.me/submissions/0b7af105-e5b4-41bf-9d56-773652d603cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
import Theorems.Thm_PI_FJMX_prod_castLE_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m : ℕ}
namespace PI.FJMX
theorem _root_.solution (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (t : ℕ) (ht : t ≤ m) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) t) =
      ∏ i : Fin m, X (ι (i, i)) ^ (if i.val < t then 1 else 0) := by
  classical
  unfold PI.FJM.leadT
  rw [dif_pos ⟨ht, ht⟩, AlgHom.map_det]
  have hD : (aeval (PI.FJMB.killS (PI.FJMB.offD ι))).mapMatrix ((blkM ι).submatrix (Fin.castLE ht) (Fin.castLE ht)) =
      Matrix.diagonal (fun i : Fin t => (X (ι (Fin.castLE ht i, Fin.castLE ht i)) : MvPolynomial σ ℂ)) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, blkM, Matrix.of_apply, aeval_X,
      Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      have : ι (Fin.castLE ht i, Fin.castLE ht i) ∉ PI.FJMB.offD ι := by
        rintro ⟨i', k', he, hne⟩
        have := hι he
        simp only [Prod.mk.injEq] at this
        apply hne
        rw [this.1, this.2]
      simp [PI.FJMB.killS, this]
    · have : ι (Fin.castLE ht i, Fin.castLE ht j) ∈ PI.FJMB.offD ι := by
        refine ⟨Fin.castLE ht i, Fin.castLE ht j, rfl, ?_⟩
        simp only [Fin.coe_castLE]
        exact fun h => hij (Fin.ext h)
      simp [PI.FJMB.killS, this, hij]
  rw [hD, Matrix.det_diagonal]
  exact prod_castLE_eq ht (fun i => (X (ι (i, i)) : MvPolynomial σ ℂ))
end PI.FJMX
