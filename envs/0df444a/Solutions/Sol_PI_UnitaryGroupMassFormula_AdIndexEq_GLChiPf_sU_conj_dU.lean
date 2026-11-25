-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.sU_conj_dU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:35:32.514982+00:00
-- url     : https://prove2.me/submissions/dd4bfe38-cce4-4d75-a275-69894e8693d3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_dU_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (hσ : σ.symm = σ) (D : Fin n → kˣ) :
    sU σ hσ * dU D * (sU σ hσ)⁻¹ = dU (D ∘ σ) := by
  apply Units.ext
  show σ.toPEquiv.toMatrix * ((dU D : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * σ.toPEquiv.toMatrix =
    ((dU (D ∘ σ) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [dU_val, dU_val, perm_conj σ hσ, Matrix.submatrix_diagonal_equiv]
  rfl
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
