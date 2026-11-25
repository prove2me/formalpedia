-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf.chi_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:49.518899+00:00
-- url     : https://prove2.me/submissions/07b83310-1565-4445-a6fd-143d86bf2e1a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_GLDelta
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_dU_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_GLChiPf_chi_single_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
open Matrix
variable {k : Type} [Field k] {n : ℕ}
namespace PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
theorem _root_.solution (χ : GL (Fin n) k →* ℚ) (hpos : ∀ g, 0 < χ g)
    (hz : ∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1)
    (i : Fin n) (d : kˣ) : χ (dU (Pi.mulSingle i d)) = 1 := by
  have hn : n ≠ 0 := by rintro rfl; exact i.elim0
  have hsc : Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d = dU (fun _ => d) := by
    apply Units.ext
    rw [dU_val]
    ext a b
    simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_apply]
  have hprod : (fun _ : Fin n => d) = ∏ l, Pi.mulSingle l d := (Finset.univ_prod_mulSingle (fun _ => d)).symm
  have h1 : (χ.comp dU) (fun _ => d) = 1 := by rw [MonoidHom.comp_apply, ← hsc]; exact hz d
  rw [hprod, map_prod] at h1
  simp only [MonoidHom.comp_apply] at h1
  have h2 : ∏ l : Fin n, χ (dU (Pi.mulSingle l d)) = ∏ _l : Fin n, χ (dU (Pi.mulSingle i d)) :=
    Finset.prod_congr rfl (fun l _ => chi_single_eq χ l i d)
  rw [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact (pow_eq_one_iff_of_nonneg (hpos _).le hn).mp h1
end PI.UnitaryGroupMassFormula.AdIndexEq.GLChiPf
