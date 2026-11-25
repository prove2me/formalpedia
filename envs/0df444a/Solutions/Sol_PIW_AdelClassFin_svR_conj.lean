-- Prove2me | solution 1 for PIW.AdelClassFin.svR_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:50.298102+00:00
-- url     : https://prove2.me/submissions/e6fecd96-d8e1-4846-b854-82249d2c1184

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
import Theorems.Thm_PIW_AdelClassFin_svR_entry
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
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution {m N : ℕ} (e : Fin N → Fin m → E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (φ : E →+* ℂ) (hc : H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)) :
    (svP e (ComplexEmbedding.conjugate φ))ᴴ * H (ComplexEmbedding.conjugate φ) *
        svP e (ComplexEmbedding.conjugate φ) = ((svP e φ)ᴴ * H φ * svP e φ).map (starRingEnd ℂ) := by
  ext i j
  rw [hc, Matrix.map_apply, svR_entry, svR_entry]
  simp only [svP, Matrix.of_apply, Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, map_sum,
    map_mul, starRingEnd_apply, star_star]
end PIW.AdelClassFin
