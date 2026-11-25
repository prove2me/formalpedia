-- Prove2me | solution 1 for PIW.AdelClassFin.svR_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:37.204337+00:00
-- url     : https://prove2.me/submissions/4a17847e-a286-4fe9-8182-fa1b5023dff9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
import Theorems.Thm_PIW_AdelClassFin_svR_entry
import Theorems.Thm_PIW_AdelClassFin_svR_hform
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
theorem _root_.solution (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a)) {m N : ℕ}
    (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) :
    (gramTr J e).map (Rat.castHom ℂ) = ∑ φ, (svP e φ)ᴴ * J.map φ * svP e φ := by
  ext i j
  rw [Matrix.map_apply, Matrix.sum_apply]
  simp_rw [svR_entry]
  simp only [gramTr, svP, Matrix.of_apply, Matrix.map_apply]
  have hcast : ∀ q : ℚ, (Rat.castHom ℂ) q = algebraMap ℚ ℂ q := fun q => by simp
  rw [hcast, trace_eq_sum_embeddings ℂ, ← Equiv.sum_comp (RingHom.equivRatAlgHom E ℂ)]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  exact svR_hform hst J φ (e i) (e j)
end PIW.AdelClassFin
