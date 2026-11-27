-- Prove2me | solution 1 for P2M_GlobalTheory_PeriodRowsCompare_modelsEquiv___da8a0362d520
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:47.124151+00:00
-- url     : https://prove2.me/submissions/041327da-18d9-4598-8ad6-a793336d6b81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModelBaseTrivModels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodRowsCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}
namespace GlobalTheory.PeriodRowsCompare
theorem _root_.solution (M : Rows.ModelsOf F r) : (modelsEquiv F r M).φ = M.φ := rfl
end GlobalTheory.PeriodRowsCompare
