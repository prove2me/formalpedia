-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.zmat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:25:05.814286+00:00
-- url     : https://prove2.me/submissions/a1d08142-5218-4edf-a8c7-3573e89bcea7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_mul_Am

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) : (X.zmat u b τ).det = 1 := by
  rw [X.zmat_eq, Matrix.det_one_add_mul_comm, X.Cm_mul_Am u hu, add_zero, Matrix.det_one]
end ReciprocityTheory.ChartRestriction.G.FD.Data
