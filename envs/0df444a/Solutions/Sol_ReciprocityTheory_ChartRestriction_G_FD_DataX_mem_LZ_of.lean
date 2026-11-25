-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.mem_LZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:53.370179+00:00
-- url     : https://prove2.me/submissions/d783f1a8-8d47-4e32-af15-800e4f218a8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_cc_c0E

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (w : Fin 2 → Fin 2 → E) (hwi : ∀ i k, IsIntegral ℤ (w i k))
    (hwh : ∀ i k, cc (w i k) = w k i) :
    X.embH (Matrix.of fun i k => X.c0E * w i k) ∈ X.LZ X.g := by
  refine ⟨Matrix.of fun i k => X.c0E * w i k, fun i k => ?_, fun i k => ⟨w i k, hwi i k, rfl⟩, rfl⟩
  show cc (X.c0E * w i k) = X.c0E * w k i
  have hm : cc (X.c0E * w i k) = cc X.c0E * cc (w i k) := map_mul (IsCMField.complexConj E) _ _
  rw [hm, X.cc_c0E, hwh i k]
end ReciprocityTheory.ChartRestriction.G.FD.DataX
