-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Mmat_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:26:18.8762+00:00
-- url     : https://prove2.me/submissions/1a63dbce-c187-43c8-bcb9-fe34e254b491

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_tau_kappa0

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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (β : Matrix (Fin 2) (Fin 2) E) (τ : X.Ψ) :
    (X.Mmat u β).map τ.1 = X.zmat u (X.embH β) τ := by
  ext a j
  by_cases h : a = j <;>
    simp [h, Matrix.map_apply, Data.Mmat, Data.zmat, Data.embH, Data.emb, map_add, map_mul, map_sum,
      X.tau_kappa0 τ, cc, NumberField.IsCMField.complexEmbedding_complexConj] <;> ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
