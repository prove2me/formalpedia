-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Zb_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:49:08.436913+00:00
-- url     : https://prove2.me/submissions/5e3688bb-2ea1-4ace-9f9d-9956e4c8a2bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mat_Zb

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
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) :
    X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x := by
  funext τ
  show X.zmat u b τ * mat (X.Zb u b' x) τ = X.zmat u (b + b') τ * mat x τ
  rw [X.mat_Zb, ← Matrix.mul_assoc, X.zmat_mul u hu]
end ReciprocityTheory.ChartRestriction.G.FD.Data
