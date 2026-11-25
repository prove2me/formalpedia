-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Jp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:38.771034+00:00
-- url     : https://prove2.me/submissions/04359a7d-a59e-40f0-a060-b14942aa707a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_positive_part_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.Jp x τ (u + v) = X.Jp x τ u + X.Jp x τ v := by
  funext i
  simp only [Jp, positive_part_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
