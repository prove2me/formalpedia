-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hermitian_pairing_Je_Je_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:34:35.534482+00:00
-- url     : https://prove2.me/submissions/e546306e-cb18-421a-be34-9596e6c549cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_Jp__4f74ff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Jp_adj

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
variable (x : Frame X.Ψ r) (τ : X.Ψ) (e : Fin r → ℂ) (δ : (Fin r → ℂ) →ₗ[ℂ] ℂ)
variable {x τ e}
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (hx : x ∈ X.dom) (he : hermC τ.1 X.Gm e e = 0) :
    hermC τ.1 X.Gm (X.Jp x τ e) (X.Jp x τ e) = 0 := by
  rw [X.Jp_adj hx τ e (X.Jp x τ e), X.Jp_Jp hx τ e, he]
end ReciprocityTheory.ChartRestriction.G.FD.Data
