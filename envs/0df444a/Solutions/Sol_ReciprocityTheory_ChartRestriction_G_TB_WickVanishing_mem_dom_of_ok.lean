-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.mem_dom_of_ok
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:32:43.777359+00:00
-- url     : https://prove2.me/submissions/bc6c6195-6f75-4da9-9600-1aedd4455cb2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_sgn_cast_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_det_ne_of_ok
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_lead_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {r : ℕ} (X : Data E r) (P : X.Ψ → Matrix (Fin r) (Fin r) ℂ)
    (hP : ∀ τ, (P τ).det ≠ 0 ∧ gram τ.1 X.Gm (P τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hy : ∀ τ, Ok X.p0 (y τ)) :
    (fun τ => (P τ * y τ : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ X.dom := by
  intro τ
  have hg : gram τ.1 X.Gm (P τ * y τ) = Gy X.p0 (y τ) := by
    rw [FrameDegreeData.gram_mul, (hP τ).2, sgn_cast_eq]
    rfl
  refine ⟨?_, fun i => ?_⟩
  · show (P τ * y τ).det ≠ 0
    rw [det_mul]
    exact mul_ne_zero (hP τ).1 (det_ne_of_ok (hy τ))
  · show 0 < psgn X.p0 i * (lminor (gram τ.1 X.Gm (P τ * y τ)) i).re
    rw [hg]
    unfold psgn sgn lminor
    exact lead_pos (hy τ) i (Nat.le_of_lt_succ i.isLt)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
