-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.gradDensCauchySchwarz_thm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:27:16.106028+00:00
-- url     : https://prove2.me/submissions/33317814-1493-4a3f-9898-812cfeb6bcdb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Theorems.Thm_ReciprocityTheory_AnForm_A_gradMat_eq_vecMulVec
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_posSemidef_of_levi
import Theorems.Thm_ReciprocityTheory_AnForm_A_re_mdisc_cons_cs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open Matrix Filter Topology
open scoped ComplexOrder
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GradDensCauchySchwarzStatement := by
  intro n φ v w U hU hφ hl z hz
  have hB : ∀ i, (hessC (φ i) z).PosSemidef := fun i =>
    hessC_posSemidef_of_levi _ _ ((hφ i).contDiffAt (hU.mem_nhds hz)) (hl i z hz)
  unfold gradDens
  simp only [gradMat_eq_vecMulVec]
  have key : ∀ c X P Q : ℝ, X ^ 2 ≤ P * Q → (c * X) ^ 2 ≤ (c * P) * (c * Q) := by
    intro c X P Q h
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg c)]
  exact key _ _ _ _ (re_mdisc_cons_cs _ _ _ hB)
end ReciprocityTheory.AnForm.A
