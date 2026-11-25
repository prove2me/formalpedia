-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_locDens_cons_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:11.311642+00:00
-- url     : https://prove2.me/submissions/345dd8ee-3506-431f-9d85-28f6736ce9e6

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesA
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_hessC_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_maDens_cons_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas (e + 1) X) (k : Fin A.n) (ψ : X → ℝ)
    (Φ : Fin e → LocPot X) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart k).target)
    (hψ : (A.chart k).symm y ∉ tsupport ψ) :
    locDens A (Fin.cons (LocPot.ofFun ψ) Φ) k y = 0 := by
  unfold locDens
  apply st_maDens_cons_eq_zero
  apply st_hessC_eq_zero 0
  have h1 : (tsupport ψ)ᶜ ∈ 𝓝 ((A.chart k).symm y) := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hψ
  have h2 := ((A.chart k).continuousAt_symm hy).preimage_mem_nhds h1
  filter_upwards [h2] with y' hy'
  first
  | exact image_eq_zero_of_notMem_tsupport hy'
  | exact image_eq_zero_of_nmem_tsupport hy'
end ReciprocityTheory.AnForm.M
