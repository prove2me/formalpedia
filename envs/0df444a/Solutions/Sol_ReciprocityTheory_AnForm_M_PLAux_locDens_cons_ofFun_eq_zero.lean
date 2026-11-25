-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.locDens_cons_ofFun_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:44.16869+00:00
-- url     : https://prove2.me/submissions/81c86709-99aa-445e-be80-8bf2aed1eb48

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_maDens_cons_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution {A : FinHolAtlas (e + 1) X} (v : X → ℝ)
    (Φ : Fin e → LocPot X) (j : Fin A.n) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart j).target)
    (hv : (A.chart j).symm y ∉ tsupport v) :
    locDens A (Fin.cons (LocPot.ofFun v) Φ) j y = 0 := by
  unfold locDens
  have hfam : (fun i y' => ((Fin.cons (LocPot.ofFun v) Φ : Fin (e + 1) → LocPot X) i).φ
      ((A.chart j).symm y) ((A.chart j).symm y')) =
      Fin.cons (fun y' => v ((A.chart j).symm y'))
        (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  rw [hfam]
  apply maDens_cons_eq_zero
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport v)ᶜ) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
      (isClosed_tsupport v).isOpen_compl
  filter_upwards [hO.mem_nhds ⟨hy, hv⟩] with y' hy'
  exact image_eq_zero_of_notMem_tsupport hy'.2
end ReciprocityTheory.AnForm.M.PLAux
