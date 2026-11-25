-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isOpen_chart_notB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:23:12.964802+00:00
-- url     : https://prove2.me/submissions/9aec8d30-1560-4b95-9471-cc5d040c7d47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeK
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_lift_mem_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_continuousOn_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J}) := by
  have hS : IsOpen {x : R.X | R.lift x x ∉ mcPts J} := by
    rw [isOpen_iff_forall_mem_open]
    intro x0 hx0
    have hP0 : R.lift x0 x0 ∈ mcPts P := R.mem x0 x0 (R.mem_U x0)

    have hex : ∃ f ∈ J, eval (R.lift x0 x0) (map (Int.castRingHom ℂ) f) ≠ 0 := by
      by_contra hcon
      exact hx0 ⟨hP0.1, fun f hf => not_not.1 fun h => hcon ⟨f, hf, h⟩⟩
    obtain ⟨f, hfJ, hf⟩ := hex
    have hcont : ContinuousOn (fun z => eval (R.lift x0 z) (map (Int.castRingHom ℂ) f)) (R.U x0) := by
      have hl : ContinuousOn (fun z => R.lift x0 z) (R.U x0) :=
        continuousOn_pi.2 fun p => continuousOn_lift R x0 p
      exact (MvPolynomial.continuous_eval _).comp_continuousOn hl
    refine ⟨R.U x0 ∩ (fun z => eval (R.lift x0 z) (map (Int.castRingHom ℂ) f)) ⁻¹' {w | w ≠ 0},
      ?_, hcont.isOpen_inter_preimage (R.isOpen_U x0) isOpen_ne, ⟨R.mem_U x0, hf⟩⟩
    rintro z ⟨hz, hzf⟩
    show R.lift z z ∉ mcPts J
    rw [lift_mem_iff R hz]
    exact fun h => hzf (h.2 f hfJ)
  exact (R.A.chart j).isOpen_inter_preimage_symm hS
end ReciprocityTheory.ChartRestriction.G.Geo
