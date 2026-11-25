-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_continuousOn_maDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:35.30767+00:00
-- url     : https://prove2.me/submissions/39926b77-08ab-486c-abfe-ede103c022f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (φ : Fin D → (Fin D → ℂ) → ℝ) {V : Set (Fin D → ℂ)}
    (hV : IsOpen V) (h : ∀ k, ContDiffOn ℝ 2 (φ k) V) :
    ContinuousOn (ReciprocityTheory.AnForm.maDens φ) V := by
  have hH : ∀ k, ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z) V := fun k =>
    ((h k).fderiv_of_isOpen hV (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  have hap : ∀ k (v w : Fin D → ℂ), ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z v w) V :=
    fun k v w => ((hH k).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hE : ∀ k i j, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z i j) V := by
    intro k i j
    unfold ReciprocityTheory.AnForm.hessC
    simp only []
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn ((hap _ _ _).add (hap _ _ _)))
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        ((hap _ _ _).sub (hap _ _ _))))
  have hM : ∀ k, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z) V := fun k =>
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hE k i j
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc
  refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
    (continuousOn_const.mul (continuousOn_finsetSum _ fun S _ => continuousOn_const.mul ?_)))
  exact (continuous_id.matrix_det).comp_continuousOn
    (continuousOn_finsetSum _ fun k _ => hM k)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
