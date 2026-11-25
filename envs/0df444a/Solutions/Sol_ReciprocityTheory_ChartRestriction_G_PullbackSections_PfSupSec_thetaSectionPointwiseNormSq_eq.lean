-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec.thetaSectionPointwiseNormSq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:31.654423+00:00
-- url     : https://prove2.me/submissions/c94d0f38-9a25-4231-8ff2-9dc0d3b649d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_SupGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExtProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SupSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_PfSupSec_one_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
open NumberField ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
theorem _root_.solution (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (w : Fin 1 → Vsp X.dim) :
    X.ptN2 1 s w = (toGT X).ptN2 1 (fun v => s (fun _ => v)) (w 0) := by
  have hw := one_col w
  have hre : (HC w w).re = ‖w 0‖ ^ 2 := by
    simp only [HC, Fin.sum_univ_one, Hf]
    rw [EuclideanSpace.norm_sq_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  show ‖s w‖ ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * (HC w w).re) =
    ‖s (fun _ => w 0)‖ ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * ‖w 0‖ ^ 2)
  rw [hw, hre]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
