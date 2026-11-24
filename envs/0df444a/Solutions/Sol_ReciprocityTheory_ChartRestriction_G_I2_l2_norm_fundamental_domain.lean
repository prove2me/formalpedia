-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.l2_norm_fundamental_domain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:31.613461+00:00
-- url     : https://prove2.me/submissions/1a53e51d-2b29-4ceb-a9af-d61b7d552ca1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_avg_fd_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E] (X : PT E)
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 q s = ⨍ x in ZSpan.fundamentalDomain X.b, X.ptN2 q s (fun _ => x) := by
  have hv : ∀ v : Fin 1 → Vsp X.dim, (fun _ : Fin 1 => v 0) = v :=
    fun v => funext fun k => by rw [Subsingleton.elim k 0]
  have h := avg_fd_prod X (n := 1) (fun _ x => X.ptN2 q s (fun _ => x))
  simp only [Fin.prod_univ_one, hv] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.I2
