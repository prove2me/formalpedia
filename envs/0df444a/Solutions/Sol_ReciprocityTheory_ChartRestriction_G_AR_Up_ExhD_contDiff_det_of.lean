-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD.contDiff_det_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:30:40.73245+00:00
-- url     : https://prove2.me/submissions/0227f896-b1ce-47c3-966b-a5b5138b1d6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
variable {f p q N' : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
theorem _root_.solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun x => M x i j) : ContDiff 𝕜 ∞ fun x => (M x).det := by
  have e : (fun x => (M x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M x (σ j) j := by
    funext x; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => h _ _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
