-- Prove2me | solution 1 for PI.WMI.lowerInv_inner_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:10:15.137541+00:00
-- url     : https://prove2.me/submissions/4480cbc8-4976-4df2-9f47-a7d3f74bbda4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
variable {N : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)}
namespace PI.WMI
theorem _root_.solution (hU : IsURepOn (Kset (allPos N)) σ) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : g ∈ Kset (allPos N)) (u w : H) : ⟪σ g u, σ g w⟫_ℂ = ⟪u, w⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g).toLinearMap, norm_map' := fun v => hU.2.1 g hg v }
  exact L.inner_map_map u w
end PI.WMI
