-- Prove2me | solution 1 for PIW.FdPA.normFactor_pos_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:21:53.548306+00:00
-- url     : https://prove2.me/submissions/195a8df2-2a0c-4a74-a044-b3b5eac51561

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : NfacPos E := by
  intro r X la x hx
  have hx' : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  unfold Data.nfac
  refine Finset.prod_pos (fun τ _ => Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos ?_ _))
  have hne : ∀ j, dmin X.Gm x τ j ≠ 0 := by
    intro j h0
    have := (hx' τ).2 j
    rw [h0] at this
    simp at this
  exact norm_pos_iff.mpr (div_ne_zero (hne _) (hne _))
end PIW.FdPA
