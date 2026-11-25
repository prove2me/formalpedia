-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.poin_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:49.274222+00:00
-- url     : https://prove2.me/submissions/e3e34559-2912-4c62-a91e-e73f80a3de0c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lact_mul__ed60d44db8d0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_chi_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {γ' : GL (Fin r) E}
    (hγ' : γ' ∈ X.Γ) (x : Frame X.Ψ r) :
    poin X la P (lact γ' x) = X.χ la γ' * poin X la P x := by
  unfold poin
  set g : X.Γ := ⟨γ', hγ'⟩
  have key : ∀ γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 (lact γ' x)) =
      X.χ la γ' * ((X.χ la (γ * g).1)⁻¹ * P (lact (γ * g).1 x)) := by
    intro γ
    have hm : ((γ * g : X.Γ) : GL (Fin r) E) = γ.1 * γ' := rfl
    rw [hm, lact_mul', X.χ_mul la γ.1 γ.2 γ' hγ']
    have h1 := chi_ne X la hγ'
    have h2 := chi_ne X la γ.2
    field_simp
  rw [tsum_congr key, tsum_mul_left]
  congr 1
  exact (Equiv.mulRight g).tsum_eq (fun δ : X.Γ => (X.χ la δ.1)⁻¹ * P (lact δ.1 x))
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
