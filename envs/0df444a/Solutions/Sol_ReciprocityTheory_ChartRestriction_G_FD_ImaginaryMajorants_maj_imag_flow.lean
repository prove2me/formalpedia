-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.maj_imag_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:08.573678+00:00
-- url     : https://prove2.me/submissions/fff23717-1285-451f-ba70-098d70924054

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_maj_imag_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_boost_lower


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (ξ : Fin r → E) (b : X.Ψ → ℝ)
    (hy : X.flow ξ (fun τ => I * (b τ : ℂ)) z ∈ X.dom) (τ : X.Ψ)
    (hee : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (he0 : Data.emb τ.1 ξ ≠ 0)
    (hq : 0 < 1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (w : Fin r → ℂ) :
    min (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ))⁻¹ *
      X.maj z τ w ≤ X.maj (X.flow ξ (fun τ => I * (b τ : ℂ)) z) τ w := by
  rw [maj_imag_eq X hz ξ b hy τ hee he0 hq w]
  have hσ : 0 < Real.sqrt (1 + X.c τ * b τ * X.maj z τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq
  have h := boost_lower (X := X) (z := z) (τ := τ) (e := Data.emb τ.1 ξ) hz hee he0 hσ w
  rwa [Real.sq_sqrt hq.le] at h
end ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
