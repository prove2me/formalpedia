-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.quad_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:49.545173+00:00
-- url     : https://prove2.me/submissions/18ae8dff-883e-4eeb-b692-c02df80b5916

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (c : Fin n → ℂ) :
    0 ≤ (∑ a, ∑ b, c a * M a b * conj (c b)).re := by
  have h : 0 ≤ star (star c) ⬝ᵥ (M *ᵥ star c) := hM.dotProduct_mulVec_nonneg (star c)
  have e : star (star c) ⬝ᵥ (M *ᵥ star c) = ∑ a, ∑ b, c a * M a b * conj (c b) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e] at h
  have h' := (Complex.le_def.1 h).1
  rwa [Complex.zero_re] at h'
end ReciprocityTheory.ChartRestriction.G.FD
