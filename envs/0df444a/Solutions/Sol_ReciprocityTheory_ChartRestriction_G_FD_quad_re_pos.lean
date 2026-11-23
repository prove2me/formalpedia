-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:38.135969+00:00
-- url     : https://prove2.me/submissions/80eccb89-28ef-4a6f-9439-2cc57743213e

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
theorem _root_.solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {c : Fin n → ℂ}
    (hc : c ≠ 0) : 0 < (∑ a, ∑ b, c a * M a b * conj (c b)).re := by
  have hc' : star c ≠ 0 := fun h0 => hc (by simpa using congrArg star h0)
  have h := hM.dotProduct_mulVec_pos hc'
  have e : star (star c) ⬝ᵥ (M *ᵥ star c) = ∑ a, ∑ b, c a * M a b * conj (c b) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [e] at h
  have h' := (Complex.lt_def.1 h).1
  rwa [Complex.zero_re] at h'
end ReciprocityTheory.ChartRestriction.G.FD
