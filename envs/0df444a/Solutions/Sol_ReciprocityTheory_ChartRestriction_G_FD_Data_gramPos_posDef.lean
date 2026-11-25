-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:17.591879+00:00
-- url     : https://prove2.me/submissions/3aacd4da-f29d-45af-888e-98717c22bcd1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_posDef_of_lminor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_psgn_eq_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_isHermitian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mem_dom_iff

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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : (X.gramPos x τ).PosDef := by
  have hx' := ((X.mem_dom_iff x).1 hx τ).2
  refine posDef_of_lminor X.p0 _ (X.gramPos_isHermitian x τ) fun i => ?_
  have h1 := hx' (Fin.castLE (Nat.succ_le_succ X.p0_le) i)
  have h2 : psgn X.p0 ((Fin.castLE (Nat.succ_le_succ X.p0_le) i : Fin (r + 1)) : ℕ) = 1 :=
    psgn_eq_one (Nat.le_of_lt_succ i.isLt)
  rw [h2, one_mul] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.FD.Data
