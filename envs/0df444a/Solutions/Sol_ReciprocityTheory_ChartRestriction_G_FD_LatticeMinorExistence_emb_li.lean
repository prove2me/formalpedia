-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence.emb_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:04:09.198172+00:00
-- url     : https://prove2.me/submissions/53554069-d04a-4409-bd47-870671aa5495

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeMinorExistence
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_LatticeMinorExistence_exists_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
theorem _root_.solution {u : Fin 2 → Fin r → E} (hu : LinearIndependent E u) (τ : E →+* ℂ) (c : Fin 2 → ℂ)
    (hc : ∑ i, c i • Data.emb τ (u i) = 0) : c = 0 := by
  obtain ⟨a, b, hab⟩ := exists_minor hu
  have hd : τ (u 0 a * u 1 b - u 0 b * u 1 a) ≠ 0 := by
    rw [map_ne_zero_iff _ τ.injective]
    exact hab
  simp only [map_sub, map_mul] at hd
  have ea := congrFun hc a
  have eb := congrFun hc b
  simp only [Finset.sum_apply, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Data.emb,
    Pi.zero_apply] at ea eb
  have h0 : c 0 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 1 b) * ea - τ (u 1 a) * eb
  have h1 : c 1 * (τ (u 0 a) * τ (u 1 b) - τ (u 0 b) * τ (u 1 a)) = 0 := by
    linear_combination τ (u 0 a) * eb - τ (u 0 b) * ea
  have h0' := (mul_eq_zero.1 h0).resolve_right hd
  have h1' := (mul_eq_zero.1 h1).resolve_right hd
  funext i
  fin_cases i
  · simpa using h0'
  · simpa using h1'
end ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
