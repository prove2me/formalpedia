-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:52.170118+00:00
-- url     : https://prove2.me/submissions/b9a30496-f7f9-471b-890e-070a053b74f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sgn_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_pair_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_e_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (τ : X.Ψ) (e : Fin r → Fin r → ℂ)
  (he : ∀ a b, hermC τ.1 X.Gm (e a) (e b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0)
include he
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
theorem _root_.solution (u : Fin r → ℂ) :
    u = ∑ a : Fin r, (((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a)) • e a := by
  have hu : u ∈ Submodule.span ℂ (Set.range e) := by rw [e_span X τ e he]; trivial
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  have hc : ∀ a : Fin r, ((sgn X.p0 a : ℝ) : ℂ) * hermC τ.1 X.Gm u (e a) = β a := by
    intro a
    rw [← hβ, pair_sum X τ e he β Finset.univ a, if_pos (Finset.mem_univ a)]
    calc ((sgn X.p0 a : ℝ) : ℂ) * (β a * ((sgn X.p0 a : ℝ) : ℂ))
        = β a * (((sgn X.p0 a : ℝ) : ℂ) * ((sgn X.p0 a : ℝ) : ℂ)) := by ring
      _ = β a := by rw [sgn_sq, mul_one]
  simp_rw [hc]
  exact hβ.symm
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
