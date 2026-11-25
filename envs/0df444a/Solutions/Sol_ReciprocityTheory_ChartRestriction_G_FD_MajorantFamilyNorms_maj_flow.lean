-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:17:55.877251+00:00
-- url     : https://prove2.me/submissions/8a8fccda-8394-41e8-b92a-0d2a739c816a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantFamilyNorms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hG_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_hsg_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_famN_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_alpha_re
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantFamilyNorms_mt_famN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramFlowTransform_mt_flw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_PositiveMinorUnits_unit_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} (X : Data E r)
variable {x : Frame X.Ψ r} (hx : x ∈ X.dom) (e : X.Ψ → Fin r → ℂ) (τ : X.Ψ)
include hx
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
theorem _root_.solution (he : hermC τ.1 X.Gm (e τ) (e τ) = 0) (s : X.Ψ → ℂ)
    (h1 : 1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0 ≠ 0) :
    X.maj (X.flowV e s x) τ (e τ) = 2 * (mN τ.1 X.Gm (mat x τ) (e τ) X.p0 /
      (1 + 2 * X.c τ * (s τ).im * mN τ.1 X.Gm (mat x τ) (e τ) X.p0)) := by
  have hα := alpha_re (X.c τ) (s τ)
  have hp : X.posPart (X.flowV e s x) τ (e τ) =
      (GramDeterminantReal.mt τ.1 X.Gm (famN (mat (X.flowV e s x) τ) X.p0 X.p0_le) (e τ)).re := rfl
  rw [Data.maj, hp, famN_flow, mt_flw (hG_of X τ) (e τ) he _ _
    (unit_of X.p0 (mat x τ) (hsg_of X hx τ) X.p0 X.p0_le), hα, mt_famN X hx e τ X.p0 X.p0_le, he,
    Complex.zero_re, sub_zero]
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div,
      Complex.ofReal_re]
  · rw [hα, mt_famN X hx e τ X.p0 X.p0_le, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_add]
    exact_mod_cast h1
end ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms
