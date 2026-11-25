-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.zmat_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:23.544327+00:00
-- url     : https://prove2.me/submissions/f7a72d99-88b2-4928-bab9-efc940a1f42f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_mul_Am

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    X.zmat u b τ * X.zmat u b' τ = X.zmat u (b + b') τ := by
  have h := X.Cm_mul_Am u hu b τ
  rw [X.zmat_eq u b τ, X.zmat_eq u b' τ, X.zmat_eq u (b + b') τ, X.Cm_add]
  calc (1 + X.Am u τ * X.Cm u b τ) * (1 + X.Am u τ * X.Cm u b' τ)
      = 1 + X.Am u τ * X.Cm u b τ + X.Am u τ * X.Cm u b' τ +
          X.Am u τ * (X.Cm u b τ * X.Am u τ) * X.Cm u b' τ := by
        simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_assoc]
        abel
    _ = 1 + X.Am u τ * (X.Cm u b τ + X.Cm u b' τ) := by
        rw [h, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_add, add_assoc]
end ReciprocityTheory.ChartRestriction.G.FD.Data
