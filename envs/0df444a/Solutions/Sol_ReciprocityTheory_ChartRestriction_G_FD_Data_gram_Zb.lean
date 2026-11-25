-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.gram_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:37.400824+00:00
-- url     : https://prove2.me/submissions/146a4069-a2f6-437b-b653-6ac2ac971b73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mat_Zb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
private lemma col_mul_eq_mulVec_col (M N : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (M * N) a = M *ᵥ col N a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
end Data
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.Zb u b x) τ) = gram τ.1 X.Gm (mat x τ) := by
  rw [X.mat_Zb]
  ext a a'
  simp only [gram, Matrix.of_apply, col_mul_eq_mulVec_col]
  exact X.zmat_unitary u hu b hb τ _ _
end ReciprocityTheory.ChartRestriction.G.FD.Data
