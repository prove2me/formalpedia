-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.zmat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:35:43.415188+00:00
-- url     : https://prove2.me/submissions/3c4447a0-c391-4980-9f36-26f40e2041b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_zmat_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Am_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Cm_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right


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
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : IsHermFam b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.zmat u b τ *ᵥ v) (X.zmat u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hee : ∀ i k, hermC τ.1 X.Gm (emb τ.1 (u i)) (emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hb' : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcw : ∀ k, conj (hermC τ.1 X.Gm w (emb τ.1 (u k))) = hermC τ.1 X.Gm (emb τ.1 (u k)) w :=
    fun k => hermC_conj τ.1 X.Gm_herm _ _
  rw [X.zmat_eq, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, X.Am_mulVec, X.Am_mulVec]
  simp only [Fin.sum_univ_two, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, hee,
    X.Cm_mulVec, map_mul, map_add, map_neg, hb', hcw, Complex.conj_I, Complex.conj_ofReal, mul_zero, add_zero]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.Data
