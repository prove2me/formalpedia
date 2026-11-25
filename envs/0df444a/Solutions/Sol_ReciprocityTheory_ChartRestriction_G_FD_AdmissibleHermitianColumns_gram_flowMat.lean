-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.gram_flowMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:27.4378+00:00
-- url     : https://prove2.me/submissions/fa6db4cc-6886-42b1-9882-83dfb28437aa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_AdmissibleHermitianColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_col_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_hermC_pair
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_AdmissibleHermitianColumns_alpha_conj
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_emb_cc__bf4bf8966b2b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_flowMat_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section gram
variable (X : Data E r)
private lemma hermC_emb_emb_eq_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc']
end gram
section affine
end affine
section adm
variable (X : Data E r)
end adm
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
theorem _root_.solution {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm (X.flowMat ξ τ s * M) =
      gram τ.1 X.Gm M + ((2 * X.c τ * s.im : ℝ) : ℂ) • rk1 X ξ τ M := by
  have he : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [hermC_emb_emb_eq_herm, hξ, map_zero]
  ext a b
  simp only [gram, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, rk1, hv,
    vecMulVec_apply]
  rw [col_mul, col_mul, flowMat_mulVec (X := X), flowMat_mulVec (X := X),
    hermC_pair τ.1 X.Gm X.Gm_herm _ _ _ he, alpha_conj]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns
