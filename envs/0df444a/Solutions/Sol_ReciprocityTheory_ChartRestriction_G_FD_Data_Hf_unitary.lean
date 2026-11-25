-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:58.50196+00:00
-- url     : https://prove2.me/submissions/c0ef9048-f260-4d5c-bdd2-61ace75b19ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantBoundOrthogonalPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
    (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)
    (hx : x ∈ X.dom) (y w : Fin r → ℂ) :
    X.Hf (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g y) (Matrix.mulVec g w) = X.Hf x τ y w := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = g.mulVec (col (mat x τ) a) := by
    intro a
    funext k
    simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    ext a b
    simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hcol, hg]
  have hppos : X.ppos (X.lmulC (fun _ => g) x) τ (g.mulVec y) = g.mulVec (X.ppos x τ y) := by
    simp only [Data.ppos, hcol, hgram, hg, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hlin : (2 : ℂ) • g.mulVec (X.ppos x τ y) - g.mulVec y =
      g.mulVec ((2 : ℂ) • X.ppos x τ y - y) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [Data.Hf]
  rw [hppos, hlin, hg]
end ReciprocityTheory.ChartRestriction.G.FD.Data
