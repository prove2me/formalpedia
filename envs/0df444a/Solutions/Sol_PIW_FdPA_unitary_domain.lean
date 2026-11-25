-- Prove2me | solution 1 for PIW.FdPA.unitary_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:41:47.414566+00:00
-- url     : https://prove2.me/submissions/83651c67-a56e-4c31-bc64-beea5e45d86e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Theorems.Thm_PIW_FdPA_mem_dom_iff
import Theorems.Thm_PIW_FdPA_det_of_minors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
open scoped ComplexConjugate
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : UnitDom E := by
  intro r X n x hn hx
  rw [mem_dom_iff] at hx ⊢
  intro τ

  have hcol : ∀ a, col (mat (X.lmulC n x) τ) a = Matrix.mulVec (n τ) (col (mat x τ) a) := by
    intro a
    funext k
    simp [col, mat, Data.lmulC, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hg : gram τ.1 X.Gm (mat (X.lmulC n x) τ) = gram τ.1 X.Gm (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, hcol, hn τ]
  have hd : ∀ i, dmin X.Gm (X.lmulC n x) τ i = dmin X.Gm x τ i := by
    intro i
    simp only [dmin, hg]
  have hpos : ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.lmulC n x) τ i).re := by
    intro i
    rw [hd]
    exact (hx τ).2 i
  exact ⟨det_of_minors X (X.lmulC n x) τ hpos, hpos⟩
end PIW.FdPA
