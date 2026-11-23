-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:44.703162+00:00
-- url     : https://prove2.me/submissions/9d83facf-8a83-4dcc-b70b-25f28e6980dc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ) :
    dv τ G f e = ∑ b, (yv τ G f e b -
      Fin.snoc (α := fun _ => ℂ) (yv τ G (fun a : Fin n => f a.castSucc) e) 0 b) • f b := by
  unfold dv pv
  simp only [sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
