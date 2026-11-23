-- Prove2me | solution 1 for UnipMove.GraphH.sum_mul_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:16.133426+00:00
-- url     : https://prove2.me/submissions/ca616cbf-672d-4683-902a-17c40c730801

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.GraphH
theorem _root_.solution (f : Fin r → ℂ) (d : Fin X.p0 → ℂ) :
    ∑ j, f j * ext X d j = ∑ b, f (Fin.castLE X.p0_le b) * d b := by
  have h : X.p0 + (r - X.p0) = r := by have := X.p0_le; omega
  have e : ∑ j, f j * ext X d j =
      ∑ i : Fin (X.p0 + (r - X.p0)), f (Fin.cast h i) * ext X d (Fin.cast h i) :=
    (Fintype.sum_equiv (finCongr h) (fun i => f (Fin.cast h i) * ext X d (Fin.cast h i))
      (fun j => f j * ext X d j) (fun _ => rfl)).symm
  rw [e, Fin.sum_univ_add]
  have h1 : ∀ a : Fin X.p0, ext X d (Fin.cast h (Fin.castAdd (r - X.p0) a)) = d a := by
    intro a
    unfold ext
    split_ifs with ha
    · rfl
    · exact absurd a.isLt ha
  have h2 : ∀ m : Fin (r - X.p0), ext X d (Fin.cast h (Fin.natAdd X.p0 m)) = 0 := by
    intro m
    unfold ext
    split_ifs with hm
    · have e2 : ((Fin.cast h (Fin.natAdd X.p0 m) : Fin r) : ℕ) = X.p0 + (m : ℕ) := rfl
      omega
    · rfl
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  rfl
end UnipMove.GraphH
