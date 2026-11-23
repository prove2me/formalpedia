-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.Canon.canonGen_isGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:03.617831+00:00
-- url     : https://prove2.me/submissions/8b9174a2-ab03-4923-9b31-68fe71b84106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out.Canon
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}
variable {K K' : Type} [Fintype K] [Fintype K']
variable (L)
variable {L}
namespace ReciprocityTheory.ChartRestriction.G.Out.Canon
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (hs : LB.SameSum φ ε φ' ε') (hsub : ∀ k, ∃ k', φ' k' = φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : (canonGen L φ ε φ' ε' hsub t).IsGen := by
  intro j1 j2
  have hW : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
      (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j1) ⊓ (LB.LinComb L φ ε).U (jhat φ ε φ' hsub j2) :=
    inf_le_inf (wchart_le_jhat φ ε φ' ε' hsub j1) (wchart_le_jhat φ ε φ' ε' hsub j2)
  have ht' : res (hW.trans inf_le_left) (t.s (jhat φ ε φ' hsub j1)) =
      res hW ((LB.LinComb L φ ε).g (jhat φ ε φ' hsub j1) (jhat φ ε φ' hsub j2)) *
      res (hW.trans inf_le_right) (t.s (jhat φ ε φ' hsub j2)) := by
    have e := congrArg (res hW) (ht (jhat φ ε φ' hsub j1) (jhat φ ε φ' hsub j2))
    exact (res_res' _ _ _).symm.trans (e.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl (res_res' _ _ _))))
  have e1 : res (inf_le_left : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
        (LB.LinComb L φ' ε').U j1) ((canonGen L φ ε φ' ε' hsub t).s j1) =
      res (hW.trans inf_le_left) (t.s (jhat φ ε φ' hsub j1)) *
        res inf_le_left (corrU φ' ε' j1) :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (res_res' _ _ _) rfl)
  have e2 : res (inf_le_right : (LB.LinComb L φ' ε').U j1 ⊓ (LB.LinComb L φ' ε').U j2 ≤
        (LB.LinComb L φ' ε').U j2) ((canonGen L φ ε φ' ε' hsub t).s j2) =
      res (hW.trans inf_le_right) (t.s (jhat φ ε φ' hsub j2)) *
        res inf_le_right (corrU φ' ε' j2) :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (res_res' _ _ _) rfl)
  rw [e1, e2, ht', mul_right_comm, canon_key hL φ ε φ' ε' hs hsub j1 j2 hW, mul_right_comm,
    mul_assoc]
end ReciprocityTheory.ChartRestriction.G.Out.Canon
