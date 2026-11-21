-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.Phi_smulVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:25.452774+00:00
-- url     : https://prove2.me/submissions/4f337ecb-0d6f-4bd5-ae3b-501dc76af4a2

module
public import Mathlib.Algebra.Ring.Rat
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_RungeKuttaOrderConditions_ButcherOrder
section
@[expose] public section
namespace RungeKuttaOrderConditions
namespace Q15
end Q15
namespace Z15
end Z15
namespace Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
end Butcher
end RungeKuttaOrderConditions
namespace RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
private theorem smulVec_cons (c a : K) (v : List K) :
    smulVec c (a :: v) = c * a :: smulVec c v := rfl
private theorem smulVec_one (v : List K) : smulVec 1 v = v := by
  simp [smulVec]
private theorem dot_smulVec (c d : K) : ∀ u v : List K,
    dot (smulVec c u) (smulVec d v) = c * d * dot u v
  | [], _ => by simp [dot, smulVec]
  | _ :: _, [] => by simp [dot, smulVec]
  | a :: u, b :: v => by
      have ih := dot_smulVec c d u v
      simp only [dot, smulVec_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      rw [ih]; ring
private theorem pmul_smulVec (c d : K) : ∀ u v : List K,
    pmul (smulVec c u) (smulVec d v) = smulVec (c * d) (pmul u v)
  | [], _ => by simp [pmul, smulVec]
  | _ :: _, [] => by simp [pmul, smulVec]
  | a :: u, b :: v => by
      have ih := pmul_smulVec c d u v
      simp only [pmul, smulVec_cons, List.zipWith_cons_cons, List.cons.injEq] at ih ⊢
      exact ⟨by ring, ih⟩
private theorem mulMatVec_smulVec (c d : K) (v : List K) : ∀ A : List (List K),
    mulMatVec (smulMat c A) (smulVec d v) = smulVec (c * d) (mulMatVec A v)
  | [] => rfl
  | row :: A => by
      have ih := mulMatVec_smulVec c d v A
      simp only [mulMatVec, smulMat, List.map_cons, smulVec_cons, List.cons.injEq] at ih ⊢
      exact ⟨dot_smulVec c d row v, ih⟩
private theorem phiForest_smulVec (c : K) (A : List (List K)) : ∀ F : Forest,
    phiForest (smulMat c A) F = smulVec (c ^ orderF F) (phiForest A F)
  | [] => by simp [phiForest, smulMat, orderF, smulVec_one, List.map_map, Function.comp_def]
  | RTree.node G :: ts => by
      have ihG := phiForest_smulVec c A G
      have ihts := phiForest_smulVec c A ts
      simp only [phiForest, phiVec, orderF, order]
      rw [ihG, ihts, mulMatVec_smulVec, pmul_smulVec]
      have hpow : c * c ^ orderF G * c ^ orderF ts = c ^ (1 + orderF G + orderF ts) := by ring
      rw [hpow]
  termination_by F => sizeOf F
  decreasing_by
    all_goals simp_wf
    omega
end Butcher
end RungeKuttaOrderConditions
end
end

set_option autoImplicit true
@[expose] public section
public section
open RungeKuttaOrderConditions RungeKuttaOrderConditions.Butcher
variable {K : Type*} [CommRing K]
namespace RungeKuttaOrderConditions.Butcher
theorem _root_.solution (c : K) (A : List (List K)) (b : List K) (t : RTree) :
    Phi (smulMat c A) (smulVec c b) t = c ^ order t * Phi A b t := by
  cases t with
  | node F =>
      simp only [Phi, phiVec, order]
      rw [phiForest_smulVec, dot_smulVec]
      ring
end RungeKuttaOrderConditions.Butcher
