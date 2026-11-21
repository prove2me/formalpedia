-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.Phi_toQ15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:58:24.994212+00:00
-- url     : https://prove2.me/submissions/0703a432-1a5e-41ad-85f3-0602a550a08b

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
private theorem toQ15_re (x : Z15) : (toQ15 x).re = (x.re : ℚ) := rfl
private theorem toQ15_im (x : Z15) : (toQ15 x).im = (x.im : ℚ) := rfl
private theorem toQ15_zero : toQ15 0 = 0 := by
  ext <;> simp [toQ15_re, toQ15_im]
private theorem toQ15_one : toQ15 1 = 1 := by
  ext <;> simp [toQ15_re, toQ15_im]
private theorem toQ15_add (x y : Z15) : toQ15 (x + y) = toQ15 x + toQ15 y := by
  ext <;> simp [toQ15_re, toQ15_im]
private theorem toQ15_mul (x y : Z15) : toQ15 (x * y) = toQ15 x * toQ15 y := by
  ext <;> simp [toQ15_re, toQ15_im]
private theorem dot_toQ15 : ∀ u v : List Z15,
    toQ15 (dot u v) = dot (u.map toQ15) (v.map toQ15)
  | [], _ => by simp [dot, toQ15_zero]
  | _ :: _, [] => by simp [dot, toQ15_zero]
  | a :: u, b :: v => by
      have ih := dot_toQ15 u v
      simp only [dot, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      rw [toQ15_add, toQ15_mul, ih]
private theorem pmul_toQ15 : ∀ u v : List Z15,
    (pmul u v).map toQ15 = pmul (u.map toQ15) (v.map toQ15)
  | [], _ => by simp [pmul]
  | _ :: _, [] => by simp [pmul]
  | a :: u, b :: v => by
      have ih := pmul_toQ15 u v
      simp only [pmul, List.map_cons, List.zipWith_cons_cons] at ih ⊢
      rw [toQ15_mul, ih]
private theorem mulMatVec_toQ15 (v : List Z15) : ∀ A : List (List Z15),
    (mulMatVec A v).map toQ15 = mulMatVec (A.map (fun row => row.map toQ15)) (v.map toQ15)
  | [] => rfl
  | row :: A => by
      have ih := mulMatVec_toQ15 v A
      simp only [mulMatVec, List.map_cons] at ih ⊢
      rw [dot_toQ15, ih]
private theorem phiForest_toQ15 (A : List (List Z15)) : ∀ F : Forest,
    (phiForest A F).map toQ15 = phiForest (A.map (fun row => row.map toQ15)) F
  | [] => by simp [phiForest, List.map_map, Function.comp_def, toQ15_one]
  | RTree.node G :: ts => by
      have ihG := phiForest_toQ15 A G
      have ihts := phiForest_toQ15 A ts
      simp only [phiForest, phiVec]
      rw [← ihG, ← ihts, ← mulMatVec_toQ15, ← pmul_toQ15]
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
theorem _root_.solution (A : List (List Z15)) (b : List Z15) (t : RTree) :
    toQ15 (Phi A b t) = Phi (A.map (fun row => row.map toQ15)) (b.map toQ15) t := by
  cases t with
  | node F =>
      simp only [Phi, phiVec]
      rw [dot_toQ15, phiForest_toQ15]
end RungeKuttaOrderConditions.Butcher
