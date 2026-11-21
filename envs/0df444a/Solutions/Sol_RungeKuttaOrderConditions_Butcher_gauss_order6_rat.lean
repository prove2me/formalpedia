-- Prove2me | solution 1 for RungeKuttaOrderConditions.Butcher.gauss_order6_rat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:59:33.379147+00:00
-- url     : https://prove2.me/submissions/cbc4729f-d8ad-4df2-a5ae-e1794d1235ae

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
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_gauss_order6
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_Phi_toQ15
public import Theorems.Thm_RungeKuttaOrderConditions_Butcher_Phi_smulVec
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
private theorem toQ15_mul (x y : Z15) : toQ15 (x * y) = toQ15 x * toQ15 y := by
  ext <;> simp [toQ15_re, toQ15_im]
private theorem q15_real_mul (a b : ℚ) : (⟨a, 0⟩ : Q15) * ⟨b, 0⟩ = ⟨a * b, 0⟩ := by
  ext <;> simp
private theorem q15_real_pow (a : ℚ) : ∀ n : ℕ, (⟨a, 0⟩ : Q15) ^ n = ⟨a ^ n, 0⟩
  | 0 => by ext <;> simp
  | n + 1 => by rw [pow_succ, q15_real_pow a n, q15_real_mul, ← pow_succ]
private theorem gaussIA_toQ15 :
    gaussIA.map (fun row => row.map toQ15) = smulMat ⟨360, 0⟩ gaussA := by
  simp only [gaussIA, gaussA, smulMat, smulVec, toQ15, List.map_cons, List.map_nil,
    List.cons.injEq, and_true]
  and_intros <;> (ext <;> norm_num)
private theorem gaussIB_toQ15 : gaussIB.map toQ15 = smulVec ⟨360, 0⟩ gaussB := by
  simp only [gaussIB, gaussB, smulVec, toQ15, List.map_cons, List.map_nil,
    List.cons.injEq, and_true]
  and_intros <;> (ext <;> norm_num)
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
theorem _root_.solution : satisfiesOrderConditions gaussA gaussB 6 := by
  intro t ht
  have h := congrArg toQ15 (gauss_order6 t ht)
  rw [toQ15_mul, Phi_toQ15, gaussIA_toQ15, gaussIB_toQ15, Phi_smulVec] at h
  have hgamma : toQ15 ⟨(gamma t : Int), 0⟩ = ((gamma t : ℕ) : Q15) := by
    rw [Q15.natCast_eq]
    ext <;> simp [toQ15_re, toQ15_im]
  have hDpow : toQ15 ⟨Dscale ^ order t, 0⟩ = (⟨360, 0⟩ : Q15) ^ order t := by
    rw [q15_real_pow]
    ext <;> simp [toQ15_re, toQ15_im, Dscale]
  rw [hgamma, hDpow] at h
  have key : (⟨1 / 360, 0⟩ : Q15) ^ order t * (⟨360, 0⟩ : Q15) ^ order t = 1 := by
    rw [← mul_pow, q15_real_mul]
    have h360 : (1 / 360 : ℚ) * 360 = 1 := by norm_num
    rw [h360, q15_real_pow, one_pow]
    ext <;> simp
  calc ((gamma t : ℕ) : Q15) * Phi gaussA gaussB t
      = ((⟨1 / 360, 0⟩ : Q15) ^ order t * (⟨360, 0⟩ : Q15) ^ order t)
          * (((gamma t : ℕ) : Q15) * Phi gaussA gaussB t) := by rw [key, one_mul]
    _ = (⟨1 / 360, 0⟩ : Q15) ^ order t
          * (((gamma t : ℕ) : Q15) * ((⟨360, 0⟩ : Q15) ^ order t * Phi gaussA gaussB t)) := by
        ring
    _ = (⟨1 / 360, 0⟩ : Q15) ^ order t * (⟨360, 0⟩ : Q15) ^ order t := by rw [h]
    _ = 1 := key
end RungeKuttaOrderConditions.Butcher
