-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_real_part_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T18:48:35.77384+00:00
-- url     : https://prove2.me/submissions/15763e14-0352-4e70-b848-4e26a5a6dba3

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_log_rounded_upper
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelUniformBounds
open RHFastKernelGammaArithmetic RHFastKernelLogData
def Bounds (v : Frac) (lo hi : Int) : Prop :=
  0<v.2 ∧ lo*(v.2:Int)≤v.1 ∧ v.1≤hi*(v.2:Int)
lemma add_bounds (a b : Frac) (l1 u1 l2 u2 : Int)
    (ha : Bounds a l1 u1) (hb : Bounds b l2 u2) :
    Bounds (add a b) (l1+l2) (u1+u2) := by
  rcases ha with ⟨ha0,hal,hau⟩
  rcases hb with ⟨hb0,hbl,hbu⟩
  refine ⟨Nat.mul_pos ha0 hb0,?_,?_⟩
  · dsimp [add]
    push_cast
    calc
      (l1+l2)*((a.2:Int)*(b.2:Int))=(l1*(a.2:Int))*(b.2:Int)+(l2*(b.2:Int))*(a.2:Int) := by ring
      _ ≤ a.1*(b.2:Int)+b.1*(a.2:Int) :=
        add_le_add (mul_le_mul_of_nonneg_right hal (Int.natCast_nonneg _))
          (mul_le_mul_of_nonneg_right hbl (Int.natCast_nonneg _))
  · dsimp [add]
    push_cast
    calc
      a.1*(b.2:Int)+b.1*(a.2:Int)≤(u1*(a.2:Int))*(b.2:Int)+(u2*(b.2:Int))*(a.2:Int) :=
        add_le_add (mul_le_mul_of_nonneg_right hau (Int.natCast_nonneg _))
          (mul_le_mul_of_nonneg_right hbu (Int.natCast_nonneg _))
      _ = (u1+u2)*((a.2:Int)*(b.2:Int)) := by ring
lemma round_bounds (v : Frac) (lo hi : Int) (h : Bounds v lo hi) :
    lo*(D:Int)≤round v ∧ round v≤hi*(D:Int) := by
  rcases h with ⟨h0,hl,hu⟩
  have hd : (0:Int)<(v.2:Int) := by exact_mod_cast h0
  constructor
  · change lo*(D:Int)≤v.1*(D:Int)/(v.2:Int)
    apply (Int.le_ediv_iff_mul_le hd).mpr
    calc
      lo*(D:Int)*(v.2:Int)=(lo*(v.2:Int))*(D:Int) := by ring
      _ ≤ v.1*(D:Int) := mul_le_mul_of_nonneg_right hl (Int.natCast_nonneg _)
  · change v.1*(D:Int)/(v.2:Int)≤hi*(D:Int)
    apply Int.ediv_le_of_le_mul hd
    calc
      v.1*(D:Int)≤(hi*(v.2:Int))*(D:Int) := mul_le_mul_of_nonneg_right hu (Int.natCast_nonneg _)
      _ = hi*(D:Int)*(v.2:Int) := by ring
end RHFastKernelUniformBounds

open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelUniformBounds

theorem solution (T i : Nat) (hT : 257≤T) (hT' : T≤4294967040) (hi : i<16384) :
    -100*(D:Int)≤(compute T i).realPart ∧ (compute T i).realPart≤0 := by
  let n : Int := (i:Int)-8192
  let bn : Nat := ((T:Int)*32+n).toNat
  let lu : Nat := rounded (bn-2^36) (bn+2^36) D
  let lb : Int := 30*(log2:Int)+(lu:Int)
  have hn : -8192≤n ∧ n≤8192 := by dsimp [n];omega
  have hbn : 32≤bn ∧ bn≤2^37 := by dsimp [bn,n];omega
  have hbni : (32:Int)≤(bn:Int) := by exact_mod_cast hbn.1
  have hbn0 : 0<bn := by omega
  have hlu : lu≤D := TaoFivePrimes.rh_fast_kernel_log_rounded_upper (bn-2^36) (bn+2^36) D (by omega)
  have hluI : (lu:Int)≤(D:Int) := by exact_mod_cast hlu
  have hlb : 20*(D:Int)≤lb ∧ lb≤22*(D:Int) := by
    dsimp [lb]
    norm_num [RHFastKernelLogData.log2,D] at hluI ⊢
    omega
  have hn2 : n^2≤8192^2 := by
    nlinarith [mul_nonneg (show 0≤n+8192 by omega) (show 0≤8192-n by omega)]
  have ha1 : Bounds (-lb+2*(RHFastKernelGammaArithmetic.log2pi:Int),4*D) (-6) (-4) := by
    norm_num [Bounds,RHFastKernelGammaArithmetic.log2pi,D] at hlb ⊢
    omega
  have ha2 : Bounds (-160,3*bn^2) (-1) 0 := by
    refine ⟨by positivity,?_,?_⟩
    · push_cast
      nlinarith [sq_nonneg ((bn:Int)-32)]
    · norm_num
  have ha3 : Bounds (256,3*(bn^2+256)) 0 1 := by
    refine ⟨by positivity,?_,?_⟩
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (bn:Int)]
  have ha4 : Bounds (-n*n,819200) (-82) 0 := by
    norm_num [Bounds]
    constructor <;> nlinarith [sq_nonneg n]
  have hz : Bounds (0,1) 0 0 := by norm_num [Bounds]
  have hs := add_bounds _ _ _ _ _ _ ha1
    (add_bounds _ _ _ _ _ _ ha2 (add_bounds _ _ _ _ _ _ ha3 (add_bounds _ _ _ _ _ _ ha4 hz)))
  have hs' : Bounds (sum [(-lb+2*(RHFastKernelGammaArithmetic.log2pi:Int),4*D),
      (-160,3*bn^2),(256,3*(bn^2+256)),(-n*n,819200)]) (-89) (-3) := hs
  have hr := round_bounds _ _ _ hs'
  change -100*(D:Int)≤round (sum [(-lb+2*(RHFastKernelGammaArithmetic.log2pi:Int),4*D),
      (-160,3*bn^2),(256,3*(bn^2+256)),(-n*n,819200)]) ∧
    round (sum [(-lb+2*(RHFastKernelGammaArithmetic.log2pi:Int),4*D),
      (-160,3*bn^2),(256,3*(bn^2+256)),(-n*n,819200)])≤0
  constructor <;> omega
#print axioms solution
