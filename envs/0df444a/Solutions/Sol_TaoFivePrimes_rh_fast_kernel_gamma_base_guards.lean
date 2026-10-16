-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_gamma_base_guards
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T19:20:54.579249+00:00
-- url     : https://prove2.me/submissions/26da4ae6-3b85-40da-9572-eef40c1abd1a

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_TaoFivePrimes_RHFastKernelGammaArithmetic
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_real_part_bounds
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_log_rounded_upper
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_phase_input_bound
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace RHFastKernelPeriodBounds
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
end RHFastKernelPeriodBounds

open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelPeriodBounds

theorem RHFastKernelUniformPeriod.raw_phase_bounds (bn : Nat) (lb : Int) (hbn : 32≤bn ∧ bn≤2^37)
    (hlb : 20*(D:Int)≤lb ∧ lb≤22*(D:Int)) :
    -3*(D:Int)≤round (sum [((bn:Int)*(lb-(D:Int)),64*D),(-(P:Int),8*10^50),
      (6,bn),(-1024,3*bn^3),(-16*(bn:Int),3*(bn^2+256))]) ∧
    round (sum [((bn:Int)*(lb-(D:Int)),64*D),(-(P:Int),8*10^50),
      (6,bn),(-1024,3*bn^3),(-16*(bn:Int),3*(bn^2+256))])≤50000000001*(D:Int) := by
  have hbni : (32:Int)≤(bn:Int) := by exact_mod_cast hbn.1
  have hbn0 : 0<bn := by omega
  have hbnu : (bn:Int)≤137438953472 := by exact_mod_cast hbn.2
  have hcubeNat : 32768≤bn^3 := by
    calc 32768=32^3 := by decide +kernel
         _ ≤ bn^3 := Nat.pow_le_pow_left hbn.1 3
  have hcubeInt : (32768:Int)≤(bn:Int)^3 := by exact_mod_cast hcubeNat
  have hbnI0 : (0:Int)≤(bn:Int) := Int.natCast_nonneg bn
  have hDlb : (D:Int)≤lb := (by decide +kernel : (D:Int)≤20*(D:Int)).trans hlb.1
  have hlbu : lb-(D:Int)≤21*(D:Int) := by linarith only [hlb.2]
  have h21 : (0:Int)≤21*(D:Int) := by decide +kernel
  have hm1 : (bn:Int)*(lb-(D:Int))≤(bn:Int)*(21*(D:Int)) := mul_le_mul_of_nonneg_left hlbu hbnI0
  have hm2 : (bn:Int)*(21*(D:Int))≤137438953472*(21*(D:Int)) := mul_le_mul_of_nonneg_right hbnu h21
  have hm3 : 137438953472*(21*(D:Int))≤50000000000*(64*(D:Int)) := by decide +kernel
  have hden : 0<64*D := by decide +kernel
  have ha1 : Bounds ((bn:Int)*(lb-(D:Int)),64*D) 0 50000000000 := by
    refine ⟨hden,?_,?_⟩
    · simpa only [zero_mul] using mul_nonneg hbnI0 (sub_nonneg.mpr hDlb)
    · simpa only [Nat.cast_mul,Nat.cast_ofNat] using hm1.trans (hm2.trans hm3)
  have ha2 : Bounds (-(P:Int),8*10^50) (-1) 0 := by norm_num [Bounds,P]
  have ha3 : Bounds (6,bn) 0 1 := by
    refine ⟨hbn0,?_,?_⟩
    · norm_num
    · simpa only [one_mul] using (by decide +kernel : (6:Int)≤32).trans hbni
  have ha4 : Bounds (-1024,3*bn^3) (-1) 0 := by
    refine ⟨by positivity,?_,?_⟩
    · push_cast
      nlinarith only [hcubeInt]
    · norm_num
  have ha5 : Bounds (-16*(bn:Int),3*(bn^2+256)) (-1) 0 := by
    refine ⟨by positivity,?_,?_⟩
    · push_cast
      nlinarith only [mul_nonneg (Int.natCast_nonneg bn) (sub_nonneg.mpr hbni)]
    · dsimp
      nlinarith only [Int.natCast_nonneg bn]
  have hz : Bounds (0,1) 0 0 := by norm_num [Bounds]
  have hs := add_bounds _ _ _ _ _ _ ha1 (add_bounds _ _ _ _ _ _ ha2
    (add_bounds _ _ _ _ _ _ ha3 (add_bounds _ _ _ _ _ _ ha4 (add_bounds _ _ _ _ _ _ ha5 hz))))
  have hs' : Bounds (sum [((bn:Int)*(lb-(D:Int)),64*D),(-(P:Int),8*10^50),
      (6,bn),(-1024,3*bn^3),(-16*(bn:Int),3*(bn^2+256))]) (-3) 50000000001 := hs
  exact round_bounds _ _ _ hs'
theorem RHFastKernelUniformPeriod.quotient_bound (ii : Int)
    (hii : -3*(D:Int)≤ii ∧ ii≤50000000001*(D:Int)) :
    ((ii*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))).natAbs≤10000000000 := by
  norm_num [P,D] at hii ⊢
  omega

theorem RHFastKernelUniformPeriod.period_bound (T i : Nat) (hT : 257≤T) (hT' : T≤4294967040) (hi : i<16384) :
    (compute T i).period.natAbs≤10000000000 := by
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
  have hraw := RHFastKernelUniformPeriod.raw_phase_bounds bn lb hbn hlb
  have hphase : -3*(D:Int)≤(compute T i).phase ∧ (compute T i).phase≤50000000001*(D:Int) := hraw
  exact RHFastKernelUniformPeriod.quotient_bound (compute T i).phase hphase

theorem RHFastKernelUniformPeriod.exp_input_bound (rr : Int)
    (hrr : -100*(D:Int)≤rr) : 2*((-rr).toNat/256)≤D := by
  norm_num [D] at hrr ⊢
  omega

theorem solution (T i : Nat) (hT : 257≤T) (hT' : T≤4294967040) (hi : i<16384) :
    (compute T i).realPart≤0 ∧ -100*(D:Int)≤(compute T i).realPart ∧
    (compute T i).period.natAbs≤10000000000 ∧
    2*(compute T i).phaseInput≤D ∧ 2*(compute T i).expInput≤D := by
  have hr := TaoFivePrimes.rh_fast_kernel_gamma_real_part_bounds T i hT hT' hi
  refine ⟨hr.2,hr.1,RHFastKernelUniformPeriod.period_bound T i hT hT' hi,
    TaoFivePrimes.rh_fast_kernel_gamma_phase_input_bound T i,?_⟩
  exact RHFastKernelUniformPeriod.exp_input_bound (compute T i).realPart hr.1
#print axioms solution
