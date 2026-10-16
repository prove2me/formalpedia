-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_intrinsic_guards
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T20:39:55.99791+00:00
-- url     : https://prove2.me/submissions/61f88e68-f7d5-468d-93fb-dd5f22622a4f

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_log_rounded_upper
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_trig_guards
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_exp_guards
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 1000000
namespace RHFastDirichletUniformRange
open RHFastKernelGammaArithmetic RHFastKernelLogData
lemma nearest_period (ii : Int) :
  let k : Int := (ii*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))
  2*((ii*10^50-2*(P:Int)*k*(D:Int)).natAbs/(8*10^50))≤D ∧
  (-60000000000*(D:Int)≤ii ∧ ii≤60000000000*(D:Int) → k.natAbs≤10000000000) := by
  dsimp only
  constructor
  · have h0 := Int.emod_nonneg (ii*10^50+(P:Int)*(D:Int))
      (by norm_num [P,D] : (2*(P:Int)*(D:Int))≠0)
    have h1 := Int.emod_lt_of_pos (ii*10^50+(P:Int)*(D:Int))
      (by norm_num [P,D] : (0:Int)<2*(P:Int)*(D:Int))
    have he := Int.emod_add_ediv_mul (ii*10^50+(P:Int)*(D:Int)) (2*(P:Int)*(D:Int))
    norm_num [P,D] at *
    omega
  · intro hii
    norm_num [P,D] at hii ⊢
    omega

lemma loga_bounds (n : Nat) (hn : 0<n) (hN : n≤50000) :
    RHFastKernelDirichletArithmetic.exponent n≤15 ∧
    2^(RHFastKernelDirichletArithmetic.exponent n)≤n ∧
    n≤2^(RHFastKernelDirichletArithmetic.exponent n+1) ∧
    RHFastKernelDirichletArithmetic.loga n≤12*D := by
  have hn0 : n≠0 := by omega
  have he : n.log2≤15 := by
    have h : n.log2<16 := (Nat.log2_lt (k:=16) hn0).mpr (show n<2^16 by omega)
    omega
  have hlo : 2^n.log2≤n := (Nat.le_log2 (k:=n.log2) hn0).mp (Nat.le_refl _)
  have hhi : n≤2^(n.log2+1) := (Nat.lt_log2_self (n:=n)).le
  have hhi' : n≤2*(2^n.log2) := by simpa only [Nat.pow_succ,Nat.mul_comm] using hhi
  have hp : 3*(n-2^n.log2)≤n+2^n.log2 := by omega
  have hlu := TaoFivePrimes.rh_fast_kernel_log_rounded_upper
    (n-2^n.log2) (n+2^n.log2) D hp
  have hc : n.log2*log2≤15*log2 := Nat.mul_le_mul_right _ he
  have hclosed : 15*log2+D+(RHFastKernelLogData.log2pi-log2)/2≤12*D := by decide +kernel
  have hla : RHFastKernelDirichletArithmetic.loga n≤12*D := by
    change n.log2*log2+rounded (n-2^n.log2) (n+2^n.log2) D+(RHFastKernelLogData.log2pi-log2)/2≤12*D
    exact (Nat.add_le_add_right (Nat.add_le_add hc hlu) _).trans hclosed
  exact ⟨he,hlo,hhi,hla⟩

lemma real_bounds (a : Nat) (ha : a≤12*D) :
    -100*(D:Int)≤(-(a:Int))/2 ∧ (-(a:Int))/2≤0 := by
  have hi : (a:Int)≤12*(D:Int) := by exact_mod_cast ha
  have h0 : (0:Int)≤a := Int.natCast_nonneg _
  norm_num [D] at hi ⊢
  omega
lemma phase_bounds (T a : Nat) (hT : T≤4294967040) (ha : a≤12*D) :
    -60000000000*(D:Int)≤-(T:Int)*(a:Int) ∧
    -(T:Int)*(a:Int)≤60000000000*(D:Int) := by
  have hp : T*a≤60000000000*D :=
    (Nat.mul_le_mul hT ha).trans (by decide +kernel)
  have hi : (T:Int)*(a:Int)≤60000000000*(D:Int) := by exact_mod_cast hp
  have h0 : (0:Int)≤(T:Int)*(a:Int) := Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  simp only [neg_mul]
  constructor <;> omega
lemma exp_input_bound (rr : Int) (hrr : -100*(D:Int)≤rr) :
    2*((-rr).toNat/256)≤D := by
  norm_num [D] at hrr ⊢
  omega
lemma bin_delta_bounds (a : Nat) (ha : a≤12*D) :
    2*((512*(a:Int)*10^50-2*(P:Int)*(D:Int)*
      (((512*(a:Int)*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))).toNat:Int))/(2*(P:Int))).natAbs≤D ∧
    ((512*(a:Int)*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))).toNat≤1024 := by
  have hi : (a:Int)≤12*(D:Int) := by exact_mod_cast ha
  have h0 : (0:Int)≤a := Int.natCast_nonneg _
  norm_num [P,D] at hi ⊢
  omega
end RHFastDirichletUniformRange
open RHFastKernelGammaArithmetic RHFastKernelLogData RHFastKernelGenericExpHorner
open RHFastDirichletUniformRange
theorem solution (T n : Nat) (hT : T≤4294967040) (hn : 0<n) (hN : n≤50000) :
  let v := RHFastKernelDirichletArithmetic.compute T n
  v.realPart≤0 ∧ -100*(D:Int)≤v.realPart ∧
  v.period.natAbs≤10000000000 ∧ 2*v.phaseInput≤D ∧ 2*v.expInput≤D ∧
  v.phaseInput^2*horner (cn D) (v.phaseInput^4)≤horner (cp D) (v.phaseInput^4) ∧
  v.phaseInput^2*horner (sn D) (v.phaseInput^4)≤horner (sp D) (v.phaseInput^4) ∧
  0<v.cos ∧ 0<v.expSeed ∧ v.expSeed≤D ∧ v.amplitude≤D ∧
  RHFastKernelDirichletArithmetic.exponent n≤15 ∧
  2^(RHFastKernelDirichletArithmetic.exponent n)≤n ∧
  n≤2^(RHFastKernelDirichletArithmetic.exponent n+1) ∧
  2*(RHFastKernelDirichletArithmetic.delta n).natAbs≤D ∧
  RHFastKernelDirichletArithmetic.bin n≤1024 := by
  let v := RHFastKernelDirichletArithmetic.compute T n
  have hl := loga_bounds n hn hN
  have hla : RHFastKernelDirichletArithmetic.loga n≤12*D := hl.2.2.2
  have hr : -100*(D:Int)≤v.realPart ∧ v.realPart≤0 :=
    real_bounds (RHFastKernelDirichletArithmetic.loga n) hla
  have hphase : -60000000000*(D:Int)≤v.phase ∧ v.phase≤60000000000*(D:Int) :=
    phase_bounds T (RHFastKernelDirichletArithmetic.loga n) hT hla
  have hnear := nearest_period v.phase
  have hp : v.period.natAbs≤10000000000 := hnear.2 hphase
  have hph : 2*v.phaseInput≤D := hnear.1
  have hex : 2*v.expInput≤D := exp_input_bound v.realPart hr.1
  have ht := TaoFivePrimes.rh_fast_kernel_gamma_trig_guards v.phaseInput hph
  have he := TaoFivePrimes.rh_fast_kernel_gamma_exp_guards v.expInput hex
  have hbd := bin_delta_bounds (RHFastKernelDirichletArithmetic.loga n) hla
  have hd : 2*(RHFastKernelDirichletArithmetic.delta n).natAbs≤D := hbd.1
  have hb : RHFastKernelDirichletArithmetic.bin n≤1024 := hbd.2
  exact ⟨hr.2,hr.1,hp,hph,hex,ht.1,ht.2.1,ht.2.2,he.1,he.2.1,he.2.2 8,
    hl.1,hl.2.1,hl.2.2.1,hd,hb⟩
#print axioms solution
