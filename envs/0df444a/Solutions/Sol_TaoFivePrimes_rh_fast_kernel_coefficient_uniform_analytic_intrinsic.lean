-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic_intrinsic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:21:53.190742+00:00
-- url     : https://prove2.me/submissions/41f85cb6-1941-4121-91c5-43c3046ec2f3

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_uniform_analytic
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_uniform_mass
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_coefficient_uniform_analytic
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
open scoped FourierTransform
namespace RHFastIntrinsicCoefficientMass
lemma grouped_norm {N M K : Nat} (q : Fin N→Fin M)
 (c : Fin N→Fin K→ℂ) (B : Fin M→Fin K→ℂ)
 (hB:∀m k,B m k=∑n:Fin N,if q n=m then c n k else 0) :
 (∑m:Fin M,∑k:Fin K,‖B m k‖)≤∑n:Fin N,∑k:Fin K,‖c n k‖ := by
 have hp (m : Fin M) (k : Fin K) :
   ‖B m k‖≤∑n:Fin N,if q n=m then ‖c n k‖ else 0 := by
  rw [hB m k]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp
 calc
  _ ≤ ∑m:Fin M,∑k:Fin K,∑n:Fin N,if q n=m then ‖c n k‖ else 0 :=
   Finset.sum_le_sum (fun m _=>Finset.sum_le_sum (fun k _=>hp m k))
  _ = ∑k:Fin K,∑m:Fin M,∑n:Fin N,if q n=m then ‖c n k‖ else 0 := Finset.sum_comm
  _ = ∑k:Fin K,∑n:Fin N,∑m:Fin M,if q n=m then ‖c n k‖ else 0 := by
   apply Finset.sum_congr rfl
   intro k hk
   exact Finset.sum_comm
  _ = ∑n:Fin N,∑k:Fin K,∑m:Fin M,if q n=m then ‖c n k‖ else 0 := Finset.sum_comm
  _ = _ := by simp
lemma mass (T : Nat) (hT:T≤4000000000) (B : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then
    (let c:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k
     ((c.1:ℂ)+(c.2:ℂ)*I)/(2:ℂ)^128) else 0) :
 (∑b:Fin 929,∑k:Fin 24,‖B b.val k.val‖)≤1024 := by
 let c : Fin 50000→Fin 24→ℂ:=fun n k=>
   let a:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k.val
   ((a.1:ℂ)+(a.2:ℂ)*I)/(2:ℂ)^128
 have hbin (n : Fin 50000) : RHFastKernelDirichletArithmetic.bin (n.val+1)<929 := by
  have h:=(TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_analytic T (n.val+1) 0 hT
    ⟨by omega,by omega⟩ (by decide)).2.2
  omega
 let q : Fin 50000→Fin 929:=fun n=>⟨RHFastKernelDirichletArithmetic.bin (n.val+1),hbin n⟩
 have hb (b : Fin 929) (k : Fin 24) :
   B b.val k.val=∑n:Fin 50000,if q n=b then c n k else 0 := by
  rw [hB b.val k.val b.isLt k.isLt]
  apply Finset.sum_congr rfl
  intro n hn
  have he:(q n=b) ↔ (RHFastKernelDirichletArithmetic.bin (n.val+1)=b.val):=Fin.ext_iff
  simp only [he,c]
 exact (grouped_norm q c (fun b k=>B b.val k.val) hb).trans
   (TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_mass T hT)
end RHFastIntrinsicCoefficientMass
theorem solution (T : Nat) (hT : 3000000000≤T ∧ T≤3300000000)
 (m : Nat) (hm:m≤1024) (B G : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then
    (let c:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k
     ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0)
 (hF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)‖≤65537)
 (heF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)-G b k‖≤1/10^15) :
 let W : ℝ→ℂ:=fun t=>completedRiemannZeta (1/2+((t+(T:ℝ):ℝ):ℂ)*Complex.I)*
   Complex.exp (((Real.pi*(t+(T:ℝ))/4-t^2/800:ℝ):ℂ))
 ‖(1/512:ℂ)*𝓕 W ((m:ℝ)/512)-
   (1/512:ℂ)*(∑b:Fin 929,∑k:Fin 24,B b.val k.val*G b.val k.val)‖≤3/10^15 := by
 have hM:=RHFastIntrinsicCoefficientMass.mass T (by omega) B hB
 exact TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic T hT m hm B G hB hM hF heF
#print axioms solution
