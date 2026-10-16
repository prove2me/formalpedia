-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_mass
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:07:01.183368+00:00
-- url     : https://prove2.me/submissions/b5f31a66-16a4-4af7-b8f1-0bad732a601d

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_uniform_analytic
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex Finset
namespace RHFastUniformDirichletMass
noncomputable def L (n : Nat) : ℝ := Real.log (n:ℝ)+Real.log Real.pi/2
noncomputable def delta (n : Nat) : ℝ :=
 512*L n/(2*Real.pi)-(RHFastKernelDirichletArithmetic.bin n:ℝ)
noncomputable def weight (T n : Nat) : ℂ := Complex.exp (-(1/2+I*(T:ℂ))*(L n:ℂ))
noncomputable def coefficient (T n k : Nat) : ℂ :=
 let c:=RHFastKernelDirichletArithmetic.coefficient T n k
 ((c.1:ℂ)+(c.2:ℂ)*I)/(2:ℂ)^128
lemma exp_log_scale (n : Nat) (hn:1≤n) : Real.exp (L n)=(n:ℝ)*Real.sqrt Real.pi := by
 have hnR:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
 rw [L,Real.exp_add,Real.exp_log hnR,Real.exp_half,Real.exp_log Real.pi_pos]
lemma weight_bound (T n : Nat) (hn:1≤n) : ‖weight T n‖≤1/Real.sqrt (n:ℝ) := by
 have hnR:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
 have hs:0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
 have hpi:1≤Real.sqrt Real.pi:=(Real.one_le_sqrt).mpr (by linarith [Real.pi_gt_three])
 have he:‖weight T n‖^2=Real.exp (-L n) := by
  rw [weight,Complex.norm_exp,pow_two,←Real.exp_add]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]
  <;> ring
 have hex:Real.exp (-L n)≤1/(n:ℝ) := by
  rw [Real.exp_neg,exp_log_scale n hn,one_div]
  exact inv_anti₀ hnR (by nlinarith)
 have hsq:‖weight T n‖^2*(n:ℝ)≤1:=by
  have h:=mul_le_mul_of_nonneg_right (he.le.trans hex) hnR.le
  simpa only [one_div,inv_mul_cancel₀ (ne_of_gt hnR)] using h
 apply (le_div_iff₀ hs).mpr
 have hs2:=Real.sq_sqrt hnR.le
 have hnon:0≤‖weight T n‖*Real.sqrt (n:ℝ):=mul_nonneg (norm_nonneg _) hs.le
 nlinarith
lemma inverse_sqrt_step (n : Nat) :
 1/Real.sqrt ((n+1:Nat):ℝ)≤2*(Real.sqrt ((n+1:Nat):ℝ)-Real.sqrt (n:ℝ)) := by
 have ha:0<Real.sqrt ((n+1:Nat):ℝ):=Real.sqrt_pos.mpr (by positivity)
 have ha2:=Real.sq_sqrt (show (0:ℝ)≤((n+1:Nat):ℝ) by positivity)
 have hb2:=Real.sq_sqrt (show (0:ℝ)≤(n:ℝ) by positivity)
 have hg:=sq_nonneg (Real.sqrt ((n+1:Nat):ℝ)-Real.sqrt (n:ℝ))
 simp only [Nat.cast_add,Nat.cast_one] at ha ha2 hg ⊢
 apply (div_le_iff₀ ha).mpr
 nlinarith
lemma inverse_sqrt_sum (N : Nat) :
 (∑n∈Finset.range N,1/Real.sqrt ((n+1:Nat):ℝ))≤2*Real.sqrt (N:ℝ) := by
 induction N with
 | zero => simp
 | succ N ih =>
  rw [Finset.sum_range_succ]
  have h:=inverse_sqrt_step N
  exact (add_le_add ih h).trans_eq (by ring)
lemma weight_sum (T : Nat) : (∑n:Fin 50000,‖weight T (n.val+1)‖)≤448 := by
 have hw:(∑n:Fin 50000,‖weight T (n.val+1)‖)≤
   ∑n:Fin 50000,1/Real.sqrt ((n.val+1:Nat):ℝ):=
  Finset.sum_le_sum (fun n _=>weight_bound T (n.val+1) (by omega))
 have h:=inverse_sqrt_sum 50000
 rw [Finset.sum_range] at h
 norm_num only [Nat.cast_ofNat] at h
 have hs:=Real.sq_sqrt (show (0:ℝ)≤50000 by norm_num)
 have hp:=Real.sqrt_nonneg (50000:ℝ)
 have hb:Real.sqrt (50000:ℝ)≤224:=by nlinarith
 exact hw.trans (h.trans (by nlinarith))
lemma power_sum : (∑k:Fin 24,((1:ℝ)/2)^k.val)≤2 := by
 rw [←Finset.sum_range]
 norm_num [Finset.sum_range_succ]
lemma coefficient_bound (T n k : Nat) (hT:T≤4000000000)
 (hn:1≤n ∧ n≤50000) (hk:k<24) :
 ‖coefficient T n k‖≤‖weight T n‖*((1:ℝ)/2)^k+1/10^24 := by
 have h:=TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_analytic T n k hT hn hk
 have he:‖coefficient T n k-weight T n*(delta n:ℂ)^k‖≤1/10^24:=h.1
 have hd:|delta n|≤1/2:=h.2.1
 have hp:‖(delta n:ℂ)^k‖≤((1:ℝ)/2)^k:=by
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hd _
 calc
  _ = ‖(coefficient T n k-weight T n*(delta n:ℂ)^k)+weight T n*(delta n:ℂ)^k‖ := by congr 1; abel
  _ ≤ ‖coefficient T n k-weight T n*(delta n:ℂ)^k‖+‖weight T n*(delta n:ℂ)^k‖ := norm_add_le _ _
  _ ≤ 1/10^24+‖weight T n‖*((1:ℝ)/2)^k := by
   rw [norm_mul]
   exact add_le_add he (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  _ = _ := by ring
lemma total (T : Nat) (hT:T≤4000000000) :
 (∑n:Fin 50000,∑k:Fin 24,‖coefficient T (n.val+1) k.val‖)≤1024 := by
 have hpoint (n : Fin 50000) :
  (∑k:Fin 24,‖coefficient T (n.val+1) k.val‖)≤2*‖weight T (n.val+1)‖+24/10^24 := by
  calc
   _ ≤ ∑k:Fin 24,(‖weight T (n.val+1)‖*((1:ℝ)/2)^k.val+1/10^24) :=
    Finset.sum_le_sum (fun k _=>coefficient_bound T (n.val+1) k.val hT ⟨by omega,by omega⟩ k.isLt)
   _ = ‖weight T (n.val+1)‖*(∑k:Fin 24,((1:ℝ)/2)^k.val)+24/10^24 := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
    simp [div_eq_mul_inv]
   _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left power_sum (norm_nonneg (weight T (n.val+1)))]
 have h:(∑n:Fin 50000,∑k:Fin 24,‖coefficient T (n.val+1) k.val‖)≤
   ∑n:Fin 50000,(2*‖weight T (n.val+1)‖+24/10^24):=
  Finset.sum_le_sum (fun n _=>hpoint n)
 have he:(∑n:Fin 50000,(2*‖weight T (n.val+1)‖+24/10^24))=
   2*(∑n:Fin 50000,‖weight T (n.val+1)‖)+50000*(24/10^24) := by
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  simp [div_eq_mul_inv]
 rw [he] at h
 have hw:=weight_sum T
 linarith
end RHFastUniformDirichletMass
theorem solution (T : Nat) (hT:T≤4000000000) :
 (∑n:Fin 50000,∑k:Fin 24,
  ‖(let c:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k.val
   ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128)‖)≤1024 :=
 RHFastUniformDirichletMass.total T hT
#print axioms solution
