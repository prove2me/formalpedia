-- Prove2me | solution 1 for TaoFivePrimes.rh_fast_kernel_coefficient_uniform_analytic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T22:05:11.057539+00:00
-- url     : https://prove2.me/submissions/48539c7d-85fe-4e12-9cc5-82f864a759b1

import Mathlib
import Definitions.Def_TaoFivePrimes_RHFastKernelDirichletArithmetic
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_uniform_analytic
import Theorems.Thm_TaoFivePrimes_rh_fast_kernel_dirichlet_static_bins_all
import Theorems.Thm_TaoFivePrimes_rh_high_height_finite_dirichlet50000
import Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_taylor24
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
open Complex Finset
open scoped FourierTransform
namespace RHFastUniformGroupedBilinear
lemma grouped {N M K : Nat} (q : Fin N→Fin M)
    (c : Fin N→Fin K→ℂ) (B F : Fin M→Fin K→ℂ)
    (hB:∀m k,B m k=∑n:Fin N,if q n=m then c n k else 0) :
    (∑m:Fin M,∑k:Fin K,B m k*F m k)=∑n:Fin N,∑k:Fin K,c n k*F (q n) k := by
  simp_rw [hB,Finset.sum_mul,ite_mul,zero_mul]
  calc
    _ = ∑k:Fin K,∑m:Fin M,∑n:Fin N,if q n=m then c n k*F m k else 0 := Finset.sum_comm
    _ = ∑k:Fin K,∑n:Fin N,∑m:Fin M,if q n=m then c n k*F m k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑n:Fin N,∑k:Fin K,∑m:Fin M,if q n=m then c n k*F m k else 0 := Finset.sum_comm
    _ = _ := by simp
lemma error {N M K : Nat} (q : Fin N→Fin M)
    (ct cp : Fin N→Fin K→ℂ) (B Ft Fp : Fin M→Fin K→ℂ)
    (εc εf A mass : ℝ) (hεc:0 ≤ εc) (hεf:0 ≤ εf) (hA:0 ≤ A)
    (hB:∀m k,B m k=∑n:Fin N,if q n=m then cp n k else 0)
    (hec:∀n k,‖ct n k-cp n k‖≤ εc)
    (hef:∀m k,‖Ft m k-Fp m k‖≤ εf)
    (hF:∀m k,‖Ft m k‖≤ A)
    (hMass:(∑m:Fin M,∑k:Fin K,‖B m k‖)≤ mass) :
    ‖(∑n:Fin N,∑k:Fin K,ct n k*Ft (q n) k)-
      (∑m:Fin M,∑k:Fin K,B m k*Fp m k)‖≤(N:ℝ)*(K:ℝ)*εc*A+mass*εf := by
  let mid:ℂ:=∑m:Fin M,∑k:Fin K,B m k*Ft m k
  have hmid:mid=∑n:Fin N,∑k:Fin K,cp n k*Ft (q n) k:=grouped q cp B Ft hB
  have hleft:‖(∑n:Fin N,∑k:Fin K,ct n k*Ft (q n) k)-mid‖≤(N:ℝ)*(K:ℝ)*εc*A := by
    rw [hmid,←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n:Fin N,∑k:Fin K,εc*A := by
        apply Finset.sum_le_sum
        intro n hn
        rw [←Finset.sum_sub_distrib]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        rw [←sub_mul,norm_mul]
        exact mul_le_mul (hec n k) (hF (q n) k) (norm_nonneg _) hεc
      _ = _ := by simp;ring
  have hright:‖mid-(∑m:Fin M,∑k:Fin K,B m k*Fp m k)‖≤ mass*εf := by
    dsimp only [mid]
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑m:Fin M,∑k:Fin K,‖B m k‖*εf := by
        apply Finset.sum_le_sum
        intro m hm
        rw [←Finset.sum_sub_distrib]
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        rw [←mul_sub,norm_mul]
        exact mul_le_mul_of_nonneg_left (hef m k) (norm_nonneg _)
      _ = (∑m:Fin M,∑k:Fin K,‖B m k‖)*εf := by simp_rw [←Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hMass hεf
  exact (norm_sub_le_norm_sub_add_norm_sub _ mid _).trans (add_le_add hleft hright)
end RHFastUniformGroupedBilinear

namespace RHFastUniformCoefficient
noncomputable def W (T : Nat) (t : ℝ) : ℂ :=
 completedRiemannZeta (1/2+((t+(T:ℝ):ℝ):ℂ)*I)*
 Complex.exp (((Real.pi*(t+(T:ℝ))/4-t^2/800:ℝ):ℂ))
noncomputable def L (n : Nat) : ℝ := Real.log (n:ℝ)+Real.log Real.pi/2
noncomputable def delta (n : Nat) : ℝ :=
 512*L n/(2*Real.pi)-(RHFastKernelDirichletArithmetic.bin n:ℝ)
noncomputable def weight (T n : Nat) : ℂ :=
 Complex.exp (-(1/2+I*(T:ℂ))*(L n:ℂ))
noncomputable def F (T m b k : Nat) : ℂ :=
 𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)
noncomputable def group (B G : Nat→Nat→ℂ) : ℂ :=
 ∑b:Fin 929,∑k:Fin 24,B b.val k.val*G b.val k.val
noncomputable def proposed (T n k : Nat) : ℂ :=
 let c:=RHFastKernelDirichletArithmetic.coefficient T n k
 ((c.1:ℂ)+(c.2:ℂ)*I)/(2:ℂ)^128
lemma bin_bound (n : Fin 50000) : RHFastKernelDirichletArithmetic.bin (n.val+1)<929 := by
 have h:=TaoFivePrimes.rh_fast_kernel_dirichlet_static_bins_all (n.val+1) ⟨by omega,by omega⟩
 omega
noncomputable def q (n : Fin 50000) : Fin 929 :=
 ⟨RHFastKernelDirichletArithmetic.bin (n.val+1),bin_bound n⟩
lemma grouped_error (T : Nat) (hT : T≤4000000000) (B Ft Fp : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then proposed T (n.val+1) k else 0)
 (hMass:(∑b:Fin 929,∑k:Fin 24,‖B b.val k.val‖)≤1024)
 (hF:∀b k:Nat,b<929 → k<24 → ‖Ft b k‖≤65537)
 (heF:∀b k:Nat,b<929 → k<24 → ‖Ft b k-Fp b k‖≤1/10^15) :
 ‖(∑n:Fin 50000,∑k:Fin 24,
   (weight T (n.val+1)*(delta (n.val+1):ℂ)^k.val)*Ft (RHFastKernelDirichletArithmetic.bin (n.val+1)) k.val)-
   group B Fp‖≤(3/2)/10^12 := by
 have hb (m : Fin 929) (k : Fin 24) :
   B m.val k.val=∑n:Fin 50000,if q n=m then proposed T (n.val+1) k.val else 0 := by
  rw [hB m.val k.val m.isLt k.isLt]
  apply Finset.sum_congr rfl
  intro n hn
  have he:(q n=m) ↔ (RHFastKernelDirichletArithmetic.bin (n.val+1)=m.val):=Fin.ext_iff
  simp only [he]
 have hc (n : Fin 50000) (k : Fin 24) :
   ‖(weight T (n.val+1)*(delta (n.val+1):ℂ)^k.val)-proposed T (n.val+1) k.val‖≤1/10^24 := by
  have h:=(TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_analytic T (n.val+1) k.val hT
    ⟨by omega,by omega⟩ k.isLt).1
  rw [norm_sub_rev]
  exact h
 have h:=RHFastUniformGroupedBilinear.error q
   (fun n k=>weight T (n.val+1)*(delta (n.val+1):ℂ)^k.val)
   (fun n k=>proposed T (n.val+1) k.val) (fun m k=>B m.val k.val)
   (fun m k=>Ft m.val k.val) (fun m k=>Fp m.val k.val)
   (1/10^24) (1/10^15) 65537 1024 (by norm_num) (by norm_num) (by norm_num)
   hb hc (fun m k=>heF m.val k.val m.isLt k.isLt)
   (fun m k=>hF m.val k.val m.isLt k.isLt) hMass
 exact h.trans (by norm_num)
lemma log_identity (n : Nat) (hn:1 ≤ n) : Real.log ((n:ℝ)*Real.sqrt Real.pi)=L n := by
 rw [Real.log_mul (by exact_mod_cast (show n≠0 by omega)) (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)),Real.log_sqrt Real.pi_pos.le]
 rfl
lemma weight_norm (T n : Nat) (hn:1 ≤ n) : ‖weight T n‖≤1 := by
 have hnR:(1:ℝ)≤n:=by exact_mod_cast hn
 have hL:0 ≤ L n := add_nonneg (Real.log_nonneg hnR) (div_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three])) (by norm_num))
 rw [weight,Complex.norm_exp,Real.exp_le_one_iff]
 norm_num [Complex.mul_re,Complex.mul_im] <;> linarith only[hL]

lemma taylor_term (T : Nat) (hT : T≤4000000000) (m n : Nat) (hn:1 ≤ n ∧ n≤50000) :
 ‖weight T n*𝓕 (RHHighSamplingFunctions.gammaWindow (T:ℝ)) ((m:ℝ)/512+L n/(2*Real.pi))-
  ∑k:Fin 24,(weight T n*(delta n:ℂ)^k.val)*F T m (RHFastKernelDirichletArithmetic.bin n) k.val‖≤1/10^20 := by
 have hd:|delta n|≤1/2 := (TaoFivePrimes.rh_fast_kernel_dirichlet_uniform_analytic T n 0 hT hn (by decide)).2.1
 have h:=TaoFivePrimes.rh_high_height_gamma_fourier_taylor24 (T:ℝ) (delta n)
  (((m+RHFastKernelDirichletArithmetic.bin n:Nat):ℝ)/512) hd
 have he:(((m+RHFastKernelDirichletArithmetic.bin n:Nat):ℝ)/512)+delta n/512=(m:ℝ)/512+L n/(2*Real.pi) := by
  unfold delta
  push_cast
  ring
 rw [he,Finset.sum_range] at h
 have heq:weight T n*𝓕 (RHHighSamplingFunctions.gammaWindow (T:ℝ)) ((m:ℝ)/512+L n/(2*Real.pi))-
  ∑k:Fin 24,(weight T n*(delta n:ℂ)^k.val)*F T m (RHFastKernelDirichletArithmetic.bin n) k.val=
  weight T n*(𝓕 (RHHighSamplingFunctions.gammaWindow (T:ℝ)) ((m:ℝ)/512+L n/(2*Real.pi))-
   ∑k:Fin 24,(delta n:ℂ)^k.val*F T m (RHFastKernelDirichletArithmetic.bin n) k.val) := by
  rw [mul_sub,Finset.mul_sum]
  simp only [mul_assoc]
 rw [heq,norm_mul]
 exact (mul_le_mul (weight_norm T n hn.1) h (norm_nonneg _) (by norm_num)).trans_eq (by ring)
lemma analytic_reduction (T : Nat) (hT : 3000000000≤T ∧ T≤3300000000) (m : Nat) (hm:m≤1024) (B G : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then proposed T (n.val+1) k else 0)
 (hMass:(∑b:Fin 929,∑k:Fin 24,‖B b.val k.val‖)≤1024)
 (hF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖F T m b k‖≤65537)
 (heF:∀b:Nat,b<929 → ∀k:Nat,k<24 → ‖F T m b k-G b k‖≤1/10^15) :
 ‖(1/512:ℂ)*𝓕 (W T) ((m:ℝ)/512)-(1/512:ℂ)*group B G‖≤3/10^15 := by
 let A:ℂ:=∑n:Fin 50000,weight T (n.val+1)*𝓕 (RHHighSamplingFunctions.gammaWindow (T:ℝ))
  ((m:ℝ)/512+L (n.val+1)/(2*Real.pi))
 let D:ℂ:=∑n:Fin 50000,∑k:Fin 24,
  (weight T (n.val+1)*(delta (n.val+1):ℂ)^k.val)*F T m (RHFastKernelDirichletArithmetic.bin (n.val+1)) k.val
 have hf:‖𝓕 (W T) ((m:ℝ)/512)-A‖≤1/10^16 := by
  have h:=TaoFivePrimes.rh_high_height_finite_dirichlet50000 (T:ℝ) ((m:ℝ)/512) ⟨by exact_mod_cast hT.1,by exact_mod_cast hT.2⟩ (by positivity)
  change ‖𝓕 (W T) ((m:ℝ)/512)-_‖≤_ at h
  rw [Finset.sum_range] at h
  norm_num only [Complex.ofReal_ofNat,Complex.ofReal_natCast] at h
  have he:(∑n:Fin 50000,Complex.exp (-(1/2+I*(T:ℂ))*(Real.log ((n.val+1:ℝ)*Real.sqrt Real.pi):ℂ))*
   𝓕 (RHHighSamplingFunctions.gammaWindow (T:ℝ))
    ((m:ℝ)/512+Real.log ((n.val+1:ℝ)*Real.sqrt Real.pi)/(2*Real.pi)))=A := by
   apply Finset.sum_congr rfl
   intro n hn
   have hl:=log_identity (n.val+1) (by omega)
   push_cast at hl
   rw [hl]
   rfl
  rw [he] at h
  simpa only [show (10:ℝ)^16=10000000000000000 by norm_num] using h
 have ht:‖A-D‖≤50000/10^20 := by
  dsimp only [A,D]
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
   _ ≤ ∑n:Fin 50000,(1/10^20:ℝ) := by
    exact Finset.sum_le_sum (fun n hn=>taylor_term T (by omega) m (n.val+1) ⟨by omega,by omega⟩)
   _ =_ :=by simp [div_eq_mul_inv]
 have hg:‖D-group B G‖≤(3/2)/10^12 := by
  exact grouped_error T (by omega) B (F T m) G hB hMass (fun b k hb hk=>hF b hb k hk) (fun b k hb hk=>heF b hb k hk)
 have he:‖𝓕 (W T) ((m:ℝ)/512)-group B G‖≤1/10^16+50000/10^20+(3/2)/10^12 := by
  have h1:=norm_sub_le_norm_sub_add_norm_sub (𝓕 (W T) ((m:ℝ)/512)) A (group B G)
  have h2:=norm_sub_le_norm_sub_add_norm_sub A D (group B G)
  linarith only[h1,h2,hf,ht,hg]
 rw [←mul_sub,norm_mul]
 norm_num only[norm_div,norm_one,norm_ofNat]
 exact (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤1/512)).trans (by norm_num)
end RHFastUniformCoefficient
theorem solution (T : Nat) (hT : 3000000000≤T ∧ T≤3300000000)
 (m : Nat) (hm:m≤1024) (B G : Nat→Nat→ℂ)
 (hB:∀b k:Nat,b<929 → k<24 → B b k=
   ∑n:Fin 50000,if RHFastKernelDirichletArithmetic.bin (n.val+1)=b then
    (let c:=RHFastKernelDirichletArithmetic.coefficient T (n.val+1) k
     ((c.1:ℂ)+(c.2:ℂ)*Complex.I)/(2:ℂ)^128) else 0)
 (hMass:(∑b:Fin 929,∑k:Fin 24,‖B b.val k.val‖)≤1024)
 (hF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)‖≤65537)
 (heF:∀b k:Nat,b<929 → k<24 →
   ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) (((m+b:Nat):ℝ)/512)-G b k‖≤1/10^15) :
 let W : ℝ→ℂ:=fun t=>completedRiemannZeta (1/2+((t+(T:ℝ):ℝ):ℂ)*Complex.I)*
   Complex.exp (((Real.pi*(t+(T:ℝ))/4-t^2/800:ℝ):ℂ))
 ‖(1/512:ℂ)*𝓕 W ((m:ℝ)/512)-
   (1/512:ℂ)*(∑b:Fin 929,∑k:Fin 24,B b.val k.val*G b.val k.val)‖≤3/10^15 := by
 exact RHFastUniformCoefficient.analytic_reduction T hT m hm B G hB hMass
  (fun b hb k hk=>hF b k hb hk) (fun b hb k hk=>heF b k hb hk)
#print axioms solution
