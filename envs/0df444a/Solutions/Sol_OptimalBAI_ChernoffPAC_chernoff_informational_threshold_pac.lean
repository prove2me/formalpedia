-- Prove2me | solution 1 for OptimalBAI.ChernoffPAC.chernoff_informational_threshold_pac
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T12:51:56.173391+00:00
-- url     : https://prove2.me/submissions/f44dd453-972c-474b-a9ff-f522114e5cdb

/-
Released under Apache 2.0 license.
Written by Codex.
-/
import Mathlib
import Definitions.Def_OptimalBAI_ChernoffPAC_KrichevskyTrofimov
import Definitions.Def_OptimalBAI_ChernoffPAC_ChernoffRule



open MeasureTheory ProbabilityTheory Set
namespace OptimalBAI.ChernoffPAC

lemma real_beta_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => u ^ (a-1) * (1-u) ^ (b-1)) volume 0 1 := by
  have h := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hr := h.norm
  apply hr.congr_uIoo
  intro u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := by simpa only [uIoo_of_le zero_le_one] using hu
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_cpow hu'.1.le,
    ← Complex.ofReal_cpow (by linarith [hu'.2] : 0 ≤ 1-u),
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hu'.1.le _)
    (Real.rpow_nonneg (by linarith [hu'.2]) _))]

lemma real_beta_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ u in (0 : ℝ)..1, u ^ (a-1) * (1-u) ^ (b-1)) = beta a b := by
  rw [beta_eq_betaIntegralReal a b ha hb, Complex.betaIntegral]
  have h := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  change _ = RCLike.re (∫ x in (0 : ℝ)..1, (x : ℂ)^((a : ℂ)-1)*(1-(x : ℂ))^((b : ℂ)-1))
  rw [← intervalIntegral.intervalIntegral_re h]
  apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
  intro u hu
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_cpow hu.1.le,
    ← Complex.ofReal_cpow (by linarith [hu.2] : 0 ≤ 1-u),
    ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]

noncomputable def arcsineDensity (u : ℝ) : ℝ := (Real.pi * Real.sqrt (u*(1-u)))⁻¹

lemma density_powers_eq (s f : ℕ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    arcsineDensity u * (u^s*(1-u)^f) =
      Real.pi⁻¹ * (u^((s : ℝ)+1/2-1) * (1-u)^((f : ℝ)+1/2-1)) := by
  have hv : 0 < 1-u := by linarith [hu.2]
  rw [show (s : ℝ)+1/2-1 = (s : ℝ)-1/2 by ring,
    show (f : ℝ)+1/2-1 = (f : ℝ)-1/2 by ring,
    Real.rpow_sub hu.1, Real.rpow_sub hv, Real.rpow_natCast, Real.rpow_natCast]
  simp only [← Real.sqrt_eq_rpow, arcsineDensity, Real.sqrt_mul hu.1.le, mul_inv_rev]
  ring

lemma density_powers_integrable (s f : ℕ) :
    IntervalIntegrable (fun u => arcsineDensity u * (u^s*(1-u)^f)) volume 0 1 := by
  apply ((real_beta_integrable ((s : ℝ)+1/2) ((f : ℝ)+1/2)
    (by positivity) (by positivity)).const_mul Real.pi⁻¹).congr_uIoo
  intro u hu
  exact (density_powers_eq s f (by simpa only [uIoo_of_le zero_le_one] using hu)).symm

lemma density_powers_integral (s f : ℕ) :
    (∫ u in (0 : ℝ)..1, arcsineDensity u * (u^s*(1-u)^f)) =
      beta ((s : ℝ)+1/2) ((f : ℝ)+1/2) / Real.pi := by
  rw [intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    (fun u hu => density_powers_eq s f hu), intervalIntegral.integral_const_mul,
    real_beta_integral _ _ (by positivity) (by positivity)]
  ring

lemma density_integral : (∫ u in (0 : ℝ)..1, arcsineDensity u) = 1 := by
  have h := density_powers_integral 0 0
  simp only [pow_zero,mul_one,Nat.cast_zero,zero_add] at h
  rw [h,beta,Real.Gamma_one_half_eq]
  norm_num [Real.Gamma_one]
  rw [Real.mul_self_sqrt Real.pi_pos.le,div_self Real.pi_ne_zero]

end OptimalBAI.ChernoffPAC


open Finset
namespace OptimalBAI.ChernoffPAC

noncomputable def onesCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (univ.filter (fun i => x i = true)).card

lemma onesCount_le {n : ℕ} (x : Fin n → Bool) : onesCount x ≤ n := by
  exact (card_filter_le _ _).trans_eq (by simp)

lemma bernSeqLik_eq_powers {n : ℕ} (x : Fin n → Bool) (u : ℝ) :
    bernSeqLik u x = u ^ onesCount x * (1-u) ^ (n-onesCount x) := by
  classical
  unfold bernSeqLik onesCount
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  congr 1
  have he : univ.filter (fun i => ¬ x i = true) = Finset.univ \ Finset.univ.filter (fun i => x i = true) := by
    ext i
    simp
  rw [he,Finset.card_sdiff]
  simp

lemma bernSeqLik_nonneg {n : ℕ} (x : Fin n → Bool) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ bernSeqLik u x := by
  apply Finset.prod_nonneg
  intro i hi
  cases h : x i <;> simp [h,hu.1,sub_nonneg.mpr hu.2]

lemma sum_bernSeqLik (n : ℕ) (u : ℝ) : (∑ x : Fin n → Bool, bernSeqLik u x) = 1 := by
  unfold bernSeqLik
  rw [← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b then u else 1-u)]
  simp [Fintype.sum_bool]

end OptimalBAI.ChernoffPAC


open MeasureTheory ProbabilityTheory Set Finset
namespace OptimalBAI.ChernoffPAC

lemma halfGamma_scaled (s : ℕ) :
    Real.Gamma ((s : ℝ)+1/2)*4^s*(s.factorial : ℝ) =
      ((2*s).factorial : ℝ)*Real.sqrt Real.pi := by
  induction s with
  | zero =>
    simpa only [Nat.cast_zero,zero_add,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,Nat.mul_zero,one_mul] using Real.Gamma_one_half_eq
  | succ s ih =>
    have hne : (s : ℝ)+1/2 ≠ 0 := by positivity
    rw [Nat.cast_add,Nat.cast_one,show (s : ℝ)+1+1/2 = ((s : ℝ)+1/2)+1 by ring,
      Real.Gamma_add_one hne,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hnat : 2*(s+1)=((2*s)+1)+1 := by omega
    rw [hnat,Nat.factorial_succ,Nat.factorial_succ]
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    nlinarith [congrArg (fun x : ℝ => (2*(s : ℝ)+1)*(2*(s : ℝ)+2)*x) ih]

noncomputable def ktCount (s f : ℕ) : ℝ := beta ((s : ℝ)+1/2) ((f : ℝ)+1/2)/Real.pi

lemma ktProb_eq_count {n : ℕ} (x : Fin n → Bool) :
    ktProb x = ktCount (onesCount x) (n-onesCount x) := by
  unfold ktProb ktCount
  simp_rw [bernSeqLik_eq_powers]
  exact density_powers_integral _ _

lemma ktCount_pos (s f : ℕ) : 0 < ktCount s f := by
  exact div_pos (beta_pos (by positivity) (by positivity)) Real.pi_pos

lemma ktCount_factorial (s f : ℕ) :
    ktCount s f = (((2*s).factorial : ℝ)*((2*f).factorial : ℝ)) /
      (4^(s+f)*(s.factorial : ℝ)*(f.factorial : ℝ)*((s+f).factorial : ℝ)) := by
  have hs := halfGamma_scaled s
  have hf := halfGamma_scaled f
  have hπ := Real.mul_self_sqrt Real.pi_pos.le
  have hs0 : (s.factorial : ℝ) ≠ 0 := by positivity
  have hf0 : (f.factorial : ℝ) ≠ 0 := by positivity
  have hn0 : ((s+f).factorial : ℝ) ≠ 0 := by positivity
  have hp0 : (4 : ℝ)^(s+f) ≠ 0 := by positivity
  unfold ktCount beta
  rw [show ((s : ℝ)+1/2)+((f : ℝ)+1/2) = ((s+f : ℕ) : ℝ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  apply (div_eq_iff (by positivity : (Real.pi : ℝ) ≠ 0)).mpr
  field_simp
  have hmul := congrArg₂ (fun x y : ℝ => x*y) hs hf
  rw [pow_add]
  rw [show ((s : ℝ)*2+1)/2 = (s : ℝ)+1/2 by ring,
    show (2*(f : ℝ)+1)/2 = (f : ℝ)+1/2 by ring]
  calc
    _ = ((2*s).factorial : ℝ)*Real.sqrt Real.pi * (((2*f).factorial : ℝ)*Real.sqrt Real.pi) := by nlinarith [hmul]
    _ = _ := by nlinarith [congrArg (fun x : ℝ => ((2*s).factorial : ℝ)*((2*f).factorial : ℝ)*x) hπ]

lemma ktProb_nonneg {n : ℕ} (x : Fin n → Bool) : 0 ≤ ktProb x := by
  rw [ktProb_eq_count]
  exact (ktCount_pos _ _).le

lemma sum_ktProb (n : ℕ) : (∑ x : Fin n → Bool, ktProb x) = 1 := by
  classical
  have hi : ∀ x : Fin n → Bool, IntervalIntegrable
      (fun u => arcsineDensity u * bernSeqLik u x) volume 0 1 := by
    intro x
    simp_rw [bernSeqLik_eq_powers]
    exact density_powers_integrable _ _
  unfold ktProb
  change (∑ x : Fin n → Bool, ∫ u in (0 : ℝ)..1, arcsineDensity u*bernSeqLik u x) = 1
  rw [← intervalIntegral.integral_finset_sum (fun x hx => hi x)]
  simp_rw [← Finset.mul_sum,sum_bernSeqLik,mul_one]
  exact density_integral

end OptimalBAI.ChernoffPAC


namespace OptimalBAI.ChernoffPAC

noncomputable def endMass (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4^n

lemma endMass_pos (n : ℕ) : 0 < endMass n := by
  exact div_pos (by exact_mod_cast Nat.centralBinom_pos n) (by positivity)

lemma endMass_succ (n : ℕ) :
    endMass (n+1) * (2*(n : ℝ)+2) = endMass n * (2*(n : ℝ)+1) := by
  have h : ((n : ℝ)+1)*(Nat.centralBinom (n+1) : ℝ) =
      2*(2*(n : ℝ)+1)*(Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold endMass
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp
  nlinarith [h]

lemma endMass_lower_square {n : ℕ} (hn : 1 ≤ n) : 1 ≤ 4*(n : ℝ)*(endMass n)^2 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [endMass,Nat.centralBinom,Nat.choose]
  | succ n hn ih =>
    have hp := endMass_pos (n+1)
    have hq := endMass_pos n
    have hr := endMass_succ n
    have hs : (endMass (n+1))^2*(2*(n : ℝ)+2)^2 =
        (endMass n)^2*(2*(n : ℝ)+1)^2 := by
      simpa only [mul_pow] using congrArg (fun x : ℝ => x^(2 : ℕ)) hr
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsn := congrArg (fun x : ℝ => (n : ℝ)*x) hs
    have hweighted : ((n : ℝ)*(endMass n)^2)*(2*(n : ℝ)+1)^2 ≤
        (((n : ℝ)+1)*(endMass (n+1))^2)*(2*(n : ℝ)+1)^2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ)+1) (sq_nonneg (endMass (n+1)))]
    have hstep := le_of_mul_le_mul_right hweighted (by positivity : 0 < (2*(n : ℝ)+1)^2)
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [hstep]

lemma endMass_lower {n : ℕ} (hn : 1 ≤ n) : 1 ≤ 2*Real.sqrt n*endMass n := by
  have h := endMass_lower_square hn
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hp := endMass_pos n
  have hnonneg : 0 ≤ 2*Real.sqrt n*endMass n := by positivity
  have hsquare : (1 : ℝ)^2 ≤ (2*Real.sqrt n*endMass n)^2 := by
    calc
      (1 : ℝ)^2 = 1 := by norm_num
      _ ≤ 4*(n : ℝ)*(endMass n)^2 := h
      _ = (2*Real.sqrt n*endMass n)^2 := by rw [mul_pow,mul_pow,hs]; norm_num
  exact (sq_le_sq₀ (by norm_num) hnonneg).mp hsquare

end OptimalBAI.ChernoffPAC


namespace OptimalBAI.ChernoffPAC

lemma choose_real_factorial {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) = (n.factorial : ℝ)/((k.factorial : ℝ)*((n-k).factorial : ℝ)) := by
  have h : (n.choose k : ℝ)*(k.factorial : ℝ)*((n-k).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  apply (eq_div_iff (by positivity : (k.factorial : ℝ)*((n-k).factorial : ℝ) ≠ 0)).mpr
  nlinarith [h]

lemma ktCount_choose (s f : ℕ) :
    ktCount s f * ((2*(s+f)).choose (2*s) : ℝ) =
      endMass (s+f)*((s+f).choose s : ℝ) := by
  rw [ktCount_factorial]
  unfold endMass Nat.centralBinom
  rw [choose_real_factorial (by omega : 2*s ≤ 2*(s+f)),
    choose_real_factorial (by omega : s+f ≤ 2*(s+f)),
    choose_real_factorial (by omega : s ≤ s+f)]
  rw [show 2*(s+f)-2*s=2*f by omega,
    show 2*(s+f)-(s+f)=s+f by omega,Nat.add_sub_cancel_left]
  field_simp

lemma ktCount_zero_left (f : ℕ) : ktCount 0 f = endMass f := by
  simpa using ktCount_choose 0 f

lemma ktCount_zero_right (s : ℕ) : ktCount s 0 = endMass s := by
  simpa using ktCount_choose s 0

end OptimalBAI.ChernoffPAC


open ProbabilityTheory
namespace OptimalBAI.ChernoffPAC

lemma ktCount_symm (s f : ℕ) : ktCount s f = ktCount f s := by
  unfold ktCount beta
  congr 2 <;> ring

lemma ktCount_succ_left (s f : ℕ) :
    ktCount (s+1) f = ktCount s f * (((s : ℝ)+1/2)/((s : ℝ)+f+1)) := by
  have hs : (s : ℝ)+1/2 ≠ 0 := by positivity
  have hn : (s : ℝ)+f+1 ≠ 0 := by positivity
  unfold ktCount beta
  simp only [Nat.cast_add,Nat.cast_one]
  rw [show (s : ℝ)+1+1/2=((s : ℝ)+1/2)+1 by ring,
    Real.Gamma_add_one hs,
    show (((s : ℝ)+1/2)+1)+((f : ℝ)+1/2)=((s : ℝ)+f+1)+1 by ring,
    Real.Gamma_add_one hn,
    show ((s : ℝ)+1/2)+((f : ℝ)+1/2)=(s : ℝ)+f+1 by ring]
  field_simp

lemma ktCount_succ_right (s f : ℕ) :
    ktCount s (f+1) = ktCount s f * (((f : ℝ)+1/2)/((s : ℝ)+f+1)) := by
  rw [ktCount_symm s (f+1),ktCount_succ_left,ktCount_symm f s]
  congr 2
  ring

lemma ktCount_le_one (s f : ℕ) : ktCount s f ≤ 1 := by
  induction s with
  | zero =>
    induction f with
    | zero => norm_num [ktCount_zero_left,endMass,Nat.centralBinom]
    | succ f ih =>
      rw [ktCount_succ_right]
      have hc : ((f : ℝ)+1/2)/((0 : ℝ)+f+1) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith
      exact (mul_le_mul_of_nonneg_right ih (by positivity)).trans (by simpa using hc)
  | succ s ih =>
    rw [ktCount_succ_left]
    have hc : ((s : ℝ)+1/2)/((s : ℝ)+f+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hf : (0 : ℝ) ≤ f := Nat.cast_nonneg _
      linarith
    exact (mul_le_mul_of_nonneg_right ih (by positivity)).trans (by simpa using hc)

end OptimalBAI.ChernoffPAC


attribute [local irreducible] OptimalBAI.ChernoffPAC.ktCount

open MeasureTheory BanditAlgorithm Finset
namespace OptimalBAI.ChernoffPAC

noncomputable def historyPulls {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : ℕ :=
  ∑ i, if (h i).1=a then 1 else 0

noncomputable def historyOnes {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : ℕ :=
  ∑ i, if (h i).1=a ∧ (h i).2=1 then 1 else 0

lemma historyOnes_le_pulls {K n : ℕ} (a : Fin K) (h : BanditHistory K n) :
    historyOnes a h ≤ historyPulls a h := by
  classical
  apply sum_le_sum
  intro i hi
  split_ifs <;> omega

lemma historyPulls_le {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : historyPulls a h ≤ n := by
  classical
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℕ) := by apply sum_le_sum; intro i hi; split_ifs <;> omega
    _ = n := by simp

lemma measurable_historyPulls {K n : ℕ} (a : Fin K) : Measurable (historyPulls (n := n) a) := by
  classical
  unfold historyPulls
  apply Finset.measurable_sum
  intro i hi
  have hp : MeasurableSet {h : BanditHistory K n | (h i).1=a} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  exact measurable_const.ite hp measurable_const

lemma measurable_historyOnes {K n : ℕ} (a : Fin K) : Measurable (historyOnes (n := n) a) := by
  classical
  unfold historyOnes
  apply Finset.measurable_sum
  intro i hi
  have hp : MeasurableSet {h : BanditHistory K n | (h i).1=a ∧ (h i).2=1} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  exact measurable_const.ite hp measurable_const

lemma historyPulls_snoc {K n : ℕ} (a : Fin K) (h : BanditHistory K n) (z : Fin K × ℝ) :
    historyPulls a (Fin.snoc h z) = historyPulls a h + if z.1=a then 1 else 0 := by
  classical
  unfold historyPulls
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

lemma historyOnes_snoc {K n : ℕ} (a : Fin K) (h : BanditHistory K n) (z : Fin K × ℝ) :
    historyOnes a (Fin.snoc h z) = historyOnes a h + if z.1=a ∧ z.2=1 then 1 else 0 := by
  classical
  unfold historyOnes
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]

noncomputable def historyRatio {K n : ℕ} (a : Fin K) (u : ℝ) (h : BanditHistory K n) : ℝ :=
  ktCount (historyOnes a h) (historyPulls a h-historyOnes a h) /
    (u^(historyOnes a h)*(1-u)^(historyPulls a h-historyOnes a h))

noncomputable def historyPairRatio {K n : ℕ} (a b : Fin K) (μ : Fin K → ℝ)
    (h : BanditHistory K n) : ℝ := historyRatio a (μ a) h * historyRatio b (μ b) h

lemma measurable_historyRatio {K n : ℕ} (a : Fin K) (u : ℝ) :
    Measurable (historyRatio (n := n) a u) := by
  have hm : Measurable (fun p : ℕ × ℕ => ktCount p.2 (p.1-p.2) /
      (u^p.2*(1-u)^(p.1-p.2))) := measurable_of_countable _
  exact hm.comp ((measurable_historyPulls a).prodMk (measurable_historyOnes a))

lemma measurable_historyPairRatio {K n : ℕ} (a b : Fin K) (μ : Fin K → ℝ) :
    Measurable (historyPairRatio (n := n) a b μ) :=
  (measurable_historyRatio a (μ a)).mul (measurable_historyRatio b (μ b))

lemma historyRatio_nonneg {K n : ℕ} (a : Fin K) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (h : BanditHistory K n) : 0 ≤ historyRatio a u h := by
  unfold historyRatio
  exact div_nonneg (ktCount_pos _ _).le
    (mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg (sub_nonneg.mpr hu.2) _))

noncomputable def predictive {K n : ℕ} (a : Fin K) (h : BanditHistory K n) : ℝ :=
  ((historyOnes a h : ℝ)+1/2)/((historyPulls a h : ℝ)+1)

lemma predictive_mem {K n : ℕ} (a : Fin K) (h : BanditHistory K n) :
    predictive a h ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · unfold predictive; positivity
  · unfold predictive
    apply (div_lt_one (by positivity)).mpr
    have he : (historyOnes a h : ℝ) ≤ historyPulls a h := by exact_mod_cast historyOnes_le_pulls a h
    linarith

lemma historyRatio_snoc_other {K n : ℕ} (a : Fin K) (u : ℝ) (h : BanditHistory K n)
    (z : Fin K × ℝ) (hz : z.1 ≠ a) : historyRatio a u (Fin.snoc h z) = historyRatio a u h := by
  unfold historyRatio
  rw [historyPulls_snoc,historyOnes_snoc]
  simp [hz]

lemma historyRatio_snoc_one {K n : ℕ} (a : Fin K) (u : ℝ) (h : BanditHistory K n) :
    historyRatio a u (Fin.snoc h (a,1)) = historyRatio a u h * (predictive a h/u) := by
  have he : historyOnes a h+(historyPulls a h-historyOnes a h)=historyPulls a h :=
    Nat.add_sub_of_le (historyOnes_le_pulls a h)
  unfold historyRatio
  rw [historyPulls_snoc,historyOnes_snoc]
  simp only [and_self,ite_true,show (a : Fin K)=a by rfl,Nat.add_sub_add_right]
  rw [ktCount_succ_left,pow_succ]
  unfold predictive
  have he' : (historyOnes a h : ℝ)+(historyPulls a h-historyOnes a h : ℕ)+1=
      (historyPulls a h : ℝ)+1 := by exact_mod_cast congrArg (fun n : ℕ => n+1) he
  rw [he']
  ring

lemma historyRatio_snoc_zero {K n : ℕ} (a : Fin K) (u : ℝ) (h : BanditHistory K n) :
    historyRatio a u (Fin.snoc h (a,0)) = historyRatio a u h * ((1-predictive a h)/(1-u)) := by
  have hon := historyOnes_le_pulls a h
  have he : historyPulls a h+1-historyOnes a h=(historyPulls a h-historyOnes a h)+1 := by omega
  unfold historyRatio
  rw [historyPulls_snoc,historyOnes_snoc]
  simp only [show (a : Fin K)=a by rfl,ite_true,show ¬ ((0 : ℝ)=1) by norm_num,and_false,ite_false,add_zero]
  rw [he,ktCount_succ_right,pow_succ]
  unfold predictive
  have he' : ((historyOnes a h : ℝ)+(historyPulls a h-historyOnes a h : ℕ)+1) =
      (historyPulls a h : ℝ)+1 := by
    exact_mod_cast congrArg (fun n : ℕ => n+1) (Nat.add_sub_of_le hon)
  rw [he']
  have hd : ((historyPulls a h : ℝ)+1) ≠ 0 := by positivity
  have hc : ((historyPulls a h-historyOnes a h : ℕ) : ℝ) = (historyPulls a h : ℝ)-historyOnes a h :=
    Nat.cast_sub hon
  have hcoef : (((historyPulls a h-historyOnes a h : ℕ) : ℝ)+1/2)/((historyPulls a h : ℝ)+1) =
      1-((historyOnes a h : ℝ)+1/2)/((historyPulls a h : ℝ)+1) := by
    rw [hc]
    field_simp
    ring
  rw [hcoef]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end OptimalBAI.ChernoffPAC


open MeasureTheory ProbabilityTheory Set Finset MeasurableSpace Preorder
namespace OptimalBAI.ChernoffPAC

lemma bounded_real_integrable {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsFiniteMeasure P] {f : Z → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) : Integrable f P := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

lemma trajectory_supermartingale {X : Type*} [MeasurableSpace X]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (κ : (t : ℕ) → Kernel (Finset.Iic t → X) X) [∀ t, IsMarkovKernel (κ t)]
    (f : (t : ℕ) → (Finset.Iic t → X) → ℝ)
    (g : (t : ℕ) → (Finset.Iic t → X) → X → ℝ)
    (hf : ∀ t, Measurable (f t)) (hg : ∀ t, Measurable (g t).uncurry)
    (hfb : ∀ t, ∃ C : ℝ, ∀ h, ‖f t h‖ ≤ C)
    (hgb : ∀ t, ∃ C : ℝ, ∀ h z, ‖g t h z‖ ≤ C)
    (heq : ∀ t (ω : ℕ → X), f (t+1) (frestrictLe (t+1) ω) = g t (frestrictLe t ω) (ω (t+1)))
    (hmean : ∀ t h, (∫ z, g t h z ∂κ t h) ≤ f t h) :
    Supermartingale (fun t ω => f t (frestrictLe t ω))
      (Filtration.piLE (X := fun _ : ℕ => X)) (Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ κ) := by
  let P := Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ κ
  have hI : ∀ t, Integrable (fun ω => f t (frestrictLe t ω)) P := by
    intro t
    obtain ⟨C,hC⟩ := hfb t
    exact bounded_real_integrable P ((hf t).comp (measurable_frestrictLe t))
      (fun ω => hC (frestrictLe t ω))
  have hadp : StronglyAdapted (Filtration.piLE (X := fun _ : ℕ => X))
      (fun t ω => f t (frestrictLe t ω)) := by
    intro t
    rw [Filtration.piLE_eq_comap_frestrictLe (X := fun _ : ℕ => X)]
    exact ((hf t).comp (comap_measurable (fun ω : ℕ → X => frestrictLe t ω))).stronglyMeasurable
  apply supermartingale_of_setIntegral_succ_le hadp hI
  intro t S hS
  rw [Filtration.piLE_eq_comap_frestrictLe,measurableSet_comap] at hS
  obtain ⟨A,hA,rfl⟩ := hS
  let Q := P.map (frestrictLe t)
  have hjoint : Q ⊗ₘ κ t = P.map (fun ω => (frestrictLe t ω,ω (t+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hGI : Integrable (g t).uncurry (Q ⊗ₘ κ t) := by
    obtain ⟨C,hC⟩ := hgb t
    exact bounded_real_integrable _ (hg t) (fun p => hC p.1 p.2)
  have hFI : Integrable (f t) Q := by
    obtain ⟨C,hC⟩ := hfb t
    exact bounded_real_integrable _ (hf t) hC
  have hinnerI : Integrable (fun h => ∫ z, g t h z ∂κ t h) Q := by
    exact hGI.integral_compProd
  calc
    _ = ∫ p in A ×ˢ Set.univ, (g t).uncurry p ∂P.map (fun ω => (frestrictLe t ω,ω (t+1))) := by
      rw [setIntegral_map (hA.prod MeasurableSet.univ) (hg t).aestronglyMeasurable
        (by fun_prop)]
      have hpre : (fun ω => (frestrictLe t ω,ω (t+1))) ⁻¹' (A ×ˢ Set.univ) = (fun ω : ℕ → X => frestrictLe t ω) ⁻¹' A := by
        ext ω; simp
      rw [hpre]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => heq t ω))
    _ = ∫ p in A ×ˢ Set.univ, (g t).uncurry p ∂(Q ⊗ₘ κ t) := by rw [hjoint]
    _ = ∫ h in A, ∫ z, g t h z ∂κ t h ∂Q := by
      rw [Measure.setIntegral_compProd hA MeasurableSet.univ hGI.integrableOn]
      simp only [setIntegral_univ]
      rfl
    _ ≤ ∫ h in A, f t h ∂Q := setIntegral_mono_on hinnerI.integrableOn hFI.integrableOn hA
      (fun h hh => hmean t h)
    _ = _ := setIntegral_map hA (hf t).aestronglyMeasurable (by fun_prop)

end OptimalBAI.ChernoffPAC


open MeasureTheory BanditAlgorithm
namespace OptimalBAI.ChernoffPAC

noncomputable def ratioScale (u : ℝ) : ℝ := max 1 (max u⁻¹ (1-u)⁻¹)

lemma ratioScale_one_le (u : ℝ) : 1 ≤ ratioScale u := le_max_left _ _

lemma historyRatio_bound {K n : ℕ} (a : Fin K) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (h : BanditHistory K n) : historyRatio a u h ≤ (ratioScale u)^n := by
  let s := historyOnes a h
  let f := historyPulls a h-s
  have hs : s+f=historyPulls a h := Nat.add_sub_of_le (historyOnes_le_pulls a h)
  have hsu : u⁻¹ ≤ ratioScale u := (le_max_left _ _).trans (le_max_right _ _)
  have hfu : (1-u)⁻¹ ≤ ratioScale u := (le_max_right _ _).trans (le_max_right _ _)
  have hC := ratioScale_one_le u
  have hC0 : 0 ≤ ratioScale u := le_trans zero_le_one hC
  have hu0 : 0 ≤ u⁻¹ := inv_nonneg.mpr hu.1
  have hf0 : 0 ≤ (1-u)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hu.2)
  unfold historyRatio
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow]
  calc
    _ = ktCount s f*(u⁻¹^s*(1-u)⁻¹^f) := by ring
    _ ≤ 1*((ratioScale u)^s*(ratioScale u)^f) := by
      apply mul_le_mul (ktCount_le_one s f)
        (mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr hu.1) hsu _)
          (pow_le_pow_left₀ (inv_nonneg.mpr (sub_nonneg.mpr hu.2)) hfu _) (by positivity) (by positivity))
        (by positivity) (by norm_num)
    _ = (ratioScale u)^(historyPulls a h) := by rw [one_mul,← pow_add,hs]
    _ ≤ (ratioScale u)^n := pow_le_pow_right₀ hC (historyPulls_le a h)

lemma historyPairRatio_bound {K n : ℕ} (a b : Fin K) (μ : Fin K → ℝ)
    (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) (h : BanditHistory K n) :
    ‖historyPairRatio a b μ h‖ ≤ (ratioScale (μ a))^n*(ratioScale (μ b))^n := by
  have ha := historyRatio_nonneg a (hμ a) h
  have hb := historyRatio_nonneg b (hμ b) h
  unfold historyPairRatio
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ha hb)]
  exact mul_le_mul (historyRatio_bound a (hμ a) h) (historyRatio_bound b (hμ b) h)
    hb (pow_nonneg (le_trans zero_le_one (ratioScale_one_le (μ a))) _)

lemma bernoulli_integral {K : ℕ} (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (f : ℝ → ℝ) :
    (∫ x, f x ∂(bernoulliBandit μ hμ).P i) = μ i*f 1+(1-μ i)*f 0 := by
  change (∫ x, f x ∂(ENNReal.ofReal (μ i) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1-μ i) • Measure.dirac (0 : ℝ))) = _
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,integral_dirac,integral_dirac,
    ENNReal.toReal_ofReal (hμ i).1,ENNReal.toReal_ofReal (sub_nonneg.mpr (hμ i).2)]
  rfl

lemma reward_ratio_expect_le {K n : ℕ} (a b : Fin K) (hab : a ≠ b)
    (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (h : BanditHistory K n) (i : Fin K) :
    (∫ x, historyPairRatio a b μ (Fin.snoc h (i,x)) ∂(bernoulliBandit μ hμ).P i) ≤
      historyPairRatio a b μ h := by
  rw [bernoulli_integral]
  have hnonneg : 0 ≤ historyPairRatio a b μ h :=
    mul_nonneg (historyRatio_nonneg a (hμ a) h) (historyRatio_nonneg b (hμ b) h)
  by_cases ha : i=a
  · subst i
    have hp := predictive_mem a h
    unfold historyPairRatio
    rw [historyRatio_snoc_one,historyRatio_snoc_zero,
      historyRatio_snoc_other b (μ b) h (a,1) hab,
      historyRatio_snoc_other b (μ b) h (a,0) hab]
    have h1 : μ a/μ a ≤ 1 := div_self_le_one _
    have h0 : (1-μ a)/(1-μ a) ≤ 1 := div_self_le_one _
    have hcoef : μ a*(predictive a h/μ a)+(1-μ a)*((1-predictive a h)/(1-μ a)) ≤ 1 := by
      have h1' := mul_le_mul_of_nonneg_left h1 hp.1.le
      have h0' := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hp.2.le)
      simp only [div_eq_mul_inv] at h1' h0' ⊢
      nlinarith [h1',h0']
    have h := mul_le_mul_of_nonneg_left hcoef hnonneg
    unfold historyPairRatio at h
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith [h]
  · by_cases hb : i=b
    · subst i
      have hp := predictive_mem b h
      unfold historyPairRatio
      rw [historyRatio_snoc_other a (μ a) h (b,1) hab.symm,
        historyRatio_snoc_other a (μ a) h (b,0) hab.symm,
        historyRatio_snoc_one,historyRatio_snoc_zero]
      have h1 : μ b/μ b ≤ 1 := div_self_le_one _
      have h0 : (1-μ b)/(1-μ b) ≤ 1 := div_self_le_one _
      have hcoef : μ b*(predictive b h/μ b)+(1-μ b)*((1-predictive b h)/(1-μ b)) ≤ 1 := by
        have h1' := mul_le_mul_of_nonneg_left h1 hp.1.le
        have h0' := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hp.2.le)
        simp only [div_eq_mul_inv] at h1' h0' ⊢
        nlinarith [h1',h0']
      have h := mul_le_mul_of_nonneg_left hcoef hnonneg
      unfold historyPairRatio at h
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith [h]
    · unfold historyPairRatio
      rw [historyRatio_snoc_other a (μ a) h (i,1) ha,
        historyRatio_snoc_other a (μ a) h (i,0) ha,
        historyRatio_snoc_other b (μ b) h (i,1) hb,
        historyRatio_snoc_other b (μ b) h (i,0) hb]
      nlinarith

end OptimalBAI.ChernoffPAC


open MeasureTheory ProbabilityTheory BanditAlgorithm
namespace OptimalBAI.ChernoffPAC

lemma step_ratio_expect_le {K n : ℕ} (a b : Fin K) (hab : a ≠ b)
    (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy K) (h : BanditHistory K n) :
    (∫ z, historyPairRatio a b μ (Fin.snoc h z) ∂banditStepKernel (bernoulliBandit μ hμ) π n h) ≤
      historyPairRatio a b μ h := by
  have hm : Measurable (fun z : Fin K × ℝ => historyPairRatio a b μ (Fin.snoc h z)) := by
    exact (measurable_historyPairRatio a b μ).comp
      (measurable_banditHistorySnoc.comp (measurable_const.prodMk measurable_id))
  have hI : Integrable (fun z => historyPairRatio a b μ (Fin.snoc h z))
      (banditStepKernel (bernoulliBandit μ hμ) π n h) :=
    bounded_real_integrable _ hm (fun z => historyPairRatio_bound a b μ hμ (Fin.snoc h z))
  unfold banditStepKernel at hI ⊢
  rw [ProbabilityTheory.integral_compProd hI]
  simp only [Kernel.comap_apply,banditRewardKernel,Kernel.ofFunOfCountable]
  have hint : Integrable (fun i : Fin K =>
      ∫ x, historyPairRatio a b μ (Fin.snoc h (i,x)) ∂(bernoulliBandit μ hμ).P i) (π.select n h) := by
    exact Integrable.of_finite
  have h := integral_mono hint (integrable_const (historyPairRatio a b μ h))
    (fun i => reward_ratio_expect_le a b hab μ hμ h i)
  simpa using h

lemma historyPairRatio_empty {K : ℕ} (a b : Fin K) (μ : Fin K → ℝ)
    (h : BanditHistory K 0) : historyPairRatio a b μ h = 1 := by
  simp [historyPairRatio,historyRatio,historyOnes,historyPulls,ktCount_zero_left,endMass,Nat.centralBinom]

end OptimalBAI.ChernoffPAC


open MeasureTheory ProbabilityTheory Set
namespace OptimalBAI.ChernoffPAC

lemma ville_finite {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M F P) (hpos : ∀ t ω, 0 ≤ M t ω)
    (hinit : (∫ ω, M 0 ω ∂P) ≤ 1) {B : ℝ} (hB : 0 < B) (N : ℕ) :
    P {ω | ∃ t ≤ N, B ≤ M t ω} ≤ ENNReal.ofReal (1/B) := by
  let τ : Ω → WithTop ℕ := fun ω => (hittingBtwn M (Ici B) 0 N ω : ℕ)
  have hτ : IsStoppingTime F τ := by
    have h := hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn (s := Ici B)
      (n := 0) (n' := N) measurableSet_Ici
    intro i
    convert h i using 1 <;> rfl
  have hbdd : ∀ ω, τ ω ≤ N := by
    intro ω
    change ((hittingBtwn M (Ici B) 0 N ω : ℕ) : WithTop ℕ) ≤ (N : WithTop ℕ)
    exact_mod_cast (hittingBtwn_le (u := M) (s := Ici B) (n := 0) (m := N) ω)
  have hle : (fun _ : Ω => (0 : WithTop ℕ)) ≤ τ := fun _ => bot_le
  have hopt := hM.neg.expected_stoppedValue_mono (isStoppingTime_const F 0) hτ hle hbdd
  have hopt' : (∫ ω, stoppedValue M τ ω ∂P) ≤ ∫ ω, M 0 ω ∂P := by
    have hh : (∫ ω, -M 0 ω ∂P) ≤ ∫ ω, -stoppedValue M τ ω ∂P := by
      convert hopt using 1 <;> congr 1 <;> funext ω <;> rfl
    simpa only [integral_neg,neg_le_neg_iff] using hh
  have hI : Integrable (stoppedValue M τ) P := by
    have h := hM.neg.integrable_stoppedValue hτ hbdd
    convert h.neg using 1
    ext ω
    simp only [stoppedValue,Pi.neg_apply,neg_neg]
  have hnonneg : ∀ ω, 0 ≤ stoppedValue M τ ω := by
    intro ω
    exact hpos _ _
  have hhit : ∀ ω ∈ {ω | ∃ t ≤ N, B ≤ M t ω}, B ≤ stoppedValue M τ ω := by
    intro ω hω
    obtain ⟨t,ht,hMt⟩ := hω
    exact stoppedValue_hittingBtwn_mem (u := M) (s := Ici B) ⟨t,⟨Nat.zero_le _,ht⟩,hMt⟩
  have hbound := (hI.div_const B).measure_le_integral (ae_of_all _ fun ω => div_nonneg (hnonneg ω) hB.le)
    (fun ω hω => (one_le_div hB).mpr (hhit ω hω))
  rw [integral_div] at hbound
  exact hbound.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hopt'.trans hinit) hB.le))

lemma ville {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M F P) (hpos : ∀ t ω, 0 ≤ M t ω)
    (hinit : (∫ ω, M 0 ω ∂P) ≤ 1) {B : ℝ} (hB : 0 < B) :
    P {ω | ∃ t, B ≤ M t ω} ≤ ENNReal.ofReal (1/B) := by
  have he : {ω | ∃ t, B ≤ M t ω} = ⋃ N : ℕ, {ω | ∃ t ≤ N, B ≤ M t ω} := by
    ext ω
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨t,ht⟩; exact ⟨t,t,le_rfl,ht⟩
    · rintro ⟨N,t,ht,hM⟩; exact ⟨t,hM⟩
  rw [he,(show Monotone (fun N : ℕ => {ω | ∃ t ≤ N, B ≤ M t ω}) from
    fun a b hab ω ⟨t,ht,hMt⟩ => ⟨t,ht.trans hab,hMt⟩).measure_iUnion]
  exact iSup_le (fun N => ville_finite hM hpos hinit hB N)

end OptimalBAI.ChernoffPAC



open MeasureTheory ProbabilityTheory BanditAlgorithm Finset Preorder
namespace OptimalBAI.ChernoffPAC

lemma iicHistory_snoc {K : ℕ} (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    banditIicHistory K (t+1) (frestrictLe (t+1) ω) =
      Fin.snoc (banditIicHistory K t (frestrictLe t ω)) (ω (t+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    rfl
  · rw [Fin.snoc_castSucc]
    rfl

lemma pairRatio_supermartingale {K : ℕ} (a b : Fin K) (hab : a ≠ b)
    (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) (π : BanditPolicy K) :
    Supermartingale (fun t ω => historyPairRatio a b μ
      (banditIicHistory K t (frestrictLe t ω)))
      (Filtration.piLE (X := fun _ : ℕ => Fin K × ℝ))
      (banditTrajMeasure (bernoulliBandit μ hμ) π) := by
  unfold banditTrajMeasure
  apply trajectory_supermartingale
    (banditStepKernel (bernoulliBandit μ hμ) π 0 (fun i : Fin 0 => i.elim0))
    (banditTrajKernel (bernoulliBandit μ hμ) π)
    (f := fun t h => historyPairRatio a b μ (banditIicHistory K t h))
    (g := fun t h z => historyPairRatio a b μ (Fin.snoc (banditIicHistory K t h) z))
  · intro t
    exact (measurable_historyPairRatio a b μ).comp measurable_banditIicHistory
  · intro t
    exact (measurable_historyPairRatio a b μ).comp (measurable_banditHistorySnoc.comp
      ((measurable_banditIicHistory.comp measurable_fst).prodMk measurable_snd))
  · intro t
    exact ⟨_,fun h => historyPairRatio_bound a b μ hμ _⟩
  · intro t
    exact ⟨_,fun h z => historyPairRatio_bound a b μ hμ _⟩
  · intro t ω
    rw [iicHistory_snoc]
  · intro t h
    unfold banditTrajKernel
    rw [Kernel.comap_apply]
    exact step_ratio_expect_le a b hab μ hμ π _

lemma initial_prefix_law {X : Type*} [MeasurableSpace X]
    (μ₀ : Measure X) [IsProbabilityMeasure μ₀]
    (κ : (t : ℕ) → Kernel (Finset.Iic t → X) X) [∀ t, IsMarkovKernel (κ t)] :
    (Kernel.trajMeasure (X := fun _ : ℕ => X) μ₀ κ).map (frestrictLe 0) =
      μ₀.map (MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => X)).symm := by
  rw [Kernel.trajMeasure,Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe,Kernel.partialTraj_self,Measure.id_comp]

lemma pairRatio_initial_expect_le {K : ℕ} (a b : Fin K) (hab : a ≠ b)
    (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) (π : BanditPolicy K) :
    (∫ ω, historyPairRatio a b μ (banditIicHistory K 0 (frestrictLe 0 ω))
      ∂banditTrajMeasure (bernoulliBandit μ hμ) π) ≤ 1 := by
  let f : (Finset.Iic 0 → Fin K × ℝ) → ℝ := fun h => historyPairRatio a b μ (banditIicHistory K 0 h)
  have hf : Measurable f := (measurable_historyPairRatio a b μ).comp measurable_banditIicHistory
  change (∫ ω, f (frestrictLe 0 ω) ∂banditTrajMeasure (bernoulliBandit μ hμ) π) ≤ 1
  rw [← integral_map (measurable_frestrictLe 0).aemeasurable hf.aestronglyMeasurable]
  unfold banditTrajMeasure
  rw [initial_prefix_law,integral_map (by fun_prop) hf.aestronglyMeasurable]
  have he : ∀ z : Fin K × ℝ, f ((MeasurableEquiv.piUnique (fun _i : Finset.Iic 0 => Fin K × ℝ)).symm z) =
      historyPairRatio a b μ (Fin.snoc (fun i : Fin 0 => i.elim0) z) := by
    intro z
    congr 1
  simp_rw [he]
  exact (step_ratio_expect_le a b hab μ hμ π (fun i : Fin 0 => i.elim0)).trans_eq
    (historyPairRatio_empty a b μ _)

end OptimalBAI.ChernoffPAC


open MeasureTheory BanditAlgorithm Finset Preorder
namespace OptimalBAI.ChernoffPAC

lemma ones_count_le {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    trajOnesCount a t ω ≤ trajPullCount a t ω := by
  unfold trajOnesCount trajPullCount
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2.1⟩

lemma historyPulls_prefix {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    historyPulls a (banditTrajPrefix K t ω) = trajPullCount a t ω := by
  classical
  unfold historyPulls trajPullCount banditTrajPrefix
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact (Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a then (1 : ℕ) else 0) t)

lemma historyOnes_prefix {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    historyOnes a (banditTrajPrefix K t ω) = trajOnesCount a t ω := by
  classical
  unfold historyOnes trajOnesCount banditTrajPrefix
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact (Fin.sum_univ_eq_sum_range (fun i => if (ω i).1=a ∧ (ω i).2=1 then (1 : ℕ) else 0) t)

lemma iicHistory_prefix {K : ℕ} (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    banditIicHistory K t (frestrictLe t ω) = banditTrajPrefix K (t+1) ω := rfl

lemma pair_pulls_le {K : ℕ} (a b : Fin K) (hab : a ≠ b) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    trajPullCount a t ω + trajPullCount b t ω ≤ t := by
  classical
  unfold trajPullCount
  have hd : Disjoint ((range t).filter fun i => (ω i).1=a) ((range t).filter fun i => (ω i).1=b) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact hab ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
  rw [← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans_eq (card_range t)

end OptimalBAI.ChernoffPAC



open MeasureTheory ProbabilityTheory BanditAlgorithm Preorder
namespace OptimalBAI.ChernoffPAC

variable {K : ℕ}

def goodReward (μ : Fin K → ℝ) (z : Fin K × ℝ) : Prop :=
  (z.2=1 ∧ 0 < μ z.1) ∨ (z.2=0 ∧ μ z.1 < 1)

lemma measurableSet_goodReward (μ : Fin K → ℝ) : MeasurableSet {z | goodReward μ z} := by
  unfold goodReward
  apply MeasurableSet.union
  · exact (measurableSet_eq_fun measurable_snd measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_of_countable μ).comp measurable_fst))
  · exact (measurableSet_eq_fun measurable_snd measurable_const).inter
      (measurableSet_lt ((measurable_of_countable μ).comp measurable_fst) measurable_const)

lemma bernoulli_ae_goodReward (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) : ∀ᵐ x ∂(bernoulliBandit μ hμ).P i, goodReward μ (i,x) := by
  change ∀ᵐ x ∂(ENNReal.ofReal (μ i) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1-μ i) • Measure.dirac (0 : ℝ)), goodReward μ (i,x)
  rw [ae_add_measure_iff]
  constructor
  · by_cases hi : μ i=0
    · simp [hi]
    · refine Measure.ae_smul_measure ?_ _
      simp only [ae_dirac_eq,Filter.eventually_pure]
      exact Or.inl ⟨rfl,lt_of_le_of_ne (hμ i).1 (Ne.symm hi)⟩
  · by_cases hi : μ i=1
    · simp [hi]
    · refine Measure.ae_smul_measure ?_ _
      simp only [ae_dirac_eq,Filter.eventually_pure]
      exact Or.inr ⟨rfl,lt_of_le_of_ne (hμ i).2 hi⟩

lemma step_ae_goodReward (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy K) (n : ℕ) (h : BanditHistory K n) :
    ∀ᵐ z ∂banditStepKernel (bernoulliBandit μ hμ) π n h, goodReward μ z := by
  unfold banditStepKernel
  apply Kernel.ae_compProd_of_ae_ae (measurableSet_goodReward μ)
  apply Filter.Eventually.of_forall
  intro i
  simp only [Kernel.comap_apply,banditRewardKernel,Kernel.ofFunOfCountable]
  convert bernoulli_ae_goodReward μ hμ i using 1 <;> rfl

lemma coordinate_zero_law (ν : StochasticBandit K) (π : BanditPolicy K) :
    (banditTrajMeasure ν π).map (fun ω => ω 0) = banditStepKernel ν π 0 (fun i => i.elim0) := by
  have he : (fun ω : ℕ → Fin K × ℝ => ω 0) =
      (fun h : Finset.Iic 0 → Fin K × ℝ => h ⟨0,by simp⟩) ∘ frestrictLe 0 := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold banditTrajMeasure
  rw [initial_prefix_law,Measure.map_map (by fun_prop) (by fun_prop)]
  convert Measure.map_id using 1 <;> rfl

lemma coordinate_succ_law (ν : StochasticBandit K) (π : BanditPolicy K) (t : ℕ) :
    (banditTrajMeasure ν π).map (fun ω => ω (t+1)) =
      banditTrajKernel ν π t ∘ₘ (banditTrajMeasure ν π).map (frestrictLe t) := by
  rw [← Measure.snd_compProd]
  have hj := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Fin K × ℝ)
    (μ₀ := banditStepKernel ν π 0 (fun i => i.elim0)) (κ := banditTrajKernel ν π) (a := t)
  change _ = ((banditTrajMeasure ν π).map (frestrictLe t) ⊗ₘ banditTrajKernel ν π t).map Prod.snd
  unfold banditTrajMeasure
  rw [hj,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma trajectory_ae_goodRewards (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy K) : ∀ᵐ ω ∂banditTrajMeasure (bernoulliBandit μ hμ) π,
      ∀ t, goodReward μ (ω t) := by
  apply ae_all_iff.mpr
  intro t
  cases t with
  | zero =>
    apply ae_of_ae_map (measurable_pi_apply 0).aemeasurable
    rw [coordinate_zero_law]
    exact step_ae_goodReward μ hμ π 0 _
  | succ t =>
    apply ae_of_ae_map (measurable_pi_apply (t+1)).aemeasurable
    rw [coordinate_succ_law]
    apply Measure.ae_comp_of_ae_ae (measurableSet_goodReward μ)
    apply Filter.Eventually.of_forall
    intro h
    unfold banditTrajKernel
    rw [Kernel.comap_apply]
    exact step_ae_goodReward μ hμ π (t+1) _

end OptimalBAI.ChernoffPAC


open MeasureTheory BanditAlgorithm Finset
namespace OptimalBAI.ChernoffPAC

lemma true_arm_lik_pos {K : ℕ} (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (ω : ℕ → Fin K × ℝ) (hgood : ∀ t, goodReward μ (ω t)) (a : Fin K) (t : ℕ) :
    0 < trajArmLik a t ω (μ a) := by
  classical
  by_cases ha0 : μ a=0
  · have hs : trajOnesCount a t ω=0 := by
      unfold trajOnesCount
      rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hia
      rcases hgood i with h1 | h0
      · have hm : μ (ω i).1=0 := hia.1 ▸ ha0
        linarith [h1.2]
      · have hn := h0.1
        linarith [hia.2]
    simp [trajArmLik,bernCountLik,ha0,hs]
  by_cases ha1 : μ a=1
  · have hs : trajOnesCount a t ω=trajPullCount a t ω := by
      unfold trajOnesCount trajPullCount
      congr 1
      ext i
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · intro h
        refine ⟨h.1,h.2,?_⟩
        rcases hgood i with h1 | h0
        · exact h1.1
        · have hm : μ (ω i).1=1 := h.2 ▸ ha1
          linarith [h0.2]
    simp [trajArmLik,bernCountLik,ha1,hs]
  have hp : 0 < μ a := lt_of_le_of_ne (hμ a).1 (Ne.symm ha0)
  have hq : 0 < 1-μ a := sub_pos.mpr (lt_of_le_of_ne (hμ a).2 ha1)
  unfold trajArmLik bernCountLik
  exact mul_pos (pow_pos hp _) (pow_pos hq _)

lemma empiricalMean_eq_count_ratio {K : ℕ} (μ : Fin K → ℝ)
    (ω : ℕ → Fin K × ℝ) (hgood : ∀ t, goodReward μ (ω t)) (a : Fin K) (t : ℕ) :
    trajEmpiricalMean a t ω = (trajOnesCount a t ω : ℝ)/trajPullCount a t ω := by
  classical
  unfold trajEmpiricalMean
  congr 1
  unfold trajOnesCount
  have he : (range t).filter (fun i => (ω i).1=a ∧ (ω i).2=1) =
      ((range t).filter fun i => (ω i).1=a).filter fun i => (ω i).2=1 := by
    ext i; simp [and_assoc]
  rw [he,Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Finset.sum_filter,Nat.cast_one]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hgood i with h1 | h0
  · simp [h1.1]
  · simp [h0.1]

lemma bernoulliBandit_mean {K : ℕ} (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) : banditArmMean (bernoulliBandit μ hμ) i = μ i := by
  rw [banditArmMean,bernoulli_integral]
  simp

lemma bernoulliBandit_best_mean {K : ℕ} (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin K) (hbest : ∀ i, μ i ≤ μ a) : banditOptimalMean (bernoulliBandit μ hμ) = μ a := by
  letI : Nonempty (Fin K) := ⟨a⟩
  unfold banditOptimalMean
  simp_rw [bernoulliBandit_mean]
  exact le_antisymm (ciSup_le hbest) (le_ciSup (Set.finite_range μ).bddAbove a)

end OptimalBAI.ChernoffPAC


open Finset
namespace OptimalBAI.ChernoffPAC

noncomputable def binMass (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ)*p^k*(1-p)^(n-k)

lemma binMass_nonneg (n k : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binMass n k p := by
  unfold binMass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

lemma sum_binMass (n : ℕ) (p : ℝ) : (∑ k ∈ range (n+1), binMass n k p) = 1 := by
  have h := add_pow p (1-p) n
  simp only [show p+(1-p)=1 by ring,one_pow] at h
  calc
    _ = ∑ k ∈ range (n+1), p^k*(1-p)^(n-k)*(n.choose k : ℝ) := by
      apply sum_congr rfl
      intro k hk
      simp only [binMass]
      ring
    _ = 1 := h.symm

lemma binMass_succ (n k : ℕ) {p : ℝ} (hk : k < n) :
    ((k : ℝ)+1)*(1-p)*binMass n (k+1) p = ((n : ℝ)-k)*p*binMass n k p := by
  have hchoose : (n.choose (k+1) : ℝ)*((k : ℝ)+1) =
      (n.choose k : ℝ)*((n : ℝ)-k) := by
    have h := Nat.choose_succ_right_eq n k
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hk.le] using congrArg (Nat.cast : ℕ → ℝ) h
  have he : n-k = n-(k+1)+1 := by omega
  unfold binMass
  rw [pow_succ,he,pow_succ]
  nlinarith [congrArg (fun x : ℝ => x * p^k * (1-p)^(n-(k+1)) * p * (1-p)) hchoose]

lemma binMass_increase {n s k : ℕ} (hs : s ≤ n) (hk : k < s)
    (hp : (s : ℝ) / n ∈ Set.Ioo (0 : ℝ) 1) :
    binMass n k ((s : ℝ)/n) ≤ binMass n (k+1) ((s : ℝ)/n) := by
  have hn : (0 : ℝ) < n := by
    by_contra h
    have hz : n=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg n))
    simp [hz] at hp
  have hrec := binMass_succ n k (p := (s : ℝ)/n) (lt_of_lt_of_le hk hs)
  have hmass := binMass_nonneg n k ⟨hp.1.le,hp.2.le⟩
  have hcoeff : ((k : ℝ)+1)*(1-(s : ℝ)/n) ≤ ((n : ℝ)-k)*((s : ℝ)/n) := by
    have hk' : (k : ℝ)+1 ≤ s := by exact_mod_cast hk
    have hs' : (s : ℝ) ≤ n := by exact_mod_cast hs
    apply (le_of_mul_le_mul_right ?_ hn)
    field_simp
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoeff hmass
  have hpos : 0 < ((k : ℝ)+1)*(1-(s : ℝ)/n) :=
    mul_pos (by positivity) (sub_pos.mpr hp.2)
  apply le_of_mul_le_mul_left ?_ hpos
  nlinarith [hrec,hprod]

lemma binMass_decrease {n s k : ℕ} (hs : s ≤ k) (hk : k < n)
    (hp : (s : ℝ)/n ∈ Set.Ioo (0 : ℝ) 1) :
    binMass n (k+1) ((s : ℝ)/n) ≤ binMass n k ((s : ℝ)/n) := by
  have hn : (0 : ℝ) < n := by
    by_contra h
    have hz : n=0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg n))
    simp [hz] at hp
  have hrec := binMass_succ n k (p := (s : ℝ)/n) hk
  have hmass := binMass_nonneg n k ⟨hp.1.le,hp.2.le⟩
  have hcoeff : ((n : ℝ)-k)*((s : ℝ)/n) ≤ ((k : ℝ)+1)*(1-(s : ℝ)/n) := by
    have hs' : (s : ℝ) ≤ k := by exact_mod_cast hs
    apply (le_of_mul_le_mul_right ?_ hn)
    field_simp
    nlinarith [mul_nonneg hn.le (sub_nonneg.mpr hs'), (div_lt_one hn).mp hp.2]
  have hprod := mul_le_mul_of_nonneg_right hcoeff hmass
  have hpos : 0 < ((k : ℝ)+1)*(1-(s : ℝ)/n) :=
    mul_pos (by positivity) (sub_pos.mpr hp.2)
  apply le_of_mul_le_mul_left ?_ hpos
  nlinarith [hrec,hprod]

lemma binMass_mode {n s : ℕ} (hs : s ≤ n)
    (hp : (s : ℝ)/n ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    binMass n k ((s : ℝ)/n) ≤ binMass n s ((s : ℝ)/n) := by
  by_cases hkn : n < k
  · simp only [binMass,Nat.choose_eq_zero_of_lt hkn,Nat.cast_zero,zero_mul]
    exact binMass_nonneg n s ⟨hp.1.le,hp.2.le⟩
  have hk : k ≤ n := le_of_not_gt hkn
  rcases le_total k s with hks | hsk
  · have hm : MonotoneOn (fun k => binMass n k ((s : ℝ)/n)) (Set.Icc 0 s) := by
      apply monotoneOn_of_le_succ Set.ordConnected_Icc
      intro j hjmax hj hjnext
      exact binMass_increase hs (Nat.lt_of_succ_le hjnext.2) hp
    exact hm ⟨Nat.zero_le _,hks⟩ ⟨Nat.zero_le _,le_rfl⟩ hks
  · have hm : AntitoneOn (fun k => binMass n k ((s : ℝ)/n)) (Set.Icc s n) := by
      apply antitoneOn_of_succ_le Set.ordConnected_Icc
      intro j hjmax hj hjnext
      exact binMass_decrease hj.1 (Nat.lt_of_succ_le hjnext.2) hp
    exact hm ⟨le_rfl,hs⟩ ⟨hsk,hk⟩ hsk

end OptimalBAI.ChernoffPAC


open Finset
namespace OptimalBAI.ChernoffPAC

lemma sum_binMass_le (n m : ℕ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∑ k ∈ range (m+1), binMass n k p) ≤ 1 := by
  rw [← sum_binMass n p]
  rcases le_total m n with hmn | hnm
  · apply sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    intro k hk hk'
    exact binMass_nonneg _ _ hp
  · apply le_of_eq
    symm
    apply sum_subset (range_mono (by omega))
    intro k hk hk'
    have hnk : n < k := by simp only [Finset.mem_range] at hk hk'; omega
    simp [binMass,Nat.choose_eq_zero_of_lt hnk]

lemma binMass_convolution (n s : ℕ) (hs : s ≤ n) (p : ℝ) :
    binMass (2*n) (2*s) p =
      ∑ k ∈ range (2*s+1), binMass n k p * binMass n (2*s-k) p := by
  have hv : ((2*n).choose (2*s) : ℝ) =
      ∑ k ∈ range (2*s+1), (n.choose k : ℝ)*(n.choose (2*s-k) : ℝ) := by
    have h := Nat.add_choose_eq n n (2*s)
    rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i * n.choose j)] at h
    simpa only [← two_mul,Nat.cast_sum,Nat.cast_mul] using congrArg (Nat.cast : ℕ → ℝ) h
  unfold binMass
  rw [hv,sum_mul,sum_mul]
  apply sum_congr rfl
  intro k hk
  have hk' : k ≤ 2*s := by simp only [Finset.mem_range] at hk; omega
  by_cases hkn : k ≤ n
  · by_cases hjn : 2*s-k ≤ n
    · have hsuc : k+(2*s-k)=2*s := by omega
      have hfuc : (n-k)+(n-(2*s-k))=2*n-2*s := by omega
      calc
        _ = (n.choose k : ℝ)*(n.choose (2*s-k) : ℝ)*p^(k+(2*s-k))*(1-p)^((n-k)+(n-(2*s-k))) := by rw [hsuc,hfuc]
        _ = _ := by rw [pow_add,pow_add]; ring
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hjn)]
  · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hkn)]

lemma binMass_doubled_le_mode {n s : ℕ} (hs : s ≤ n)
    (hp : (s : ℝ)/n ∈ Set.Ioo (0 : ℝ) 1) :
    binMass (2*n) (2*s) ((s : ℝ)/n) ≤ binMass n s ((s : ℝ)/n) := by
  rw [binMass_convolution n s hs]
  calc
    _ ≤ ∑ k ∈ range (2*s+1), binMass n k ((s : ℝ)/n)*binMass n s ((s : ℝ)/n) := by
      apply sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (binMass_mode hs hp (2*s-k))
        (binMass_nonneg _ _ ⟨hp.1.le,hp.2.le⟩)
    _ = (∑ k ∈ range (2*s+1), binMass n k ((s : ℝ)/n))*binMass n s ((s : ℝ)/n) := (sum_mul ..).symm
    _ ≤ 1*binMass n s ((s : ℝ)/n) :=
      mul_le_mul_of_nonneg_right (sum_binMass_le n (2*s) ⟨hp.1.le,hp.2.le⟩)
        (binMass_nonneg _ _ ⟨hp.1.le,hp.2.le⟩)
    _ = _ := one_mul _

end OptimalBAI.ChernoffPAC


namespace OptimalBAI.ChernoffPAC

lemma likelihood_le_empirical {s f : ℕ} (hs : 0 < s) (hf : 0 < f)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    u^s*(1-u)^f ≤ ((s : ℝ)/(s+f))^s*((f : ℝ)/(s+f))^f := by
  let a : ℝ := (s : ℝ)/(s+f)
  let b : ℝ := (f : ℝ)/(s+f)
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hn : (0 : ℝ) < s+f := by positivity
  have ha : 0 < a := div_pos hs' hn
  have hb : 0 < b := div_pos hf' hn
  have hab : a+b=1 := by dsimp [a,b]; field_simp
  have ham := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
    (div_nonneg hu.1 ha.le) (div_nonneg (sub_nonneg.mpr hu.2) hb.le) hab
  have hsimp : a*(u/a)+b*((1-u)/b)=1 := by field_simp; ring
  rw [hsimp] at ham
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (div_nonneg hu.1 ha.le) _)
    (Real.rpow_nonneg (div_nonneg (sub_nonneg.mpr hu.2) hb.le) _)) ham (s+f)
  rw [one_pow,mul_pow,← Real.rpow_natCast,← Real.rpow_mul (div_nonneg hu.1 ha.le),
    ← Real.rpow_natCast,← Real.rpow_mul (div_nonneg (sub_nonneg.mpr hu.2) hb.le)] at hp
  have hea : a*((s+f : ℕ) : ℝ) = s := by dsimp [a]; push_cast; field_simp
  have heb : b*((s+f : ℕ) : ℝ) = f := by dsimp [b]; push_cast; field_simp
  rw [hea,heb,Real.rpow_natCast,Real.rpow_natCast] at hp
  have hpos : 0 < a^s*b^f := by positivity
  have he : (u/a)^s*((1-u)/b)^f = (u^s*(1-u)^f)/(a^s*b^f) := by
    simp only [div_pow]
    ring
  rw [he] at hp
  have hresult := (div_le_one hpos).mp hp
  exact hresult

end OptimalBAI.ChernoffPAC


namespace OptimalBAI.ChernoffPAC

lemma count_likelihood_choose {s f : ℕ} (hs : 0 < s) (hf : 0 < f)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (u^s*(1-u)^f)*((2*(s+f)).choose (2*s) : ℝ) ≤ ((s+f).choose s : ℝ) := by
  let n := s+f
  let p : ℝ := (s : ℝ)/n
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hp : p ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hs' hn
    · apply (div_lt_one hn).mpr
      dsimp [n]
      push_cast
      linarith
  have hconv := binMass_doubled_le_mode (by dsimp [n]; omega : s ≤ n) hp
  have he : 1-p = (f : ℝ)/(s+f) := by dsimp [p,n]; push_cast; field_simp; ring
  have hL : 0 < p^s*(1-p)^f := mul_pos (pow_pos hp.1 _) (pow_pos (sub_pos.mpr hp.2) _)
  have hnp : n-s=f := by dsimp [n]; omega
  have h2np : 2*n-2*s=2*f := by dsimp [n]; omega
  unfold binMass at hconv
  rw [hnp,h2np,show 2*s=s+s by omega,show 2*f=f+f by omega,pow_add,pow_add] at hconv
  rw [← two_mul s] at hconv
  change ((2*n).choose (2*s) : ℝ)*(p^s*p^s)*((1-p)^f*(1-p)^f) ≤ (n.choose s : ℝ)*p^s*(1-p)^f at hconv
  have hmode : (p^s*(1-p)^f)*((2*n).choose (2*s) : ℝ) ≤ (n.choose s : ℝ) := by
    apply le_of_mul_le_mul_left ?_ hL
    nlinarith [hconv]
  have hmax := likelihood_le_empirical hs hf hu
  have hpn : (s : ℝ)/(s+f)=p := by dsimp [p,n]; push_cast; rfl
  rw [hpn,← he] at hmax
  exact (mul_le_mul_of_nonneg_right hmax (Nat.cast_nonneg _)).trans hmode

lemma count_likelihood_times_endMass {s f : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    endMass (s+f)*(u^s*(1-u)^f) ≤ ktCount s f := by
  by_cases hs : s=0
  · subst s
    simp only [zero_add,pow_zero,one_mul,ktCount_zero_left]
    exact mul_le_of_le_one_right (endMass_pos f).le
      (pow_le_one₀ (sub_nonneg.mpr hu.2) (by linarith [hu.1]))
  by_cases hf : f=0
  · subst f
    simp only [add_zero,pow_zero,mul_one,ktCount_zero_right]
    exact mul_le_of_le_one_right (endMass_pos s).le (pow_le_one₀ hu.1 hu.2)
  have h := count_likelihood_choose (Nat.pos_of_ne_zero hs) (Nat.pos_of_ne_zero hf) hu
  have hkt := ktCount_choose s f
  have hpos : (0 : ℝ) < ((2*(s+f)).choose (2*s) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2*s ≤ 2*(s+f))
  apply le_of_mul_le_mul_right ?_ hpos
  have hmul := mul_le_mul_of_nonneg_left h (endMass_pos (s+f)).le
  nlinarith [hmul,hkt]

lemma bernSeqLik_bound {n : ℕ} (hn : 1 ≤ n) (x : Fin n → Bool) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : bernSeqLik u x ≤ 2*Real.sqrt n*ktProb x := by
  have h := count_likelihood_times_endMass (s := onesCount x) (f := n-onesCount x) hu
  have he : onesCount x+(n-onesCount x)=n := Nat.add_sub_of_le (onesCount_le x)
  rw [he,← bernSeqLik_eq_powers,← ktProb_eq_count] at h
  have hlower := endMass_lower hn
  have hlik := bernSeqLik_nonneg x hu
  have hmul := mul_le_mul_of_nonneg_right hlower hlik
  have hmul' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*Real.sqrt n)
  nlinarith [hmul,hmul']

end OptimalBAI.ChernoffPAC



open MeasureTheory BanditAlgorithm
namespace OptimalBAI.ChernoffPAC

noncomputable def regretFactor (n : ℕ) : ℝ := if n=0 then 1 else 2*Real.sqrt n

lemma regretFactor_nonneg (n : ℕ) : 0 ≤ regretFactor n := by
  unfold regretFactor
  split_ifs <;> positivity

lemma count_lik_bound {n s : ℕ} (hs : s ≤ n) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    bernCountLik n s u ≤ regretFactor n * ktCount s (n-s) := by
  by_cases hn : n=0
  · subst n
    have he : s=0 := by omega
    subst s
    norm_num [bernCountLik,regretFactor,ktCount_zero_left,endMass,Nat.centralBinom]
  have he : s+(n-s)=n := Nat.add_sub_of_le hs
  have h := count_likelihood_times_endMass (s := s) (f := n-s) hu
  rw [he] at h
  have hB := endMass_lower (by omega : 1 ≤ n)
  have hlik : 0 ≤ u^s*(1-u)^(n-s) :=
    mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg (sub_nonneg.mpr hu.2) _)
  have hmul := mul_le_mul_of_nonneg_right hB hlik
  have hmul' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*Real.sqrt n)
  simp only [regretFactor,if_neg hn,bernCountLik]
  nlinarith [hmul,hmul']

lemma regretFactor_pair {n m t : ℕ} (ht : 1 ≤ t) (hnm : n+m ≤ t) :
    regretFactor n*regretFactor m ≤ 2*(t : ℝ) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnm' : (n : ℝ)+m ≤ t := by exact_mod_cast hnm
  have hsn := Real.sq_sqrt hn'
  have hsm := Real.sq_sqrt hm'
  have hnS := Real.sqrt_nonneg (n : ℝ)
  have hmS := Real.sqrt_nonneg (m : ℝ)
  by_cases hn : n=0
  · subst n
    by_cases hm : m=0
    · subst m
      norm_num [regretFactor]
      linarith
    · simp only [regretFactor,eq_self,ite_true,if_neg hm,one_mul]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
      have hS : Real.sqrt m ≤ m := by nlinarith [sq_nonneg (Real.sqrt m-1)]
      linarith
  · by_cases hm : m=0
    · subst m
      simp only [regretFactor,eq_self,ite_true,if_neg hn,mul_one]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hS : Real.sqrt n ≤ n := by nlinarith [sq_nonneg (Real.sqrt n-1)]
      linarith
    · simp only [regretFactor,if_neg hn,if_neg hm]
      nlinarith [sq_nonneg (Real.sqrt n-Real.sqrt m)]

noncomputable def pairKT {K : ℕ} (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℝ :=
  ktCount (trajOnesCount a t ω) (trajPullCount a t ω-trajOnesCount a t ω)*
    ktCount (trajOnesCount b t ω) (trajPullCount b t ω-trajOnesCount b t ω)

lemma trajArmLik_nonneg {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ trajArmLik a t ω u := by
  unfold trajArmLik bernCountLik
  exact mul_nonneg (pow_nonneg hu.1 _) (pow_nonneg (sub_nonneg.mpr hu.2) _)

lemma trajArmLik_half_pos {K : ℕ} (a : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) :
    0 < trajArmLik a t ω (1/2) := by
  unfold trajArmLik bernCountLik
  positivity

lemma trajPairLik_bound {K : ℕ} (a b : Fin K) (hab : a ≠ b) {t : ℕ} (ht : 1 ≤ t)
    (ω : ℕ → Fin K × ℝ) {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    trajArmLik a t ω u*trajArmLik b t ω v ≤ 2*(t : ℝ)*pairKT a b t ω := by
  have ha := count_lik_bound (ones_count_le a t ω) hu
  have hb := count_lik_bound (ones_count_le b t ω) hv
  have hpair := mul_le_mul ha hb (trajArmLik_nonneg b t ω hv)
    (mul_nonneg (regretFactor_nonneg _) (ktCount_pos _ _).le)
  have hfac := regretFactor_pair ht (pair_pulls_le a b hab t ω)
  have hKT : 0 ≤ pairKT a b t ω := mul_nonneg (ktCount_pos _ _).le (ktCount_pos _ _).le
  have hmul := mul_le_mul_of_nonneg_right hfac hKT
  unfold pairKT trajArmLik at *
  nlinarith [hpair,hmul]

end OptimalBAI.ChernoffPAC



open MeasureTheory BanditAlgorithm Set
namespace OptimalBAI.ChernoffPAC

noncomputable def glrNum {K : ℕ} (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => trajArmLik a t ω p.1*trajArmLik b t ω p.2) ''
    {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.2 ≤ p.1})

noncomputable def glrDen {K : ℕ} (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => trajArmLik a t ω p.1*trajArmLik b t ω p.2) ''
    {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2})

lemma pairKT_pos {K : ℕ} (a b : Fin K) (t : ℕ) (ω : ℕ → Fin K × ℝ) : 0 < pairKT a b t ω :=
  mul_pos (ktCount_pos _ _) (ktCount_pos _ _)

lemma glr_sup_bounds {K : ℕ} (a b : Fin K) (hab : a ≠ b) {t : ℕ} (ht : 1 ≤ t)
    (ω : ℕ → Fin K × ℝ) :
    (0 < glrNum a b t ω ∧ glrNum a b t ω ≤ 2*(t : ℝ)*pairKT a b t ω) ∧
    (0 < glrDen a b t ω ∧ ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      u ≤ v → trajArmLik a t ω u*trajArmLik b t ω v ≤ glrDen a b t ω) := by
  let F : ℝ × ℝ → ℝ := fun p => trajArmLik a t ω p.1*trajArmLik b t ω p.2
  let A : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.2 ≤ p.1}
  let B : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.1 ≤ p.2}
  have hA : F '' A |>.Nonempty := ⟨F (1/2,1/2),(1/2,1/2),by norm_num [A],rfl⟩
  have hB : F '' B |>.Nonempty := ⟨F (1/2,1/2),(1/2,1/2),by norm_num [B],rfl⟩
  have hbA : BddAbove (F '' A) := by
    refine ⟨2*(t : ℝ)*pairKT a b t ω,?_⟩
    rintro y ⟨p,hp,rfl⟩
    exact trajPairLik_bound a b hab ht ω hp.1 hp.2.1
  have hbB : BddAbove (F '' B) := by
    refine ⟨2*(t : ℝ)*pairKT a b t ω,?_⟩
    rintro y ⟨p,hp,rfl⟩
    exact trajPairLik_bound a b hab ht ω hp.1 hp.2.1
  have hh : 0 < F (1/2,1/2) := mul_pos (trajArmLik_half_pos _ _ _) (trajArmLik_half_pos _ _ _)
  refine ⟨⟨hh.trans_le (le_csSup hbA ⟨_,by norm_num [A],rfl⟩),?_⟩,
    ⟨hh.trans_le (le_csSup hbB ⟨_,by norm_num [B],rfl⟩),?_⟩⟩
  · apply csSup_le hA
    rintro y ⟨p,hp,rfl⟩
    exact trajPairLik_bound a b hab ht ω hp.1 hp.2.1
  · intro u hu v hv huv
    exact le_csSup hbB ⟨(u,v),⟨hu,hv,huv⟩,rfl⟩

noncomputable def trajectoryPairRatio {K : ℕ} (a b : Fin K) (μ : Fin K → ℝ)
    (t : ℕ) (ω : ℕ → Fin K × ℝ) : ℝ := historyPairRatio a b μ (banditTrajPrefix K t ω)

lemma trajectoryPairRatio_eq {K : ℕ} (a b : Fin K) (μ : Fin K → ℝ)
    (t : ℕ) (ω : ℕ → Fin K × ℝ) : trajectoryPairRatio a b μ t ω =
      pairKT a b t ω/(trajArmLik a t ω (μ a)*trajArmLik b t ω (μ b)) := by
  unfold trajectoryPairRatio historyPairRatio historyRatio
  rw [historyPulls_prefix,historyPulls_prefix,historyOnes_prefix,historyOnes_prefix]
  unfold pairKT trajArmLik bernCountLik
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma glr_ratio_bound {K : ℕ} (a b : Fin K) (hab : a ≠ b) (μ : Fin K → ℝ)
    (hμ : ∀ i, μ i ∈ Icc (0 : ℝ) 1) (horder : μ a ≤ μ b) {t : ℕ} (ht : 1 ≤ t)
    (ω : ℕ → Fin K × ℝ)
    (htrue : 0 < trajArmLik a t ω (μ a)*trajArmLik b t ω (μ b)) :
    glrNum a b t ω/glrDen a b t ω ≤ 2*(t : ℝ)*trajectoryPairRatio a b μ t ω := by
  have hb := glr_sup_bounds a b hab ht ω
  have hD := hb.2.2 (μ a) (hμ a) (μ b) (hμ b) horder
  have hB : 0 ≤ 2*(t : ℝ)*pairKT a b t ω := by
    exact mul_nonneg (by positivity) (pairKT_pos _ _ _ _).le
  rw [trajectoryPairRatio_eq]
  calc
    _ ≤ (2*(t : ℝ)*pairKT a b t ω)/glrDen a b t ω :=
      div_le_div_of_nonneg_right hb.1.2 hb.2.1.le
    _ ≤ (2*(t : ℝ)*pairKT a b t ω)/(trajArmLik a t ω (μ a)*trajArmLik b t ω (μ b)) :=
      div_le_div_of_nonneg_left hB htrue hD
    _ = _ := by ring

lemma card_gt_one_of_ne {K : ℕ} (a b : Fin K) (hab : a ≠ b) : 1 < K := by
  by_contra hK
  have ha := a.isLt
  have hb := b.isLt
  have he : a.val=b.val := by omega
  exact hab (Fin.ext he)

lemma informationalThreshold_pos {K : ℕ} (hK : 1 < K) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    {t : ℕ} (ht : 1 ≤ t) : 0 < informationalThreshold K δ t := by
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
  have hKm : (1 : ℝ) ≤ (K : ℝ)-1 := by linarith
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  unfold informationalThreshold
  apply Real.log_pos
  apply (one_lt_div hδ.1).mpr
  have hm := mul_le_mul_of_nonneg_left hKm (by positivity : 0 ≤ 2*(t : ℝ))
  nlinarith [hm,hδ.2]

lemma glr_crossing_ratio {K : ℕ} (a b : Fin K) (μ : Fin K → ℝ)
    (hμ : ∀ i, μ i ∈ Icc (0 : ℝ) 1) (hab : μ a < μ b) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    {t : ℕ} (ht : 1 ≤ t) (ω : ℕ → Fin K × ℝ)
    (htrue : 0 < trajArmLik a t ω (μ a)*trajArmLik b t ω (μ b))
    (hc : informationalThreshold K δ t < glrStat a b t ω) :
    ((K : ℝ)-1)/δ < trajectoryPairRatio a b μ t ω := by
  have hab' : a ≠ b := fun h => by subst b; exact lt_irrefl _ hab
  have hK := card_gt_one_of_ne a b hab'
  have hKreal : (1 : ℝ) < K := by exact_mod_cast hK
  have hKm : (0 : ℝ) < (K : ℝ)-1 := by linarith
  have ht' : 0 < (t : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one ht
  have hb := glr_sup_bounds a b hab' ht ω
  have harg : 0 < 2*(t : ℝ)*((K : ℝ)-1)/δ :=
    div_pos (mul_pos (mul_pos (by norm_num) ht') hKm) hδ.1
  change Real.log (2*(t : ℝ)*((K : ℝ)-1)/δ) < Real.log (glrNum a b t ω/glrDen a b t ω) at hc
  have hc' := (Real.log_lt_log_iff harg (div_pos hb.1.1 hb.2.1)).mp hc
  have hbound := glr_ratio_bound a b hab' μ hμ hab.le ht ω htrue
  apply lt_of_mul_lt_mul_left ?_ (by positivity : 0 ≤ 2*(t : ℝ))
  calc
    _ = 2*(t : ℝ)*((K : ℝ)-1)/δ := by ring
    _ < _ := hc'.trans_le hbound

end OptimalBAI.ChernoffPAC



open MeasureTheory ProbabilityTheory BanditAlgorithm Preorder
namespace OptimalBAI.ChernoffPAC

theorem pairwise_crossing_proved {K : ℕ} (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (π : BanditPolicy K) (μ : Fin K → ℝ) (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    (a b : Fin K) (hab : μ a < μ b) :
    banditTrajMeasure (bernoulliBandit μ hμ) π
        {ω | ∃ t : ℕ, 1 ≤ t ∧ informationalThreshold K δ t < glrStat a b t ω} ≤
      ENNReal.ofReal (δ / ((K : ℝ) - 1)) := by
  have hab' : a ≠ b := fun h => by subst b; exact lt_irrefl _ hab
  have hK : (1 : ℝ) < K := by exact_mod_cast card_gt_one_of_ne a b hab'
  have hKm : 0 < (K : ℝ)-1 := by linarith
  let M : ℕ → (ℕ → Fin K × ℝ) → ℝ := fun t ω =>
    historyPairRatio a b μ (banditIicHistory K t (frestrictLe t ω))
  have hM := pairRatio_supermartingale a b hab' μ hμ π
  have hpos : ∀ t ω, 0 ≤ M t ω := fun t ω =>
    mul_nonneg (historyRatio_nonneg a (hμ a) _) (historyRatio_nonneg b (hμ b) _)
  have hinit := pairRatio_initial_expect_le a b hab' μ hμ π
  have hVille := ville hM hpos hinit (div_pos hKm hδ.1)
  have hsub : ∀ᵐ ω ∂banditTrajMeasure (bernoulliBandit μ hμ) π,
      (∃ t : ℕ, 1 ≤ t ∧ informationalThreshold K δ t < glrStat a b t ω) →
      ∃ t, ((K : ℝ)-1)/δ ≤ M t ω := by
    filter_upwards [trajectory_ae_goodRewards μ hμ π] with ω hgood
    rintro ⟨t,ht,hc⟩
    have htrue := mul_pos (true_arm_lik_pos μ hμ ω hgood a t)
      (true_arm_lik_pos μ hμ ω hgood b t)
    have hr := glr_crossing_ratio a b μ hμ hab hδ ht ω htrue hc
    refine ⟨t-1,?_⟩
    change ((K : ℝ)-1)/δ ≤ historyPairRatio a b μ
      (banditIicHistory K (t-1) (frestrictLe (t-1) ω))
    rw [iicHistory_prefix,Nat.sub_add_cancel ht]
    exact hr.le
  have he : (1 : ℝ) / (((K : ℝ)-1)/δ) = δ/((K : ℝ)-1) := by
    field_simp
  rw [he] at hVille
  exact (measure_mono_ae hsub).trans hVille

end OptimalBAI.ChernoffPAC



open MeasureTheory BanditAlgorithm Set
namespace OptimalBAI.ChernoffPAC

lemma count_ratio_mem {n s : ℕ} (hs : s ≤ n) :
    (s : ℝ)/(n : ℝ) ∈ Icc (0 : ℝ) 1 := by
  by_cases hn : n=0
  · simp [hn]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact ⟨by positivity,(div_le_one hn').mpr (by exact_mod_cast hs)⟩

lemma count_lik_mle {n s : ℕ} (hsn : s ≤ n) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    bernCountLik n s u ≤ bernCountLik n s ((s : ℝ)/(n : ℝ)) := by
  by_cases hn : n=0
  · have hs : s=0 := by omega
    simp [hn,hs,bernCountLik]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  by_cases hs : s=0
  · subst s
    simp only [bernCountLik,Nat.cast_zero,zero_div,pow_zero,sub_zero,one_pow,one_mul,
      Nat.sub_zero]
    exact pow_le_one₀ (sub_nonneg.mpr hu.2) (by linarith [hu.1])
  by_cases hf : n-s=0
  · have he : s=n := by omega
    subst s
    simp only [bernCountLik,Nat.sub_self,pow_zero,mul_one,div_self hn',one_pow]
    exact pow_le_one₀ hu.1 hu.2
  have h := likelihood_le_empirical (Nat.pos_of_ne_zero hs) (Nat.pos_of_ne_zero hf) hu
  have hsum : (s : ℝ)+((n-s : ℕ) : ℝ) = n := by exact_mod_cast Nat.add_sub_of_le hsn
  have hcomp : ((n-s : ℕ) : ℝ)/(n : ℝ) = 1-(s : ℝ)/(n : ℝ) := by
    rw [Nat.cast_sub hsn]
    field_simp
  rw [hsum,hcomp] at h
  exact h

lemma glr_nonpos_of_count_order {K : ℕ} (a b : Fin K) (hab : a ≠ b)
    {t : ℕ} (ht : 1 ≤ t) (ω : ℕ → Fin K × ℝ)
    (horder : (trajOnesCount a t ω : ℝ)/trajPullCount a t ω ≤
      (trajOnesCount b t ω : ℝ)/trajPullCount b t ω) : glrStat a b t ω ≤ 0 := by
  let ua : ℝ := (trajOnesCount a t ω : ℝ)/trajPullCount a t ω
  let ub : ℝ := (trajOnesCount b t ω : ℝ)/trajPullCount b t ω
  have hua := count_ratio_mem (ones_count_le a t ω)
  have hub := count_ratio_mem (ones_count_le b t ω)
  have hmax : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      trajArmLik a t ω u*trajArmLik b t ω v ≤ trajArmLik a t ω ua*trajArmLik b t ω ub := by
    intro u hu v hv
    exact mul_le_mul (count_lik_mle (ones_count_le a t ω) hu)
      (count_lik_mle (ones_count_le b t ω) hv)
      (trajArmLik_nonneg b t ω hv) (trajArmLik_nonneg a t ω hua)
  have hnum : glrNum a b t ω ≤ trajArmLik a t ω ua*trajArmLik b t ω ub := by
    unfold glrNum
    apply csSup_le
    · exact ⟨_,(1/2,1/2),by norm_num,rfl⟩
    · rintro y ⟨p,hp,rfl⟩
      exact hmax p.1 hp.1 p.2 hp.2.1
  have hb := glr_sup_bounds a b hab ht ω
  have hden := hb.2.2 ua hua ub hub horder
  change Real.log (glrNum a b t ω/glrDen a b t ω) ≤ 0
  exact Real.log_nonpos (div_nonneg hb.1.1.le hb.2.1.le)
    ((div_le_one hb.2.1).mpr (hnum.trans hden))

lemma chernoffStop_mem {K : ℕ} (β : ℕ → ℝ) (ω : ℕ → Fin K × ℝ)
    (hstop : chernoffStop β ω < ⊤) :
    ∃ n : ℕ, chernoffStop β ω = n ∧ 1 ≤ n ∧
      ∃ a : Fin K, ∀ b : Fin K, b ≠ a → β n < glrStat a b n ω := by
  let S : Set ℕ∞ := {t | ∃ n : ℕ, (n : ℕ∞)=t ∧ 1 ≤ n ∧
    ∃ a : Fin K, ∀ b : Fin K, b ≠ a → β n < glrStat a b n ω}
  have hS : S.Nonempty := by
    by_contra h
    have he : S=∅ := Set.not_nonempty_iff_eq_empty.mp h
    change sInf S < ⊤ at hstop
    simpa [he] using hstop
  obtain ⟨n,hn,hn1,a,ha⟩ := csInf_mem hS
  exact ⟨n,hn.symm,hn1,a,ha⟩

end OptimalBAI.ChernoffPAC



open MeasureTheory BanditAlgorithm Set
namespace OptimalBAI.ChernoffPAC

theorem chernoff_pac_proved {K : ℕ} [NeZero K] (δ : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (π : BanditPolicy K)
    (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hψ : ∀ (ω : ℕ → Fin K × ℝ) (n : ℕ),
      chernoffStop (informationalThreshold K δ) ω = n →
        ∀ b : Fin K, trajEmpiricalMean b n ω ≤ trajEmpiricalMean (ψ ω) n ω) :
    IsSoundBAI δ π (chernoffStop (informationalThreshold K δ)) ψ (bernoulliClass K) := by
  classical
  rintro ν ⟨m,rfl⟩
  rcases m with ⟨μ,hμ,hS⟩
  obtain ⟨best,hbest⟩ := hS
  have hbest' : ∀ i, μ i ≤ μ best := by
    intro i
    by_cases hi : i=best
    · simp [hi]
    · exact (hbest i hi).le
  have hgap : ∀ i, banditGap (bernoulliBandit μ hμ) i = μ best-μ i := by
    intro i
    rw [banditGap,bernoulliBandit_best_mean μ hμ best hbest',bernoulliBandit_mean]
  by_cases hK : 1 < K
  · let I : Finset (Fin K) := Finset.univ.erase best
    let E : Fin K → Set (ℕ → Fin K × ℝ) := fun a =>
      {ω | ∃ t : ℕ, 1 ≤ t ∧ informationalThreshold K δ t < glrStat a best t ω}
    have hsub : ∀ᵐ ω ∂banditTrajMeasure (bernoulliBandit μ hμ) π,
        (chernoffStop (informationalThreshold K δ) ω < ⊤ ∧
          0 < banditGap (bernoulliBandit μ hμ) (ψ ω)) → ω ∈ ⋃ a ∈ I, E a := by
      filter_upwards [trajectory_ae_goodRewards μ hμ π] with ω hgood
      rintro ⟨hst,hwrong⟩
      have hne : ψ ω ≠ best := by
        intro he
        rw [he,hgap] at hwrong
        exact lt_irrefl 0 (by simpa using hwrong)
      obtain ⟨n,hn,hn1,a,ha⟩ := chernoffStop_mem _ ω hst
      have haψ : a=ψ ω := by
        by_contra hne'
        have hmean := hψ ω n hn a
        rw [empiricalMean_eq_count_ratio μ ω hgood a n,
          empiricalMean_eq_count_ratio μ ω hgood (ψ ω) n] at hmean
        have hnpos := informationalThreshold_pos hK hδ hn1
        have hle := glr_nonpos_of_count_order a (ψ ω) hne' hn1 ω hmean
        have hgt := ha (ψ ω) (Ne.symm hne')
        linarith
      subst a
      exact mem_iUnion.mpr ⟨ψ ω,mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hne,Finset.mem_univ _⟩,
        ⟨n,hn1,ha best (Ne.symm hne)⟩⟩⟩
    have hp : ∀ a ∈ I, banditTrajMeasure (bernoulliBandit μ hμ) π (E a) ≤
        ENNReal.ofReal (δ/((K : ℝ)-1)) := by
      intro a ha
      exact pairwise_crossing_proved δ hδ π μ hμ a best (hbest a (Finset.mem_erase.mp ha).1)
    have hcard : I.card=K-1 := by simp [I]
    have hKm : 0 < (K : ℝ)-1 := by
      have : (1 : ℝ) < K := by exact_mod_cast hK
      linarith
    have hsum : (∑ a ∈ I, ENNReal.ofReal (δ/((K : ℝ)-1))) = ENNReal.ofReal δ := by
      rw [Finset.sum_const,nsmul_eq_mul,hcard]
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      rw [Nat.cast_sub (by omega : 1 ≤ K)]
      field_simp
      norm_num
      ring
    exact (measure_mono_ae hsub).trans ((measure_biUnion_finset_le I E).trans
      ((Finset.sum_le_sum hp).trans_eq hsum))
  · have he : ∀ i : Fin K, i=best := by
      intro i
      apply Fin.ext
      have hi := i.isLt
      have hb := best.isLt
      omega
    have hsub : {ω | chernoffStop (informationalThreshold K δ) ω < ⊤ ∧
        0 < banditGap (bernoulliBandit μ hμ) (ψ ω)} ⊆ ∅ := by
      intro ω hω
      have hh := hω.2
      rw [he (ψ ω),hgap] at hh
      exact False.elim (lt_irrefl 0 (by simpa using hh))
    exact (measure_mono hsub).trans (by simp)

end OptimalBAI.ChernoffPAC

open OptimalBAI.ChernoffPAC
theorem solution {K : ℕ} [NeZero K] (δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (π : BanditPolicy K)
    (ψ : (ℕ → Fin K × ℝ) → Fin K)
    (hψ : ∀ (ω : ℕ → Fin K × ℝ) (n : ℕ),
      chernoffStop (informationalThreshold K δ) ω = n →
        ∀ b : Fin K, trajEmpiricalMean b n ω ≤ trajEmpiricalMean (ψ ω) n ω) :
    IsSoundBAI δ π (chernoffStop (informationalThreshold K δ)) ψ (bernoulliClass K) := by
  exact chernoff_pac_proved δ hδ π ψ hψ

#print axioms solution
