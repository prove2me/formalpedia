-- Prove2me | solution 1 for OptimalBAI.ChernoffPAC.kt_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T12:07:07.870046+00:00
-- url     : https://prove2.me/submissions/e71e7078-231d-45d0-a3dc-78ccb7f19820

/-
Released under Apache 2.0 license.
Written by Codex.
-/
import Mathlib
import Definitions.Def_OptimalBAI_ChernoffPAC_KrichevskyTrofimov



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

open OptimalBAI.ChernoffPAC
theorem solution (n : ℕ) :
    (∀ x : Fin n → Bool, 0 ≤ ktProb x) ∧
    (∑ x : Fin n → Bool, ktProb x) = 1 ∧
    (1 ≤ n → ∀ x : Fin n → Bool, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      bernSeqLik u x ≤ 2 * Real.sqrt n * ktProb x) := by
  refine ⟨fun x => ktProb_nonneg x, sum_ktProb n, ?_⟩
  intro hn x u hu
  exact bernSeqLik_bound hn x hu

#print axioms solution
