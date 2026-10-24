-- Prove2me | solution 1 for OnlineStochMatching.TSM.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T03:51:08.673041+00:00
-- url     : https://prove2.me/submissions/0c13cb09-b722-43aa-8381-b4e10ac68dc4

import Definitions.Def_OnlineStochMatching_TSM_Model
import Definitions.Def_OnlineStochMatching_TSM_Coloring
import Definitions.Def_OnlineStochMatching_TSM_Algorithm
import Definitions.Def_OnlineStochMatching_TSM_Cut
set_option autoImplicit false


set_option autoImplicit false

open scoped BigOperators
open Finset

namespace TSMProof

noncomputable def avg {I : Type} [Fintype I] (n : ℕ) (f : (Fin n → I) → ℝ) : ℝ :=
  (∑ ω, f ω) / (Fintype.card I : ℝ) ^ n

noncomputable def mean {J : Type} [Fintype J] (f : J → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card J

lemma avg_eq_mean {I : Type} [Fintype I] (n : ℕ) (f : (Fin n → I) → ℝ) :
    avg n f = mean f := by
  simp [avg, mean]

lemma mean_const {J : Type} [Fintype J] [Nonempty J] (c : ℝ) :
    mean (fun _ : J => c) = c := by
  have h : (Fintype.card J : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, h]

lemma mean_add {J : Type} [Fintype J] (f g : J → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

lemma mean_sub {J : Type} [Fintype J] (f g : J → ℝ) :
    mean (fun x => f x - g x) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

lemma mean_mul {J : Type} [Fintype J] (c : ℝ) (f : J → ℝ) :
    mean (fun x => c * f x) = c * mean f := by
  simp [mean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_mono {J : Type} [Fintype J] {f g : J → ℝ} (h : ∀ x, f x ≤ g x) :
    mean f ≤ mean g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun x _ => h x

lemma mean_nonneg {J : Type} [Fintype J] {f : J → ℝ} (h : ∀ x, 0 ≤ f x) :
    0 ≤ mean f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => h x) (Nat.cast_nonneg _)

lemma mean_center {J : Type} [Fintype J] [Nonempty J] (f : J → ℝ) :
    mean (fun x => f x - mean f) = 0 := by
  rw [mean_sub, mean_const, sub_self]

lemma mean_equiv {J K : Type} [Fintype J] [Fintype K] (e : J ≃ K) (f : K → ℝ) :
    mean (fun x => f (e x)) = mean f := by
  unfold mean
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma mean_prod {J K : Type} [Fintype J] [Fintype K] (f : J × K → ℝ) :
    mean f = mean (fun j => mean (fun k => f (j,k))) := by
  simp only [mean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  rw [← Finset.sum_div]
  ring

lemma avg_cons {I : Type} [Fintype I] (n : ℕ) (f : (Fin (n+1) → I) → ℝ) :
    avg (n+1) f = mean (fun i => avg n (fun ω => f (Fin.cons i ω))) := by
  simp only [avg_eq_mean]
  rw [← mean_equiv (Fin.consEquiv (fun _ : Fin (n+1) => I)) f, mean_prod]
  rfl

lemma avg_indicator {I : Type} [Fintype I] (n : ℕ) (P : (Fin n → I) → Prop) [DecidablePred P] :
    avg n (fun ω => if P ω then 1 else 0) = OnlineStochMatching.TSM.prob n P := by
  classical
  simp only [avg, OnlineStochMatching.TSM.prob]
  congr 1
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

lemma mean_uniform_integral {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] (f : J → ℝ) :
    (∫ x, f x ∂(PMF.uniformOfFintype J).toMeasure) = mean f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  simp [mean, div_eq_mul_inv, mul_comm]

lemma mean_exp_bound {J : Type} [Fintype J] [Nonempty J] (f : J → ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hb : ∀ j, |f j| ≤ L) (hz : mean f = 0) (t : ℝ) :
    mean (fun j => Real.exp (t * f j)) ≤ Real.exp (L ^ 2 * t ^ 2 / 2) := by
  let : MeasurableSpace J := ⊤
  let : MeasurableSingletonClass J := ⟨fun _ => trivial⟩
  have hm : Measurable f := measurable_of_finite f
  have hh := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := (PMF.uniformOfFintype J).toMeasure) hm.aemeasurable
    (Filter.Eventually.of_forall (fun j => (abs_le.mp (hb j))))
    (by rw [mean_uniform_integral]; exact hz)
  have ht := hh.mgf_le t
  rw [ProbabilityTheory.mgf, mean_uniform_integral] at ht
  have he : (L + L) / 2 = L := by ring
  simpa only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
    sub_neg_eq_add, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ L + L), he] using ht

lemma mean_center_bound {J : Type} [Fintype J] [Nonempty J] (f : J → ℝ)
    (L : ℝ) (h : ∀ i j, |f i - f j| ≤ L) (i : J) :
    |f i - mean f| ≤ L := by
  have hlo : mean (fun j => f i - L) ≤ mean f := mean_mono fun j => by
    have := (abs_le.mp (h i j)).2
    linarith
  have hhi : mean f ≤ mean (fun j => f i + L) := mean_mono fun j => by
    have := (abs_le.mp (h i j)).1
    linarith
  rw [mean_const] at hlo hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma abs_mean_le {J : Type} [Fintype J] [Nonempty J] (f : J → ℝ)
    (L : ℝ) (h : ∀ j, |f j| ≤ L) : |mean f| ≤ L := by
  have h₁ := mean_mono (fun j => (abs_le.mp (h j)).1)
  have h₂ := mean_mono (fun j => (abs_le.mp (h j)).2)
  rw [mean_const] at h₁ h₂
  exact abs_le.mpr ⟨h₁,h₂⟩

def Oscillation {I : Type} (n : ℕ) (f : (Fin n → I) → ℝ) (L : ℝ) : Prop :=
  ∀ ω j i, |f (Function.update ω j i) - f ω| ≤ L

lemma avg_zero {I : Type} [Fintype I] (f : (Fin 0 → I) → ℝ) :
    avg 0 f = f Fin.elim0 := by
  simp only [avg, pow_zero, div_one]
  rw [Fintype.sum_unique]
  congr 1

lemma mgf_bound {I : Type} [Fintype I] [Nonempty I] (n : ℕ)
    (f : (Fin n → I) → ℝ) (L : ℝ) (hL : 0 ≤ L) (hf : Oscillation n f L)
    (t : ℝ) :
    avg n (fun ω => Real.exp (t * (f ω - avg n f))) ≤
      Real.exp ((n : ℝ) * L ^ 2 * t ^ 2 / 2) := by
  classical
  induction n with
  | zero => simp [avg_zero]
  | succ n ih =>
    let g : I → ℝ := fun i => avg n (fun ω => f (Fin.cons i ω))
    have hg : ∀ i j, |g i - g j| ≤ L := by
      intro i j
      rw [show g i - g j = mean (fun ω => f (Fin.cons i ω) - f (Fin.cons j ω)) by
        simp [g, avg_eq_mean, mean_sub]]
      apply abs_mean_le
      intro ω
      simpa only [Fin.update_cons_zero] using hf (Fin.cons j ω) 0 i
    have hgi := mean_exp_bound (fun i => g i - mean g) L hL
      (mean_center_bound g L hg) (mean_center g) t
    have havg : avg (n+1) f = mean g := avg_cons n f
    rw [avg_cons]
    have hs : ∀ i, avg n (fun ω => Real.exp (t * (f (Fin.cons i ω) - avg (n+1) f))) ≤
        Real.exp (t * (g i - mean g)) * Real.exp ((n:ℝ)*L^2*t^2/2) := by
      intro i
      have hslice : Oscillation n (fun ω => f (Fin.cons i ω)) L := by
        intro ω j x
        have he : Function.update (Fin.cons i ω : Fin (n+1) → I) j.succ x = Fin.cons i (Function.update ω j x) := by
          funext z
          refine Fin.cases ?_ (fun z => ?_) z
          · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
            rfl
          · simp [Function.update_apply, Fin.succ_inj]
        simpa only [he] using hf (Fin.cons i ω) j.succ x
      have h := ih (fun ω => f (Fin.cons i ω)) hslice
      rw [havg]
      calc
        _ = Real.exp (t * (g i - mean g)) *
            avg n (fun ω => Real.exp (t * (f (Fin.cons i ω) - g i))) := by
          simp only [avg_eq_mean]
          rw [← mean_mul]
          congr 1
          funext ω
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    apply (mean_mono hs).trans
    rw [show (fun i => Real.exp (t * (g i - mean g)) * Real.exp ((n:ℝ)*L^2*t^2/2)) =
      (fun i => Real.exp ((n:ℝ)*L^2*t^2/2) * Real.exp (t * (g i - mean g))) by funext; ring]
    rw [mean_mul]
    calc
      _ ≤ Real.exp ((n:ℝ)*L^2*t^2/2) * Real.exp (L^2*t^2/2) :=
        mul_le_mul_of_nonneg_left hgi (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma chernoff_upper {I : Type} [Fintype I] [Nonempty I] (n : ℕ)
    (f : (Fin n → I) → ℝ) (L : ℝ) (hL : 0 ≤ L) (hf : Oscillation n f L)
    (a t : ℝ) (ht : 0 ≤ t) :
    OnlineStochMatching.TSM.prob n (fun ω => a ≤ f ω - avg n f) ≤
      Real.exp (-t*a + (n:ℝ)*L^2*t^2/2) := by
  classical
  rw [← avg_indicator]
  have hp : ∀ ω, (if a ≤ f ω - avg n f then (1:ℝ) else 0) ≤
      Real.exp (-t*a) * Real.exp (t*(f ω-avg n f)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp_iff.mpr
      nlinarith
    · exact (Real.exp_pos _).le
  have h := mean_mono hp
  simp only [← avg_eq_mean n] at h
  calc
    _ ≤ avg n (fun ω => Real.exp (-t*a) * Real.exp (t*(f ω-avg n f))) := h
    _ = Real.exp (-t*a) * avg n (fun ω => Real.exp (t*(f ω-avg n f))) := by
      simp only [avg_eq_mean, mean_mul]
    _ ≤ Real.exp (-t*a) * Real.exp ((n:ℝ)*L^2*t^2/2) :=
      mul_le_mul_of_nonneg_left (mgf_bound n f L hL hf t) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

lemma upper_tail {I : Type} [Fintype I] [Nonempty I] (n : ℕ) (hn : 0 < n)
    (f : (Fin n → I) → ℝ) (L : ℝ) (hL : 0 < L) (hf : Oscillation n f L)
    (a : ℝ) (ha : 0 ≤ a) :
    OnlineStochMatching.TSM.prob n (fun ω => a ≤ f ω - avg n f) ≤
      Real.exp (-a^2/(2*(n:ℝ)*L^2)) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)*L^2 := mul_pos hn' (sq_pos_of_pos hL)
  have h := chernoff_upper n f L hL.le hf a (a/((n:ℝ)*L^2)) (div_nonneg ha hd.le)
  convert h using 1
  congr 1
  field_simp
  ring

lemma lower_tail {I : Type} [Fintype I] [Nonempty I] (n : ℕ) (hn : 0 < n)
    (f : (Fin n → I) → ℝ) (L : ℝ) (hL : 0 < L) (hf : Oscillation n f L)
    (a : ℝ) (ha : 0 ≤ a) :
    OnlineStochMatching.TSM.prob n (fun ω => a ≤ avg n f - f ω) ≤
      Real.exp (-a^2/(2*(n:ℝ)*L^2)) := by
  have hh : Oscillation n (fun ω => -f ω) L := by
    intro ω j i
    simpa only [neg_sub_neg, abs_sub_comm] using hf ω j i
  have h := upper_tail n hn (fun ω => -f ω) L hL hh a ha
  have he : avg n (fun ω => -f ω) = -avg n f := by simp [avg, Finset.sum_neg_distrib, neg_div]
  simpa only [he, sub_neg_eq_add, neg_add_eq_sub] using h

lemma prob_mono {I : Type} [Fintype I] (n : ℕ) {P Q : (Fin n → I) → Prop}
    (h : ∀ ω, P ω → Q ω) :
    OnlineStochMatching.TSM.prob n P ≤ OnlineStochMatching.TSM.prob n Q := by
  classical
  rw [← avg_indicator, ← avg_indicator, avg_eq_mean, avg_eq_mean]
  apply mean_mono
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, if_false]
    split_ifs <;> norm_num

lemma prob_compl {I : Type} [Fintype I] [Nonempty I] (n : ℕ)
    (P : (Fin n → I) → Prop) :
    OnlineStochMatching.TSM.prob n (fun ω => ¬P ω) = 1 - OnlineStochMatching.TSM.prob n P := by
  classical
  rw [← avg_indicator, ← avg_indicator, avg_eq_mean, avg_eq_mean]
  have he : (fun ω => if ¬P ω then (1:ℝ) else 0) = (fun ω => 1-(if P ω then (1:ℝ) else 0)) := by
    funext ω
    split_ifs <;> simp_all
  rw [he, mean_sub, mean_const]

lemma prob_and_lower {I : Type} [Fintype I] [Nonempty I] (n : ℕ)
    (P Q : (Fin n → I) → Prop) :
    OnlineStochMatching.TSM.prob n P + OnlineStochMatching.TSM.prob n Q - 1 ≤
      OnlineStochMatching.TSM.prob n (fun ω => P ω ∧ Q ω) := by
  classical
  have h := mean_mono (J := Fin n → I) (f := fun ω => (if P ω then (1:ℝ) else 0) +
    (if Q ω then (1:ℝ) else 0)-1) (g := fun ω => if P ω ∧ Q ω then (1:ℝ) else 0)
    (by intro ω; split_ifs <;> simp_all)
  rw [mean_sub, mean_add, mean_const] at h
  simpa only [← avg_eq_mean n, avg_indicator] using h

lemma concentration_good {I : Type} [Fintype I] [Nonempty I] (n : ℕ) (hn : 0 < n)
    (f g : (Fin n → I) → ℝ) (hf : Oscillation n f 2) (hg : Oscillation n g 1)
    (a : ℝ) (ha : 0 ≤ a) :
    1-Real.exp (-a^2/(8*(n:ℝ)))-Real.exp (-a^2/(2*(n:ℝ))) ≤
      OnlineStochMatching.TSM.prob n (fun ω => avg n f - a < f ω ∧ g ω < avg n g + a) := by
  have h₁ := lower_tail n hn f 2 (by norm_num) hf a ha
  have h₂ := upper_tail n hn g 1 (by norm_num) hg a ha
  norm_num at h₁ h₂
  have he₁ : (fun ω => avg n f - a < f ω) = (fun ω => ¬a ≤ avg n f - f ω) := by
    funext ω
    exact propext (by push Not; constructor <;> intro h <;> linarith)
  have he₂ : (fun ω => g ω < avg n g + a) = (fun ω => ¬a ≤ g ω - avg n g) := by
    funext ω
    exact propext (by push Not; constructor <;> intro h <;> linarith)
  have h := prob_and_lower n (fun ω => avg n f - a < f ω) (fun ω => g ω < avg n g + a)
  rw [he₁, he₂, prob_compl, prob_compl] at h
  have hr : -a^2/(2*(n:ℝ)*4) = -a^2/(8*(n:ℝ)) := by ring
  rw [hr] at h₁
  linarith

end TSMProof


set_option autoImplicit false

namespace TSMProof
open OnlineStochMatching.TSM

lemma exp_one_gt_two : (2 : ℝ) < Real.exp 1 := by
  have h := Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
  norm_num at h ⊢
  exact h

lemma exp_one_lt_three : Real.exp 1 < (3 : ℝ) := by
  have h := Real.exp_one_lt_d9
  norm_num at h ⊢
  linarith

lemma alpha_positive : 0 < alpha := by
  have he := exp_one_gt_two
  unfold alpha
  apply div_pos
  · rw [sub_pos, div_lt_one (by positivity)]
    nlinarith
  · have hp : 0 < (3:ℝ)*Real.exp 1 := by positivity
    apply sub_pos.mpr
    apply (div_lt_iff₀ hp).mpr
    nlinarith

lemma alpha_beats_classical : 1 - Real.exp (-1) < alpha := by
  have he := exp_one_gt_two
  have h3 := exp_one_lt_three
  have hp : 0 < Real.exp 1 := Real.exp_pos _
  have hd : 0 < 4/3 - 2/(3*Real.exp 1) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ (by positivity : 0 < (3:ℝ)*Real.exp 1)).mpr
    nlinarith
  rw [Real.exp_neg, alpha, lt_div_iff₀ hd]
  have hprod : 0 < (Real.exp 1 - 2) * (4 - Real.exp 1) := mul_pos (by linarith) (by linarith)
  field_simp
  nlinarith

lemma coefficient_bound (br bb b r d : ℝ) (_hbr : 0 ≤ br) (hbb : 0 ≤ bb)
    (_hb : 0 ≤ b) (hr : 0 ≤ r) (hrb : r ≤ b)
    (hd : 3*d ≤ 2*br+4*bb+3*b+r) :
    alpha * (br+bb+(b+r)/2+(1/2-Real.exp (-1))*d) ≤
      (1-2*Real.exp (-2))*br+(1-Real.exp (-2))*bb+
      (1-Real.exp (-1))*b+(1-2*Real.exp (-1))*r := by
  let e := Real.exp 1
  have he : 2 < e := exp_one_gt_two
  have h3 : e < 3 := exp_one_lt_three
  have ep : 0 < e := by linarith
  have e0 : e ≠ 0 := ne_of_gt ep
  have den : 0 < 2*e^2*(2*e-1) := mul_pos (by positivity) (by linarith)
  have den0 : 2*e-1 ≠ 0 := by linarith
  have ha : alpha = 3*(e^2-2)/(2*e*(2*e-1)) := by
    change (1-2/e^2)/(4/3-2/(3*e)) = _
    have hh : (4:ℝ)/3-2/(3*e) = 2*(2*e-1)/(3*e) := by
      field_simp
      ring
    rw [hh]
    field_simp [e0, den0]
  have hx1 : Real.exp (-1) = 1/e := by simp [e, Real.exp_neg]
  have hx2 : Real.exp (-2) = 1/e^2 := by
    rw [show (-2:ℝ) = -(1+1) by norm_num, Real.exp_neg, Real.exp_add]
    simp [e, pow_two]
  rw [hx1, hx2]
  let z : ℝ := 1/2-1/e
  have hz : 0 ≤ z := by
    dsimp [z]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ ep).mpr
    linarith
  have hd' : alpha*z*d ≤ alpha*z*((2*br+4*bb+3*b+r)/3) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg alpha_positive.le hz)
  have hbbp : 0 ≤ -e^3+2*e^2+6*e-6 := by
    have hsq : e^2 ≤ 3*e := by nlinarith [mul_nonneg ep.le (show 0 ≤ 3-e by linarith)]
    have hcube : e^3 ≤ 3*e^2 := by nlinarith [mul_nonneg (sq_nonneg e) (show 0 ≤ 3-e by linarith)]
    nlinarith
  have hbp : 0 ≤ (e-1)*(e^2-2*e+6) := mul_nonneg (by linarith) (by nlinarith [sq_nonneg (e-1)])
  have hpair : 0 ≤ (e-2)*(3*e^2-6*e+4) := mul_nonneg (by linarith) (by nlinarith [sq_nonneg (e-1)])
  let cb := (e-1)*(e^2-2*e+6)/(2*e^2*(2*e-1))
  let cbb := (-e^3+2*e^2+6*e-6)/(2*e^2*(2*e-1))
  let cp := (e-2)*(3*e^2-6*e+4)/(2*e^2*(2*e-1))
  have hc : 0 ≤ cbb*bb+cb*(b-r)+cp*r := by
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (div_nonneg hbbp den.le) hbb)
        (mul_nonneg (div_nonneg hbp den.le) (sub_nonneg.mpr hrb))
    · exact mul_nonneg (div_nonneg hpair den.le) hr
  have hid : (1-2/e^2)*br+(1-1/e^2)*bb+(1-1/e)*b+(1-2/e)*r -
      alpha*(br+bb+(b+r)/2+z*((2*br+4*bb+3*b+r)/3)) = cbb*bb+cb*(b-r)+cp*r := by
    rw [ha]
    dsimp [z,cbb,cb,cp]
    field_simp
    ring
  have hh := sub_nonneg.mp (hid ▸ hc)
  dsimp [z] at hd' hh
  simp only [mul_one_div]
  nlinarith

open Filter Topology

lemma occupancy_limit (a : ℝ) :
    Tendsto (fun n : ℕ => (1-a/n)^n) atTop (𝓝 (Real.exp (-a))) := by
  simpa only [neg_div, sub_eq_add_neg] using Real.tendsto_one_add_div_pow_exp (-a)

lemma occupancy_base_limit (a : ℝ) :
    Tendsto (fun n : ℕ => 1-a/n) atTop (𝓝 (1:ℝ)) := by
  have h : Tendsto (fun n : ℕ => a/(n:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.sub h

lemma occupancy_pred_limit (a : ℝ) :
    Tendsto (fun n : ℕ => (1-a/n)^(n-1)) atTop (𝓝 (Real.exp (-a))) := by
  have h := (occupancy_limit a).div (occupancy_base_limit a) (by norm_num : (1:ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  have hn : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hb : ∀ᶠ n : ℕ in atTop, 1-a/(n:ℝ) ≠ 0 :=
    (occupancy_base_limit a).eventually_ne (by norm_num)
  filter_upwards [hn,hb] with n hn hb
  change (1-a/(n:ℝ))^n / (1-a/(n:ℝ)) = _
  rw [show (1-a/(n:ℝ))^n = (1-a/(n:ℝ))^(n-1) * (1-a/(n:ℝ)) by
    rw [← pow_succ]; congr 1; omega, mul_div_cancel_right₀ _ hb]

lemma occupancy_errors (η : ℝ) (hη : 0 < η) : ∃ N : ℕ, 2 ≤ N ∧ ∀ n ≥ N,
    |(1-1/(n:ℝ))^n-Real.exp (-1)| < η ∧
    |(1-1/(n:ℝ))^(n-1)-Real.exp (-1)| < η ∧
    |(1-2/(n:ℝ))^n-Real.exp (-2)| < η ∧
    |(1-2/(n:ℝ))^(n-1)-Real.exp (-2)| < η := by
  obtain ⟨N₁,h₁⟩ := Metric.tendsto_atTop.mp (occupancy_limit 1) η hη
  obtain ⟨N₂,h₂⟩ := Metric.tendsto_atTop.mp (occupancy_pred_limit 1) η hη
  obtain ⟨N₃,h₃⟩ := Metric.tendsto_atTop.mp (occupancy_limit 2) η hη
  obtain ⟨N₄,h₄⟩ := Metric.tendsto_atTop.mp (occupancy_pred_limit 2) η hη
  refine ⟨N₁+N₂+N₃+N₄+2, by omega, ?_⟩
  intro n hn
  exact ⟨by simpa [Real.dist_eq] using h₁ n (by omega),
    by simpa [Real.dist_eq] using h₂ n (by omega),
    by simpa [Real.dist_eq] using h₃ n (by omega),
    by simpa [Real.dist_eq] using h₄ n (by omega)⟩

lemma moment_gap (n br bb b r d η q₁ q₁' q₂ q₂' ef eg : ℝ)
    (hη : 0 ≤ η) (hbr : 0 ≤ br) (hbb : 0 ≤ bb) (hb : 0 ≤ b) (hr : 0 ≤ r)
    (hd0 : 0 ≤ d) (hrb : r ≤ b) (hsize : br+bb+b+r ≤ 2*n) (hdn : d ≤ 2*n)
    (hpack : 3*d ≤ 2*br+4*bb+3*b+r)
    (hq₁ : |q₁-Real.exp (-1)| ≤ η) (hq₁' : |q₁'-Real.exp (-1)| ≤ η)
    (hq₂ : |q₂-Real.exp (-2)| ≤ η) (hq₂' : |q₂'-Real.exp (-2)| ≤ η)
    (hf : ef = (1-q₂)*bb+(1-q₂-q₂')*br+(1-q₁)*b+(1-q₁-q₁')*r)
    (hg : eg ≤ br+bb+(b+r)/2+(1/2-q₁)*d) :
    alpha*eg-ef ≤ (4+2*alpha)*η*n := by
  let V := (1-2*Real.exp (-2))*br+(1-Real.exp (-2))*bb+
    (1-Real.exp (-1))*b+(1-2*Real.exp (-1))*r
  let U := br+bb+(b+r)/2+(1/2-Real.exp (-1))*d
  have hVU : alpha*U ≤ V := coefficient_bound br bb b r d hbr hbb hb hr hrb hpack
  have hf' : V-4*η*n ≤ ef := by
    have h₁ := mul_le_mul_of_nonneg_right (abs_le.mp hq₁).2 hb
    have h₂ := mul_le_mul_of_nonneg_right (abs_le.mp hq₁).2 hr
    have h₃ := mul_le_mul_of_nonneg_right (abs_le.mp hq₁').2 hr
    have h₄ := mul_le_mul_of_nonneg_right (abs_le.mp hq₂).2 hbb
    have h₅ := mul_le_mul_of_nonneg_right (abs_le.mp hq₂).2 hbr
    have h₆ := mul_le_mul_of_nonneg_right (abs_le.mp hq₂').2 hbr
    have hs := mul_le_mul_of_nonneg_left hsize hη
    dsimp [V]
    nlinarith [mul_nonneg hη hb, mul_nonneg hη hbb]
  have hg' : eg ≤ U+2*η*n := by
    have h₁ := mul_le_mul_of_nonneg_right (abs_le.mp hq₁).1 hd0
    have h₂ := mul_le_mul_of_nonneg_left hdn hη
    dsimp [U]
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hg' alpha_positive.le
  nlinarith

lemma absorb_tails (η : ℝ) (hη : 0 < η) : ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n →
      Real.exp (-(η*(n:ℝ))^2/(8*(n:ℝ))) + Real.exp (-(η*(n:ℝ))^2/(2*(n:ℝ))) ≤
        Real.exp (-δ*(n:ℝ)) := by
  let δ := η^2/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (Real.log 2 / δ)
  refine ⟨δ,hδ,N+1,?_⟩
  intro n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hlog : Real.log 2 ≤ δ*n := by
    have h := (div_le_iff₀ hδ).mp (hN.trans hnR)
    nlinarith
  have hx : Real.exp (-δ*n) ≤ 1/2 := by
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]; norm_num
  have ha : -(η*(n:ℝ))^2/(8*(n:ℝ)) = -2*δ*n := by
    dsimp [δ]
    field_simp
    ring
  have hb : -(η*(n:ℝ))^2/(2*(n:ℝ)) = -8*δ*n := by
    dsimp [δ]
    field_simp
    ring
  rw [ha,hb]
  have h₁ : Real.exp (-8*δ*n) ≤ Real.exp (-2*δ*n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he : Real.exp (-2*δ*n) = (Real.exp (-δ*n))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he] at h₁ ⊢
  nlinarith [Real.exp_pos (-δ*n)]

lemma probability_closure (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ (I : Type) [Fintype I] [Nonempty I] (n : ℕ), N ≤ n →
    ∀ (f g : (Fin n → I) → ℝ) (br bb b r d : ℝ),
      Oscillation n f 2 → Oscillation n g 1 →
      0 ≤ br → 0 ≤ bb → 0 ≤ b → 0 ≤ r → 0 ≤ d → r ≤ b →
      br+bb+b+r ≤ 2*(n:ℝ) → d ≤ 2*(n:ℝ) → 3*d ≤ 2*br+4*bb+3*b+r →
      avg n f = (1-(1-2/(n:ℝ))^n)*bb +
        (1-(1-2/(n:ℝ))^n-(1-2/(n:ℝ))^(n-1))*br +
        (1-(1-1/(n:ℝ))^n)*b + (1-(1-1/(n:ℝ))^n-(1-1/(n:ℝ))^(n-1))*r →
      avg n g ≤ br+bb+(b+r)/2+(1/2-(1-1/(n:ℝ))^n)*d →
      1-Real.exp (-δ*(n:ℝ)) ≤ OnlineStochMatching.TSM.prob n
        (fun ω => c*(n:ℝ) ≤ g ω → (alpha-ε)*g ω ≤ f ω) := by
  let η := ε*c/(8*(alpha+1))
  have hp := alpha_positive
  have hη : 0 < η := by dsimp [η]; positivity
  have hηeq : 8*(alpha+1)*η = ε*c := by dsimp [η]; field_simp
  obtain ⟨N₁,hN₁,herr⟩ := occupancy_errors η hη
  obtain ⟨δ,hδ,N₂,htail⟩ := absorb_tails η hη
  refine ⟨δ,hδ,N₁+N₂+2,by omega,?_⟩
  intro I _ _ n hn f g br bb b r d hf hg hbr hbb hb hr hd hrb hsize hdn hpack hef heg
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg _
  obtain ⟨hq₁,hq₁',hq₂,hq₂'⟩ := herr n (by omega)
  have hgap := moment_gap (n:ℝ) br bb b r d η
    ((1-1/(n:ℝ))^n) ((1-1/(n:ℝ))^(n-1))
    ((1-2/(n:ℝ))^n) ((1-2/(n:ℝ))^(n-1)) (avg n f) (avg n g)
    hη.le hbr hbb hb hr hd hrb hsize hdn hpack hq₁.le hq₁'.le hq₂.le hq₂'.le hef heg
  have hgood := concentration_good n hn0 f g hf hg (η*n) (mul_nonneg hη.le hnR)
  have htail' := htail n (by omega)
  have hprob : OnlineStochMatching.TSM.prob n (fun ω => avg n f - η*n < f ω ∧ g ω < avg n g + η*n) ≤
      OnlineStochMatching.TSM.prob n (fun ω => c*(n:ℝ) ≤ g ω → (alpha-ε)*g ω ≤ f ω) := by
    apply prob_mono
    intro ω hω hcg
    have hg' := mul_le_mul_of_nonneg_left hω.2.le hp.le
    have heps := mul_le_mul_of_nonneg_left hcg hε.le
    have heq := congrArg (fun x : ℝ => x*(n:ℝ)) hηeq
    have hpos : 0 ≤ (3+5*alpha)*η*(n:ℝ) := by positivity
    nlinarith [hω.1.le]
  linarith

end TSMProof


set_option autoImplicit false
namespace TSMProof.Peer
open OnlineStochMatching.TSM

lemma component_side_parity {A I : Type} {F : Finset (A × I)} (C : Comp A I)
    (hC : C.IsPathOrCycle F) (j : ℕ) (hj : j ≤ C.len) :
    ((C.v j).isRight = true) ↔ (Even j ↔ (C.v 0).isRight = true) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < C.len := by omega
    obtain ⟨e,_,he⟩ := hC.2.1 j hj'
    have hstep : (C.v (j+1)).isRight = true ↔ ¬(C.v j).isRight = true := by
      rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [h₁,h₂]
    rw [hstep,ih (by omega)]
    simp only [Nat.even_add_one]
    tauto

lemma component_cycle_even {A I : Type} {F : Finset (A × I)} (C : Comp A I)
    (hC : C.IsPathOrCycle F) (hc : C.cyc = true) : Even C.len := by
  have hend : C.v C.len = C.v 0 := (by simpa [hc] using hC.2.2 :
    4 ≤ C.len ∧ C.v C.len = C.v 0 ∧ ∀ j₁ < C.len, ∀ j₂ < C.len, C.v j₁ = C.v j₂ → j₁ = j₂).2.1
  have h := component_side_parity C hC C.len le_rfl
  rw [hend] at h
  tauto

lemma component_blue_zero {A I : Type} (C : Comp A I) : C.BlueAt 0 := by
  by_cases h : C.IsEvenImpressionPath <;> simp [Comp.BlueAt,h]

lemma component_blue_pair {A I : Type} (C : Comp A I) (j : ℕ)
    (hj : 0 < j) (hex : ¬(C.IsEvenImpressionPath ∧ j = 1)) :
    C.BlueAt (j-1) ↔ ¬C.BlueAt j := by
  by_cases h : C.IsEvenImpressionPath
  · have hj1 : j ≠ 1 := by tauto
    simp only [Comp.BlueAt,h,true_and,not_true_eq_false,false_and,or_false]
    simp only [Nat.odd_iff]
    omega
  · simp only [Comp.BlueAt,h,false_and,not_false_eq_true,true_and,false_or,Nat.even_iff]
    omega

lemma component_exception_blue {A I : Type} (C : Comp A I) (h : C.IsEvenImpressionPath) :
    C.BlueAt 0 ∧ C.BlueAt 1 := by
  simp [Comp.BlueAt,h]

lemma component_last_blue {A I : Type} {F : Finset (A × I)} (C : Comp A I)
    (hC : C.IsPathOrCycle F) (_hc : C.cyc = false) (ha : (C.v C.len).isRight = false) :
    C.BlueAt (C.len-1) ↔ Odd C.len := by
  have hn := hC.1
  have hex : ¬C.IsEvenImpressionPath := by
    intro h
    have hp := component_side_parity C hC C.len le_rfl
    have hright := hp.mpr (by simp [h.2.1,h.2.2])
    simp [ha] at hright
  simp only [Comp.BlueAt,hex,false_and,not_false_eq_true,true_and,false_or,
    Nat.even_iff,Nat.odd_iff]
  omega

lemma component_cycle_wrap {A I : Type} {F : Finset (A × I)} (C : Comp A I)
    (hC : C.IsPathOrCycle F) (hc : C.cyc = true) :
    ¬C.BlueAt (C.len-1) ∧ C.BlueAt 0 := by
  have he := component_cycle_even C hC hc
  have hn := hC.1
  have hex : ¬C.IsEvenImpressionPath := by simp [Comp.IsEvenImpressionPath,hc]
  refine ⟨?_,component_blue_zero C⟩
  simp only [Comp.BlueAt,hex,false_and,not_false_eq_true,true_and,false_or,Nat.even_iff]
  rw [Nat.even_iff] at he
  omega


lemma component_both_blue_iff {A I : Type} (C : Comp A I) (j : ℕ) (hj : 0 < j) :
    (C.BlueAt (j-1) ∧ C.BlueAt j) ↔ C.IsEvenImpressionPath ∧ j = 1 := by
  constructor
  · intro h
    by_contra hn
    exact ((component_blue_pair C j hj hn).mp h.1) h.2
  · rintro ⟨h,rfl⟩
    simpa using component_exception_blue C h

lemma component_exception_is_advertiser {A I : Type} {F : Finset (A × I)} (C : Comp A I)
    (hC : C.IsPathOrCycle F) (h : C.IsEvenImpressionPath) : (C.v 1).isRight = false := by
  have hp := component_side_parity C hC 1 hC.1
  simpa [h.2.2] using hp

lemma component_last_impression_blue {A I : Type} {F : Finset (A × I)} (C : Comp A I)
    (hC : C.IsPathOrCycle F) (hc : C.cyc = false) (hi : (C.v C.len).isRight = true) :
    C.BlueAt (C.len-1) := by
  have hn := hC.1
  have hp := (component_side_parity C hC C.len le_rfl).mp hi
  by_cases he : Even C.len
  · have hspecial : C.IsEvenImpressionPath := ⟨hc,he,hp.mp he⟩
    simp only [Comp.BlueAt,hspecial,true_and,not_true_eq_false,false_and,or_false,Nat.odd_iff]
    rw [Nat.even_iff] at he
    omega
  · have hspecial : ¬C.IsEvenImpressionPath := fun h => he h.2.1
    simp only [Comp.BlueAt,hspecial,false_and,not_false_eq_true,true_and,false_or,Nat.even_iff]
    rw [Nat.even_iff] at he
    omega

end TSMProof.Peer


set_option autoImplicit false
namespace TSMProof.Peer
open Finset

lemma linear_triple_bound (J : Finset ℕ) (L : ℕ) (hJ : J ⊆ range L)
    (hsep : ∀ x ∈ J, ∀ y ∈ J, x < y → x+3 ≤ y) : 3*J.card ≤ L+2 := by
  let S := J ×ˢ range 3
  have hmap : ∀ p ∈ S, p.1+p.2 ∈ range (L+2) := by
    intro p hp
    have hx := mem_range.mp (hJ (mem_product.mp hp).1)
    have ht := mem_range.mp (mem_product.mp hp).2
    exact mem_range.mpr (by omega)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1+p.2) (S : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    change p.1+p.2 = q.1+q.2 at he
    have hpx := (mem_product.mp hp).1
    have hqx := (mem_product.mp hq).1
    have hpt := mem_range.mp (mem_product.mp hp).2
    have hqt := mem_range.mp (mem_product.mp hq).2
    have hx : p.1=q.1 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · have := hsep _ hpx _ hqx h; omega
      · have := hsep _ hqx _ hpx h; omega
    exact Prod.ext hx (by omega)
  have h := card_le_card_of_injOn (fun p : ℕ × ℕ => p.1+p.2) hmap hinj
  simpa [S,card_product,Nat.mul_comm] using h

lemma cyclic_triple_bound (J : Finset ℕ) (L : ℕ) (hL : 3 ≤ L) (hJ : J ⊆ range L)
    (hsep : ∀ x ∈ J, (x+1)%L ∉ J ∧ (x+2)%L ∉ J) : 3*J.card ≤ L := by
  let S := J ×ˢ range 3
  have hinj : Set.InjOn (fun p : ℕ × ℕ => (p.1+p.2)%L) (S : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    have hpx := (mem_product.mp hp).1
    have hqx := (mem_product.mp hq).1
    have hpt := mem_range.mp (mem_product.mp hp).2
    have hqt := mem_range.mp (mem_product.mp hq).2
    have hpl := mem_range.mp (hJ hpx)
    have hql := mem_range.mp (hJ hqx)
    have hmod : Nat.ModEq L (p.1+p.2) (q.1+q.2) := he
    have hoff : p.2=q.2 := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with h | h
      · have heq : q.1+q.2 = (q.1+(q.2-p.2))+p.2 := by omega
        rw [heq] at hmod
        have hh := Nat.ModEq.add_right_cancel' p.2 hmod
        have hx : p.1 = (q.1+(q.2-p.2))%L := by
          simpa only [Nat.ModEq,Nat.mod_eq_of_lt hpl] using hh
        have hd : q.2-p.2=1 ∨ q.2-p.2=2 := by omega
        rcases hd with hd | hd
        · rw [hd] at hx; exact (hsep _ hqx).1 (hx ▸ hpx)
        · rw [hd] at hx; exact (hsep _ hqx).2 (hx ▸ hpx)
      · have heq : p.1+p.2 = (p.1+(p.2-q.2))+q.2 := by omega
        rw [heq] at hmod
        have hh := Nat.ModEq.add_right_cancel' q.2 hmod.symm
        have hx : q.1 = (p.1+(p.2-q.2))%L := by
          simpa only [Nat.ModEq,Nat.mod_eq_of_lt hql] using hh
        have hd : p.2-q.2=1 ∨ p.2-q.2=2 := by omega
        rcases hd with hd | hd
        · rw [hd] at hx; exact (hsep _ hpx).1 (hx ▸ hqx)
        · rw [hd] at hx; exact (hsep _ hpx).2 (hx ▸ hqx)
    have hh := Nat.ModEq.add_right_cancel' p.2 (by simpa only [← hoff] using hmod)
    have hx : p.1=q.1 := by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hpl,Nat.mod_eq_of_lt hql] using hh
    exact Prod.ext hx hoff
  have hmap : ∀ p ∈ S, (p.1+p.2)%L ∈ range L := by
    intro p _
    exact mem_range.mpr (Nat.mod_lt _ (by omega))
  have h := card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1+p.2)%L) hmap hinj
  simpa [S,card_product,Nat.mul_comm] using h

end TSMProof.Peer


set_option autoImplicit false
open Finset
open scoped BigOperators

namespace TSMProof.Occupancy
attribute [local instance] Classical.propDecidable

def Avoid {I : Type} {n : ℕ} (B : Finset I) (ω : Fin n → I) : Prop := ∀ t, ω t ∉ B

def count {I : Type} [DecidableEq I] {n : ℕ} (i : I) (ω : Fin n → I) : ℕ :=
  (univ.filter fun t => ω t = i).card

def One {I : Type} [DecidableEq I] {n : ℕ} (B : Finset I) (i : I) (ω : Fin n → I) : Prop :=
  Avoid B ω ∧ count i ω = 1

lemma avoid_cons {I : Type} {n : ℕ} (B : Finset I) (x : I) (ω : Fin n → I) :
    Avoid B (Fin.cons x ω) ↔ x ∉ B ∧ Avoid B ω := by
  simp [Avoid,Fin.forall_fin_succ]

lemma count_cons {I : Type} [DecidableEq I] {n : ℕ} (i x : I) (ω : Fin n → I) :
    count i (Fin.cons x ω) = (if x=i then 1 else 0)+count i ω := by
  simp only [count,Finset.card_filter,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma count_zero {I : Type} [DecidableEq I] {n : ℕ} (i : I) (ω : Fin n → I) :
    count i ω = 0 ↔ ∀ t, ω t ≠ i := by
  simp [count,Finset.card_eq_zero,Finset.filter_eq_empty_iff]

lemma avoid_insert {I : Type} [DecidableEq I] {n : ℕ} (B : Finset I) (i : I) (ω : Fin n → I) :
    Avoid (insert i B) ω ↔ Avoid B ω ∧ count i ω = 0 := by
  rw [count_zero]
  simp only [Avoid,mem_insert,not_or,forall_and]
  tauto

lemma one_cons {I : Type} [DecidableEq I] {n : ℕ} (B : Finset I) (i x : I)
    (hi : i ∉ B) (ω : Fin n → I) :
    One B i (Fin.cons x ω) ↔
      (x=i ∧ Avoid (insert i B) ω) ∨ (x ∉ insert i B ∧ One B i ω) := by
  rw [One,avoid_cons,count_cons,avoid_insert]
  by_cases hx : x=i
  · subst x
    simp [hi]
  · simp [hx,One]
    tauto

lemma mean_indicator {I : Type} [Fintype I] (P : I → Prop) [DecidablePred P] :
    TSMProof.mean (fun i => if P i then (1:ℝ) else 0) =
      ((univ.filter P).card : ℝ)/(Fintype.card I : ℝ) := by
  unfold TSMProof.mean
  congr 1
  rw [Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma avg_avoid {I : Type} [Fintype I] [Nonempty I] (B : Finset I) (n : ℕ) :
    TSMProof.avg n (fun ω => if Avoid B ω then (1:ℝ) else 0) =
      (((Fintype.card I:ℝ)-B.card)/(Fintype.card I:ℝ))^n := by
  classical
  induction n with
  | zero => simp [TSMProof.avg_zero,Avoid]
  | succ n ih =>
    rw [TSMProof.avg_cons]
    have hf : (fun x => TSMProof.avg n (fun ω => if Avoid B (Fin.cons x ω) then (1:ℝ) else 0)) =
        (fun x => (if x ∉ B then (1:ℝ) else 0) * TSMProof.avg n (fun ω => if Avoid B ω then (1:ℝ) else 0)) := by
      funext x
      by_cases hx : x ∈ B
      · simp [avoid_cons,hx,TSMProof.avg]
      · simp [avoid_cons,hx]
    rw [hf,ih]
    have hc : (univ.filter fun x => x ∉ B).card = Fintype.card I - B.card := by
      rw [show (univ.filter fun x => x ∉ B) = univ \ B by ext x; simp]
      rw [card_sdiff_of_subset (subset_univ _),card_univ]
    have he : (fun x => (if x ∉ B then (1:ℝ) else 0) * (((Fintype.card I:ℝ)-B.card)/(Fintype.card I:ℝ))^n) =
      (fun x => (((Fintype.card I:ℝ)-B.card)/(Fintype.card I:ℝ))^n * (if x ∉ B then (1:ℝ) else 0)) := by funext; ring
    rw [he,TSMProof.mean_mul,mean_indicator,hc,Nat.cast_sub (card_le_univ B),pow_succ]

lemma mean_mul_right {J : Type} [Fintype J] (f : J → ℝ) (c : ℝ) :
    TSMProof.mean (fun x => f x*c) = TSMProof.mean f*c := by
  simpa only [mul_comm] using TSMProof.mean_mul c f

lemma avg_one_step {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (B : Finset I) (i : I) (hi : i ∉ B) (n : ℕ) :
    TSMProof.avg (n+1) (fun ω => if One B i ω then (1:ℝ) else 0) =
      (1/(Fintype.card I:ℝ))*TSMProof.avg n (fun ω => if Avoid (insert i B) ω then (1:ℝ) else 0) +
      (((Fintype.card I:ℝ)-B.card-1)/(Fintype.card I:ℝ))*
        TSMProof.avg n (fun ω => if One B i ω then (1:ℝ) else 0) := by
  classical
  have hp : ∀ (x : I) (ω : Fin n → I),
      (if One B i (Fin.cons x ω) then (1:ℝ) else 0) =
      (if x=i then (1:ℝ) else 0)*(if Avoid (insert i B) ω then (1:ℝ) else 0) +
      (if x ∉ insert i B then (1:ℝ) else 0)*(if One B i ω then (1:ℝ) else 0) := by
    intro x ω
    rw [one_cons B i x hi]
    by_cases hx : x=i
    · subst x; simp
    · by_cases hb : x ∈ B <;> simp [hx,hb]
  rw [TSMProof.avg_cons]
  simp_rw [hp,TSMProof.avg_eq_mean,TSMProof.mean_add,TSMProof.mean_mul]
  rw [mean_mul_right,mean_mul_right,mean_indicator (fun x : I => x=i),
    mean_indicator (fun x : I => x ∉ insert i B)]
  have h₁ : (univ.filter fun x : I => x=i).card = 1 := by
    rw [show (univ.filter fun x : I => x=i) = {i} by ext x; simp]
    exact card_singleton i
  have h₂ : (univ.filter fun x : I => x ∉ insert i B).card = Fintype.card I-(B.card+1) := by
    rw [show (univ.filter fun x : I => x ∉ insert i B) = univ \ insert i B by ext x; simp]
    rw [card_sdiff_of_subset (subset_univ _),card_univ,card_insert_of_notMem hi]
  rw [h₁,h₂,Nat.cast_sub (by have h := card_le_univ (insert i B); simpa [hi] using h)]
  push_cast
  ring

lemma avg_one {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (B : Finset I) (i : I) (hi : i ∉ B) (n : ℕ) :
    TSMProof.avg n (fun ω => if One B i ω then (1:ℝ) else 0) =
      (n:ℝ)*((Fintype.card I:ℝ)-B.card-1)^(n-1)/(Fintype.card I:ℝ)^n := by
  classical
  have hN : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  induction n with
  | zero => simp [TSMProof.avg_zero,One,count]
  | succ n ih =>
    rw [avg_one_step B i hi,avg_avoid,ih,card_insert_of_notMem hi]
    push_cast
    have he : (Fintype.card I:ℝ)-(B.card+1) = (Fintype.card I:ℝ)-B.card-1 := by ring
    rw [he]
    by_cases hn : n = 0
    · subst n; simp
    · have hp : ((Fintype.card I:ℝ)-B.card-1)^n =
          ((Fintype.card I:ℝ)-B.card-1)^(n-1)*((Fintype.card I:ℝ)-B.card-1) := by
        rw [← pow_succ]; congr 1; omega
      rw [div_pow,pow_succ]
      field_simp [hN]
      rw [hp]
      ring

def visits {I : Type} [DecidableEq I] {n : ℕ} (S : Finset I) (ω : Fin n → I) : ℕ :=
  (univ.filter fun t => ω t ∈ S).card

lemma visits_cons {I : Type} [DecidableEq I] {n : ℕ} (S : Finset I) (x : I) (ω : Fin n → I) :
    visits S (Fin.cons x ω) = (if x∈S then 1 else 0)+visits S ω := by
  simp only [visits,card_filter,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma avg_visits {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (S : Finset I) (n : ℕ) :
    TSMProof.avg n (fun ω => (visits S ω : ℝ)) = (n:ℝ)*S.card/(Fintype.card I:ℝ) := by
  induction n with
  | zero => simp [TSMProof.avg_zero,visits]
  | succ n ih =>
    rw [TSMProof.avg_cons]
    simp_rw [visits_cons,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      TSMProof.avg_eq_mean,TSMProof.mean_add,TSMProof.mean_const]
    rw [mean_indicator (fun x : I => x ∈ S)]
    have he : (univ.filter fun x : I => x ∈ S) = S := by ext x; simp
    rw [he,← TSMProof.avg_eq_mean n,ih]
    ring

lemma prob_avoid {I : Type} [Fintype I] [Nonempty I] (B : Finset I) (n : ℕ) :
    OnlineStochMatching.TSM.prob n (Avoid B) =
      (((Fintype.card I:ℝ)-B.card)/(Fintype.card I:ℝ))^n := by
  rw [← TSMProof.avg_indicator]
  exact avg_avoid B n

lemma prob_one {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (B : Finset I) (i : I) (hi : i ∉ B) (n : ℕ) :
    OnlineStochMatching.TSM.prob n (One B i) =
      (n:ℝ)*((Fintype.card I:ℝ)-B.card-1)^(n-1)/(Fintype.card I:ℝ)^n := by
  rw [← TSMProof.avg_indicator]
  exact avg_one B i hi n

lemma avg_avoid_ratio {I : Type} [Fintype I] [Nonempty I] (B : Finset I) (n : ℕ) :
    TSMProof.avg n (fun ω => if Avoid B ω then (1:ℝ) else 0) =
      (1-(B.card:ℝ)/(Fintype.card I:ℝ))^n := by
  rw [avg_avoid]
  congr 1
  have hN : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma avg_one_diagonal {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (B : Finset I) (i : I) (hi : i ∉ B) :
    TSMProof.avg (Fintype.card I) (fun ω => if One B i ω then (1:ℝ) else 0) =
      (1-((B.card:ℝ)+1)/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  rw [avg_one B i hi]
  have hN : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : 0 < Fintype.card I := Fintype.card_pos
  have hb : 1-((B.card:ℝ)+1)/(Fintype.card I:ℝ) =
      ((Fintype.card I:ℝ)-B.card-1)/(Fintype.card I:ℝ) := by field_simp; ring
  rw [hb,div_pow]
  have hp : (Fintype.card I:ℝ)^(Fintype.card I) =
      (Fintype.card I:ℝ)^(Fintype.card I-1)*(Fintype.card I:ℝ) := by
    rw [← pow_succ]; congr 1; omega
  rw [hp]
  field_simp

lemma avg_visits_diagonal {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (S : Finset I) :
    TSMProof.avg (Fintype.card I) (fun ω => (visits S ω : ℝ)) = S.card := by
  rw [avg_visits]
  have hN : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma avg_avoid_singleton {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i : I) (n : ℕ) :
    TSMProof.avg n (fun ω => if Avoid {i} ω then (1:ℝ) else 0) =
      (1-1/(Fintype.card I:ℝ))^n := by
  simpa using avg_avoid_ratio ({i}:Finset I) n

lemma avg_avoid_pair {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i j : I) (hij : i ≠ j) (n : ℕ) :
    TSMProof.avg n (fun ω => if Avoid {i,j} ω then (1:ℝ) else 0) =
      (1-2/(Fintype.card I:ℝ))^n := by
  simpa [hij] using avg_avoid_ratio ({i,j}:Finset I) n

lemma avg_one_empty {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i : I) :
    TSMProof.avg (Fintype.card I) (fun ω => if One ∅ i ω then (1:ℝ) else 0) =
      (1-1/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  simpa using avg_one_diagonal (∅:Finset I) i (by simp)

lemma avg_one_avoid_other {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i j : I) (hij : i ≠ j) :
    TSMProof.avg (Fintype.card I) (fun ω => if One {j} i ω then (1:ℝ) else 0) =
      (1-2/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  simpa only [card_singleton,Nat.cast_one,show (1:ℝ)+1=2 by norm_num] using
    avg_one_diagonal ({j}:Finset I) i (by simpa)

lemma avg_sum {I X : Type} [Fintype I] (n : ℕ) (S : Finset X) (f : X → (Fin n → I) → ℝ) :
    TSMProof.avg n (fun ω => ∑ x ∈ S, f x ω) = ∑ x ∈ S, TSMProof.avg n (f x) := by
  simp only [TSMProof.avg]
  rw [Finset.sum_comm,Finset.sum_div]

lemma avg_card_filter {I X : Type} [Fintype I] (n : ℕ) (S : Finset X)
    (P : (Fin n → I) → X → Prop) :
    TSMProof.avg n (fun ω => ((S.filter (P ω)).card : ℝ)) =
      ∑ x ∈ S, TSMProof.avg n (fun ω => if P ω x then (1:ℝ) else 0) := by
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  exact avg_sum n S _

lemma avg_occupied {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i : I) (n : ℕ) :
    TSMProof.avg n (fun ω => if ∃ t, ω t=i then (1:ℝ) else 0) =
      1-(1-1/(Fintype.card I:ℝ))^n := by
  classical
  have he : (fun ω : Fin n → I => if ∃ t, ω t=i then (1:ℝ) else 0) =
      (fun ω => 1-(if Avoid {i} ω then (1:ℝ) else 0)) := by
    funext ω
    have h : Avoid {i} ω ↔ ¬∃ t, ω t=i := by simp [Avoid]
    rw [h]
    split_ifs <;> simp_all
  rw [he,TSMProof.avg_eq_mean,TSMProof.mean_sub,TSMProof.mean_const,
    ← TSMProof.avg_eq_mean n,avg_avoid_singleton]

lemma avg_occupied_types {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (S : Finset I) (n : ℕ) :
    TSMProof.avg n (fun ω => ((S.filter fun i => ∃ t, ω t=i).card : ℝ)) =
      S.card*(1-(1-1/(Fintype.card I:ℝ))^n) := by
  have he : ∀ ω : Fin n → I, ((S.filter fun i => ∃ t, ω t=i).card : ℝ) =
      ∑ i ∈ S, if ∃ t, ω t=i then (1:ℝ) else 0 := by
    intro ω
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  simp_rw [he]
  rw [avg_sum]
  simp_rw [avg_occupied]
  simp
  ring

def Success {I : Type} [DecidableEq I] {n : ℕ} (U V : Finset I) (ω : Fin n → I) : Prop :=
  (∃ i ∈ U, 0 < count i ω) ∨ (∃ i ∈ V, 1 < count i ω)

lemma success_empty {I : Type} [DecidableEq I] {n : ℕ} (ω : Fin n → I) :
    ¬Success ∅ ∅ ω := by simp [Success]

lemma success_blue {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (U : Finset I) (n : ℕ) :
    TSMProof.avg n (fun ω => if Success U ∅ ω then (1:ℝ) else 0) =
      1-(1-(U.card:ℝ)/(Fintype.card I:ℝ))^n := by
  have he : (fun ω : Fin n → I => if Success U ∅ ω then (1:ℝ) else 0) =
      (fun ω => 1-(if Avoid U ω then (1:ℝ) else 0)) := by
    funext ω
    have h : Success U ∅ ω ↔ ¬Avoid U ω := by
      simp only [Success,Avoid]
      constructor
      · rintro (⟨i,hi,hc⟩ | ⟨i,hi,_⟩) ha
        · have hz : count i ω = 0 := (count_zero i ω).2 (fun t ht => ha t (ht ▸ hi))
          omega
        · simp at hi
      · intro h
        have hx : ∃ t, ω t ∈ U := by simpa only [not_forall,not_not] using h
        obtain ⟨t,ht⟩ := hx
        left
        refine ⟨ω t,ht,?_⟩
        have hz : count (ω t) ω ≠ 0 := by intro hz; exact (count_zero _ _).1 hz t rfl
        omega
    rw [h]
    split_ifs <;> simp_all
  rw [he,TSMProof.avg_eq_mean,TSMProof.mean_sub,TSMProof.mean_const,
    ← TSMProof.avg_eq_mean n,avg_avoid_ratio]

lemma success_red {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i : I) :
    TSMProof.avg (Fintype.card I) (fun ω => if Success ∅ {i} ω then (1:ℝ) else 0) =
      1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I)-
        (1-1/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  have he : (fun ω : Fin (Fintype.card I) → I => if Success ∅ {i} ω then (1:ℝ) else 0) =
      (fun ω => 1-(if Avoid {i} ω then (1:ℝ) else 0)-(if One ∅ i ω then (1:ℝ) else 0)) := by
    funext ω
    have ha : Avoid {i} ω ↔ count i ω=0 := by simpa [Avoid] using (count_zero i ω).symm
    simp only [Success,Finset.notMem_empty,false_and,exists_false,mem_singleton,exists_eq_left,false_or,
      One,show Avoid (∅:Finset I) ω from by simp [Avoid],true_and,ha]
    split_ifs <;> simp_all
    all_goals omega
  rw [he,TSMProof.avg_eq_mean,TSMProof.mean_sub,TSMProof.mean_sub,TSMProof.mean_const,
    ← TSMProof.avg_eq_mean (Fintype.card I),← TSMProof.avg_eq_mean (Fintype.card I),
    avg_avoid_singleton,avg_one_empty]

lemma success_mixed {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] (i j : I) (hij : i ≠ j) :
    TSMProof.avg (Fintype.card I) (fun ω => if Success {i} {j} ω then (1:ℝ) else 0) =
      1-(1-2/(Fintype.card I:ℝ))^(Fintype.card I)-
        (1-2/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  have he : (fun ω : Fin (Fintype.card I) → I => if Success {i} {j} ω then (1:ℝ) else 0) =
      (fun ω => 1-(if Avoid {i,j} ω then (1:ℝ) else 0)-(if One {i} j ω then (1:ℝ) else 0)) := by
    funext ω
    have ha : Avoid {i,j} ω ↔ count i ω=0 ∧ count j ω=0 := by
      rw [avoid_insert]
      have hj : Avoid {j} ω ↔ count j ω=0 := by simpa [Avoid] using (count_zero j ω).symm
      rw [hj]; tauto
    have hb : Avoid {i} ω ↔ count i ω=0 := by simpa [Avoid] using (count_zero i ω).symm
    simp only [Success,mem_singleton,exists_eq_left,One,ha,hb]
    split_ifs <;> simp_all
    all_goals omega
  rw [he,TSMProof.avg_eq_mean,TSMProof.mean_sub,TSMProof.mean_sub,TSMProof.mean_const,
    ← TSMProof.avg_eq_mean (Fintype.card I),← TSMProof.avg_eq_mean (Fintype.card I),
    avg_avoid_pair i j hij,avg_one_avoid_other j i (Ne.symm hij)]

lemma success_card_blue {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (U V : Finset I) (hV : V.card=0) (n : ℕ) :
    TSMProof.avg n (fun ω => if Success U V ω then (1:ℝ) else 0) =
      1-(1-(U.card:ℝ)/(Fintype.card I:ℝ))^n := by
  have hv := card_eq_zero.mp hV
  subst V
  exact success_blue U n

lemma success_card_red {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (U V : Finset I) (hU : U.card=0) (hV : V.card=1) :
    TSMProof.avg (Fintype.card I) (fun ω => if Success U V ω then (1:ℝ) else 0) =
      1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I)-
        (1-1/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  obtain rfl := card_eq_zero.mp hU
  obtain ⟨i,rfl⟩ := card_eq_one.mp hV
  exact success_red i

lemma success_card_mixed {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (U V : Finset I) (hU : U.card=1) (hV : V.card=1) (hd : Disjoint U V) :
    TSMProof.avg (Fintype.card I) (fun ω => if Success U V ω then (1:ℝ) else 0) =
      1-(1-2/(Fintype.card I:ℝ))^(Fintype.card I)-
        (1-2/(Fintype.card I:ℝ))^(Fintype.card I-1) := by
  obtain ⟨i,rfl⟩ := card_eq_one.mp hU
  obtain ⟨j,rfl⟩ := card_eq_one.mp hV
  exact success_mixed i j (by simpa using hd)

lemma success_classes {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (U V : Finset I) (hd : Disjoint U V)
    (hc : (U.card=0 ∧ V.card=0) ∨ (U.card=1 ∧ V.card=0) ∨
      (U.card=0 ∧ V.card=1) ∨ (U.card=1 ∧ V.card=1) ∨ (U.card=2 ∧ V.card=0)) :
    TSMProof.avg (Fintype.card I) (fun ω => if Success U V ω then (1:ℝ) else 0) =
      (if U.card=1 ∧ V.card=1 then
        1-(1-2/(Fintype.card I:ℝ))^(Fintype.card I)-(1-2/(Fintype.card I:ℝ))^(Fintype.card I-1) else 0) +
      (if U.card=2 ∧ V.card=0 then 1-(1-2/(Fintype.card I:ℝ))^(Fintype.card I) else 0) +
      (if U.card=1 ∧ V.card=0 then 1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I) else 0) +
      (if U.card=0 ∧ V.card=1 then
        1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I)-(1-1/(Fintype.card I:ℝ))^(Fintype.card I-1) else 0) := by
  rcases hc with ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [success_card_blue U V hv]
    simp [hu,hv]
  · rw [success_card_blue U V hv]
    simp [hu,hv]
  · rw [success_card_red U V hu hv]
    simp [hu,hv]
  · rw [success_card_mixed U V hu hv hd]
    simp [hu,hv]
  · rw [success_card_blue U V hv]
    simp [hu,hv]

end TSMProof.Occupancy


open Finset
open OnlineStochMatching.TSM
namespace TSMProof
variable {A I : Type}

def graph (F : Finset (A × I)) : SimpleGraph (A ⊕ I) where
  Adj x y := match x, y with
    | .inl a, .inr i => (a,i) ∈ F
    | .inr i, .inl a => (a,i) ∈ F
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

@[simp] theorem graph_left_right (F : Finset (A × I)) (a : A) (i : I) :
    (graph F).Adj (.inl a) (.inr i) ↔ (a,i) ∈ F := Iff.rfl
@[simp] theorem graph_right_left (F : Finset (A × I)) (a : A) (i : I) :
    (graph F).Adj (.inr i) (.inl a) ↔ (a,i) ∈ F := Iff.rfl

 theorem three_mem_eq {α : Type} [DecidableEq α] {s : Finset α} (hc : s.card ≤ 2)
    {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hd : c ∈ s) :
    a = b ∨ a = c ∨ b = c := by
  by_contra h
  push Not at h
  have hs : ({a,b,c} : Finset α) ⊆ s := by simp_all [subset_iff]
  have := card_le_card hs
  simp [h.1,h.2.1,h.2.2] at this
  omega

 theorem graph_three [DecidableEq A] [DecidableEq I] (E F : Finset (A × I)) (h : IsTwoMatching E F)
    {v x y z : A ⊕ I} (hx : (graph F).Adj v x) (hy : (graph F).Adj v y)
    (hz : (graph F).Adj v z) : x = y ∨ x = z ∨ y = z := by
  cases v with
  | inl a =>
    cases x with
    | inl b => exact False.elim hx
    | inr i =>
      cases y with
      | inl b => exact False.elim hy
      | inr j =>
        cases z with
        | inl b => exact False.elim hz
        | inr k =>
          have hh := three_mem_eq (h.2.1 a)
            (mem_filter.mpr ⟨hx,rfl⟩) (mem_filter.mpr ⟨hy,rfl⟩)
            (mem_filter.mpr ⟨hz,rfl⟩)
          simpa only [Prod.mk.injEq, true_and, Sum.inr.injEq] using hh
  | inr i =>
    cases x with
    | inr j => exact False.elim hx
    | inl a =>
      cases y with
      | inr j => exact False.elim hy
      | inl b =>
        cases z with
        | inr j => exact False.elim hz
        | inl c =>
          have hh := three_mem_eq (h.2.2 i)
            (mem_filter.mpr ⟨hx,rfl⟩) (mem_filter.mpr ⟨hy,rfl⟩)
            (mem_filter.mpr ⟨hz,rfl⟩)
          simpa only [Prod.mk.injEq, and_true, Sum.inl.injEq] using hh

section Generic
variable {V : Type} {G : SimpleGraph V}
variable (hdeg : ∀ {v x y z}, G.Adj v x → G.Adj v y → G.Adj v z →
  x = y ∨ x = z ∨ y = z)

 include hdeg in
 theorem path_internal_neighbors {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    {j : ℕ} (hj : 0 < j) (hjl : j < p.length) {w : V} (hw : G.Adj (p.getVert j) w) :
    w = p.getVert (j-1) ∨ w = p.getVert (j+1) := by
  have ha : G.Adj (p.getVert j) (p.getVert (j-1)) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using
      (p.adj_getVert_succ (i := j-1) (by omega)).symm
  have hb := p.adj_getVert_succ hjl
  rcases hdeg hw ha hb with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have := hp.getVert_injOn (by simp; omega) (by simp; omega) h
    omega

 theorem maximal_endpoint_support {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {w : V} (hw : G.Adj u w) : w ∈ p.support := by
  by_contra hn
  have hq : (p.cons hw.symm).IsPath := (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hp,hn⟩
  have := hm _ _ _ hq
  simp only [SimpleGraph.Walk.length_cons] at this
  omega

 include hdeg in
 theorem maximal_path_closed {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {x y : V} (hx : x ∈ p.support) (hy : G.Adj x y) : y ∈ p.support := by
  obtain ⟨j,hj,hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  subst x
  by_cases h0 : j = 0
  · subst j
    exact maximal_endpoint_support p hp hm (by simpa using hy)
  by_cases hl : j = p.length
  · subst j
    have hr := maximal_endpoint_support p.reverse hp.reverse
      (fun a b q hq => by simpa using hm a b q hq) (by simpa using hy)
    simpa using hr
  rcases path_internal_neighbors hdeg p hp (by omega) (by omega) hy with h | h
  · exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨j-1,h.symm,by omega⟩
  · exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨j+1,h.symm,by omega⟩

 include hdeg in
 theorem maximal_endpoint_neighbors {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {w : V} (hw : G.Adj u w) : w = p.getVert 1 ∨ w = v := by
  obtain ⟨j,hj,hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (maximal_endpoint_support p hp hm hw)
  by_cases hl : j = p.length
  · right; simpa [hl] using hj.symm
  have h0 : j ≠ 0 := by intro h; subst j; simp at hj; exact hw.ne hj
  have hi := path_internal_neighbors hdeg p hp (by omega) (by omega)
    (show G.Adj (p.getVert j) u by rw [hj]; exact hw.symm)
  rcases hi with h | h
  · have he := hp.getVert_injOn (show 0 ≤ p.length by omega) (show j-1 ≤ p.length by omega)
      (by simpa using h)
    left; have : j = 1 := by omega
    simpa [this] using hj.symm
  · have he := hp.getVert_injOn (show 0 ≤ p.length by omega) (show j+1 ≤ p.length by omega)
      (by simpa using h)
    omega
include hdeg in
 theorem maximal_path_edges {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (hm : ∀ (x y : V) (q : G.Walk x y), q.IsPath → q.length ≤ p.length)
    {x y : V} (hx : x ∈ p.support) (hy : G.Adj x y) :
    s(x,y) ∈ p.edges ∨ s(x,y) = s(u,v) := by
  have hend : ∀ {w}, G.Adj u w → s(u,w) ∈ p.edges ∨ s(u,w) = s(u,v) := by
    intro w hw
    rcases maximal_endpoint_neighbors hdeg p hp hm hw with h | h
    · left; rw [h]
      apply p.mk_mem_edges_iff_exists.mpr
      refine ⟨0, ?_, by simp⟩
      by_contra hn
      have he : p.length = 0 := by omega
      have : p.getVert 1 = u := by rw [p.getVert_of_length_le (by omega)]; simpa using p.getVert_length.symm.trans (by simp [he])
      exact hw.ne (h.trans this).symm
    · right; rw [h]
  obtain ⟨j,hj,hjl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  subst x
  by_cases h0 : j = 0
  · subst j; simpa using hend (by simpa using hy)
  by_cases hl : j = p.length
  · subst j
    have hr := maximal_endpoint_neighbors hdeg p.reverse hp.reverse
      (fun a b q hq => by simpa using hm a b q hq) (by simpa using hy)
    rcases hr with hr | hr
    · left
      rw [p.getVert_length, hr]
      have hpos : 0 < p.reverse.length := by
        by_contra hn
        have he : p.length = 0 := by simpa using Nat.eq_zero_of_not_pos hn
        exact h0 he
      have hh : s(v,p.reverse.getVert 1) ∈ p.reverse.edges :=
        p.reverse.mk_mem_edges_iff_exists.mpr ⟨0,hpos,by simp⟩
      simpa using hh
    · right; simp [hr, Sym2.eq_swap]
  rcases path_internal_neighbors hdeg p hp (by omega) (by omega) hy with h | h
  · left; apply p.mk_mem_edges_iff_exists.mpr
    refine ⟨j-1,by omega,?_⟩
    simp [Nat.sub_add_cancel (by omega : 1 ≤ j),h,Sym2.eq_swap]
  · left; apply p.mk_mem_edges_iff_exists.mpr
    exact ⟨j,by omega,by rw [h]⟩
end Generic

section Convert
 theorem graph_triangle_free (F : Finset (A × I)) {x y z : A ⊕ I}
    (hxy : (graph F).Adj x y) (hyz : (graph F).Adj y z) : ¬(graph F).Adj z x := by
  cases x <;> cases y <;> cases z <;> simp_all [graph]

 def walkComp {F : Finset (A × I)} {u v : A ⊕ I} (p : (graph F).Walk u v)
    (cyc : Bool) : Comp A I := ⟨p.length,p.getVert,cyc⟩

 theorem walkComp_edge {F : Finset (A × I)} {u v : A ⊕ I}
    (p : (graph F).Walk u v) (cyc : Bool) (j : ℕ) (e : A × I) :
    (walkComp p cyc).HasEdgeAt j e ↔
      s(p.getVert j,p.getVert (j+1)) = s(Sum.inl e.1,Sum.inr e.2) := by
  simp only [Comp.HasEdgeAt,walkComp,Sym2.eq,Sym2.rel_iff',Prod.mk.injEq,Prod.swap_prod_mk]

 theorem walkComp_edges {F : Finset (A × I)} {u v : A ⊕ I}
    (p : (graph F).Walk u v) (cyc : Bool) (e : A × I) :
    (∃ j < (walkComp p cyc).len, (walkComp p cyc).HasEdgeAt j e) ↔
      s(Sum.inl e.1,Sum.inr e.2) ∈ p.edges := by
  simp_rw [walkComp_edge]
  exact p.mk_mem_edges_iff_exists.symm

 theorem walkComp_verts [DecidableEq A] [DecidableEq I] {F : Finset (A × I)} {u v : A ⊕ I}
    (p : (graph F).Walk u v) (cyc : Bool) (x : A ⊕ I) :
    x ∈ (walkComp p cyc).verts ↔ x ∈ p.support := by
  simp only [Comp.verts,walkComp,mem_image,mem_range]
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
  constructor
  · rintro ⟨j,hj,h⟩; exact ⟨j,h,by omega⟩
  · rintro ⟨j,h,hj⟩; exact ⟨j,by omega,h⟩

 theorem walkComp_valid {F : Finset (A × I)} {u v : A ⊕ I}
    (p : (graph F).Walk u v) (hp : p.IsPath) (hn : 0 < p.length) :
    (walkComp p false).IsPathOrCycle F := by
  refine ⟨hn,?_,?_⟩
  · intro j hj
    have ha := p.adj_getVert_succ hj
    change (match p.getVert j, p.getVert (j+1) with
      | .inl a, .inr i => (a,i) ∈ F
      | .inr i, .inl a => (a,i) ∈ F
      | _, _ => False) at ha
    cases hx : p.getVert j with
    | inl a =>
      cases hy : p.getVert (j+1) with
      | inl b => simp [hx,hy] at ha
      | inr i => exact ⟨(a,i),by simpa [hx,hy] using ha,Or.inl ⟨hx,hy⟩⟩
    | inr i =>
      cases hy : p.getVert (j+1) with
      | inl a => exact ⟨(a,i),by simpa [hx,hy] using ha,Or.inr ⟨hx,hy⟩⟩
      | inr k => simp [hx,hy] at ha
  · change ∀ j ≤ p.length, ∀ k ≤ p.length, p.getVert j = p.getVert k → j = k
    exact hp.getVert_injOn

 theorem walkComp_cycle_valid {F : Finset (A × I)} {u : A ⊕ I}
    (p : (graph F).Walk u u) (hp : p.IsCycle) :
    (walkComp p true).IsPathOrCycle F := by
  have h3 := hp.three_le_length
  have h4 : 4 ≤ p.length := by
    by_contra hn
    have he : p.length = 3 := by omega
    have hh := graph_triangle_free F (p.adj_getVert_succ (i:=0) (by omega))
      (p.adj_getVert_succ (i:=1) (by omega))
    apply hh
    simpa [← he] using p.adj_getVert_succ (i:=2) (by omega)
  refine ⟨by exact Nat.le_trans (by omega) h4,?_,?_⟩
  · intro j hj
    have ha := p.adj_getVert_succ hj
    change (match p.getVert j, p.getVert (j+1) with
      | .inl a, .inr i => (a,i) ∈ F
      | .inr i, .inl a => (a,i) ∈ F
      | _, _ => False) at ha
    cases hx : p.getVert j with
    | inl a =>
      cases hy : p.getVert (j+1) with
      | inl b => simp [hx,hy] at ha
      | inr i => exact ⟨(a,i),by simpa [hx,hy] using ha,Or.inl ⟨hx,hy⟩⟩
    | inr i =>
      cases hy : p.getVert (j+1) with
      | inl a => exact ⟨(a,i),by simpa [hx,hy] using ha,Or.inr ⟨hx,hy⟩⟩
      | inr k => simp [hx,hy] at ha
  · change 4 ≤ p.length ∧ p.getVert p.length = p.getVert 0 ∧ _
    refine ⟨h4,by simp,?_⟩
    intro j hj k hk hh
    change j < p.length at hj
    change k < p.length at hk
    exact hp.getVert_injOn' (by simp; omega) (by simp; omega) hh
end Convert

section Extraction
def Occurs (C : Comp A I) (e : A × I) : Prop :=
  ∃ j < C.len, C.HasEdgeAt j e

def Closed [DecidableEq A] [DecidableEq I] (F : Finset (A × I)) (C : Comp A I) : Prop :=
  ∀ e ∈ F, (Sum.inl e.1 ∈ C.verts ∨ Sum.inr e.2 ∈ C.verts) → Occurs C e

 theorem exists_closed_component [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] (E F : Finset (A × I)) (ht : IsTwoMatching E F)
    (hn : F.Nonempty) : ∃ C : Comp A I, C.IsPathOrCycle F ∧ Closed F C := by
  classical
  obtain ⟨e,he⟩ := hn
  let : Nonempty (A ⊕ I) := ⟨Sum.inl e.1⟩
  obtain ⟨u,v,p,hp,hm⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length (graph F)
  have hpos : 0 < p.length := by
    have hh : (graph F).Adj (Sum.inl e.1) (Sum.inr e.2) := he
    have := hm _ _ hh.toWalk (SimpleGraph.Walk.IsPath.of_adj hh)
    change 1 ≤ p.length at this
    omega
  have hd : ∀ {v x y z}, (graph F).Adj v x → (graph F).Adj v y →
      (graph F).Adj v z → x = y ∨ x = z ∨ y = z := graph_three E F ht
  have mkClosed : ∀ {x y : A ⊕ I} (q : (graph F).Walk x y) (b : Bool),
      (∀ z ∈ q.support, ∀ w, (graph F).Adj z w → s(z,w) ∈ q.edges) →
      Closed F (walkComp q b) := by
    intro x y q b hh f hf hv
    apply (walkComp_edges q b f).mpr
    rcases hv with hv | hv
    · exact hh _ ((walkComp_verts q b _).mp hv) _ hf
    · simpa [Sym2.eq_swap] using hh _ ((walkComp_verts q b _).mp hv) _
        (show (graph F).Adj (Sum.inr f.2) (Sum.inl f.1) from hf)
  by_cases hc : (graph F).Adj u v ∧ 1 < p.length
  · let q := p.cons hc.1.symm
    have hq : q.IsCycle := by
      apply (SimpleGraph.Walk.cons_isCycle_iff _ _).mpr
      refine ⟨hp,?_⟩
      intro hmemb
      have hs : v = p.getVert 1 := hp.eq_snd_of_mem_edges (by simpa [Sym2.eq_swap] using hmemb)
      have := hp.getVert_injOn (show p.length ≤ p.length from le_rfl)
        (show 1 ≤ p.length by omega) (by simpa using hs)
      omega
    refine ⟨walkComp q true,walkComp_cycle_valid q hq,mkClosed q true ?_⟩
    intro z hz w hw
    have hz' : z ∈ p.support := by
      simp only [q,SimpleGraph.Walk.support_cons,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact p.end_mem_support
      · exact hz
    rcases maximal_path_edges hd p hp hm hz' hw with h | h
    · simp [q,SimpleGraph.Walk.edges_cons,h]
    · simp [q,SimpleGraph.Walk.edges_cons,h,Sym2.eq_swap]
  · refine ⟨walkComp p false,walkComp_valid p hp hpos,mkClosed p false ?_⟩
    intro z hz w hw
    rcases maximal_path_edges hd p hp hm hz hw with h | h
    · exact h
    · have huv : (graph F).Adj u v := by
        have hs : (z,w) = (u,v) ∨ (z,w) = (u,v).swap := by
          simpa only [Sym2.eq,Sym2.rel_iff'] using h
        rcases hs with hs | hs <;> simp only [Prod.mk.injEq,Prod.swap_prod_mk] at hs
        · rcases hs with ⟨rfl,rfl⟩; exact hw
        · rcases hs with ⟨rfl,rfl⟩; exact hw.symm
      have hl : p.length = 1 := by
        have : ¬1 < p.length := fun hh => hc ⟨huv,hh⟩
        omega
      rw [h]
      exact p.mk_mem_edges_iff_exists.mpr ⟨0,hpos,by simp [← hl]⟩

 theorem hasEdgeAt_unique (C : Comp A I) (j : ℕ) {e f : A × I}
    (he : C.HasEdgeAt j e) (hf : C.HasEdgeAt j f) : e = f := by
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    rcases hf with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;> simp_all <;> apply Prod.ext <;> symm <;> assumption

 theorem occurs_mem {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) {e : A × I} (he : Occurs C e) : e ∈ F := by
  obtain ⟨j,hj,h⟩ := he
  obtain ⟨f,hf,hf'⟩ := hC.2.1 j hj
  exact hasEdgeAt_unique C j h hf' ▸ hf

 theorem occurs_verts [DecidableEq A] [DecidableEq I] {C : Comp A I} {e : A × I} (he : Occurs C e) :
    Sum.inl e.1 ∈ C.verts ∧ Sum.inr e.2 ∈ C.verts := by
  obtain ⟨j,hj,h⟩ := he
  have h1 : C.v j ∈ C.verts := mem_image.mpr ⟨j,mem_range.mpr (by omega),rfl⟩
  have h2 : C.v (j+1) ∈ C.verts := mem_image.mpr ⟨j+1,mem_range.mpr (by omega),rfl⟩
  rcases h with ⟨ha,hi⟩ | ⟨hi,ha⟩ <;> simp_all

 theorem valid_mono {F H : Finset (A × I)} (hFH : F ⊆ H) {C : Comp A I}
    (hC : C.IsPathOrCycle F) : C.IsPathOrCycle H := by
  refine ⟨hC.1,?_,hC.2.2⟩
  intro j hj
  obtain ⟨e,he,h⟩ := hC.2.1 j hj
  exact ⟨e,hFH he,h⟩

 theorem verts_incident [DecidableEq A] [DecidableEq I] {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) {x : A ⊕ I} (hx : x ∈ C.verts) :
    ∃ e ∈ F, x = Sum.inl e.1 ∨ x = Sum.inr e.2 := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
  have hlen := hC.1
  have hj' : j ≤ C.len := by simpa using Nat.le_of_lt_succ (mem_range.mp hj)
  by_cases hl : j < C.len
  · obtain ⟨e,he,hh⟩ := hC.2.1 j hl
    exact ⟨e,he,hh.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩
  · have heq : j = C.len := by omega
    obtain ⟨e,he,hh⟩ := hC.2.1 (j-1) (by omega)
    have hs : j-1+1 = j := by omega
    exact ⟨e,he,hh.elim (fun h => Or.inr (by simpa [hs] using h.2))
      (fun h => Or.inl (by simpa [hs] using h.2))⟩

 theorem twoMatching_mono [DecidableEq A] [DecidableEq I] {E F H : Finset (A × I)}
    (hF : IsTwoMatching E F) (hHF : H ⊆ F) : IsTwoMatching E H := by
  refine ⟨hHF.trans hF.1,?_,?_⟩
  · intro a; exact (card_le_card (filter_subset_filter _ hHF)).trans (hF.2.1 a)
  · intro i; exact (card_le_card (filter_subset_filter _ hHF)).trans (hF.2.2 i)

 theorem component_listing [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (E F : Finset (A × I)) (ht : IsTwoMatching E F) :
    ∃ L : List (Comp A I),
      (∀ C ∈ L, C.IsPathOrCycle F) ∧
      L.Pairwise (fun C D => Disjoint C.verts D.verts) ∧
      ∀ e ∈ F, ∃ C ∈ L, Occurs C e := by
  classical
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases hF : F = ∅
    · subst F; exact ⟨[],by simp,by simp,by simp⟩
    obtain ⟨C,hC,hclosed⟩ := exists_closed_component E F ht (nonempty_iff_ne_empty.mpr hF)
    let S := F.filter (Occurs C)
    let H := F \ S
    have hHF : H ⊆ F := sdiff_subset
    have hlt : H.card < F.card := by
      obtain ⟨e,he,hh⟩ := hC.2.1 0 (by have := hC.1; omega)
      have hS : e ∈ S := mem_filter.mpr ⟨he,0,by have := hC.1; omega,hh⟩
      apply card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hHF,fun heq => (mem_sdiff.mp (heq ▸ he)).2 hS⟩
    obtain ⟨L,hL,hpair,hcov⟩ := ih H.card (by omega) H (twoMatching_mono ht hHF) rfl
    have hd : ∀ D ∈ L, Disjoint C.verts D.verts := by
      intro D hD
      apply disjoint_left.mpr
      intro x hx hy
      obtain ⟨e,he,hh⟩ := verts_incident (hL D hD) hy
      have ho : Occurs C e := hclosed e (hHF he) (hh.elim
        (fun h => Or.inl (h ▸ hx)) (fun h => Or.inr (h ▸ hx)))
      exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨hHF he,ho⟩)
    refine ⟨C::L,?_,List.pairwise_cons.mpr ⟨hd,hpair⟩,?_⟩
    · intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact hC
      · exact valid_mono hHF (hL D hD)
    · intro e he
      by_cases ho : Occurs C e
      · exact ⟨C,by simp,ho⟩
      · obtain ⟨D,hD,hd⟩ := hcov e (mem_sdiff.mpr ⟨he,by simpa [S,he]⟩)
        exact ⟨D,List.mem_cons_of_mem C hD,hd⟩

 theorem coloring_exists [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
    (E F : Finset (A × I)) (ht : IsTwoMatching E F) :
    ∃ blue red : Finset (A × I), IsTSMColoring F blue red := by
  classical
  obtain ⟨L,hL,hpair,hcov⟩ := component_listing E F ht
  let C : Fin L.length → Comp A I := L.get
  let B := fun e => ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ (C k).BlueAt j
  let R := fun e => ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ ¬(C k).BlueAt j
  have hvalid : ∀ k, (C k).IsPathOrCycle F := fun k => hL _ (List.get_mem ..)
  refine ⟨F.filter B,F.filter R,L.length,C,hvalid,?_,?_,?_,?_⟩
  · intro k l hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hpair.rel_get_of_lt h
    · exact (hpair.rel_get_of_lt h).symm
  · intro e he
    obtain ⟨D,hD,j,hj,hh⟩ := hcov e he
    obtain ⟨k,rfl⟩ := List.get_of_mem hD
    exact ⟨k,j,hj,hh⟩
  · intro e
    change e ∈ F.filter B ↔ B e
    rw [mem_filter]
    constructor
    · exact And.right
    · intro h
      exact ⟨by obtain ⟨k,j,hj,hh,_⟩ := h; exact occurs_mem (hvalid k) ⟨j,hj,hh⟩,h⟩
  · intro e
    change e ∈ F.filter R ↔ R e
    rw [mem_filter]
    constructor
    · exact And.right
    · intro h
      exact ⟨by obtain ⟨k,j,hj,hh,_⟩ := h; exact occurs_mem (hvalid k) ⟨j,hj,hh⟩,h⟩
end Extraction
end TSMProof

open Finset OnlineStochMatching.TSM
namespace TSMProof
variable {A I : Type}

 theorem vertex_index_eq {F : Finset (A × I)} {C : Comp A I} (hC : C.IsPathOrCycle F)
    {j k : ℕ} (hj : j ≤ C.len) (hk : k ≤ C.len) (he : C.v j = C.v k) :
    j = k ∨ C.cyc = true ∧ ((j=0 ∧ k=C.len) ∨ (j=C.len ∧ k=0)) := by
  by_cases hc : C.cyc = true
  · have hh := hC.2.2
    simp only [hc,↓reduceIte] at hh
    by_cases hjl : j=C.len
    · by_cases hkl : k=C.len
      · left; omega
      · have h0 : C.v 0 = C.v k := by rw [← hh.2.1,← hjl]; exact he
        have hk0 := hh.2.2 0 (by omega) k (by omega) h0
        right; exact ⟨hc,Or.inr ⟨hjl,hk0.symm⟩⟩
    · by_cases hkl : k=C.len
      · have h0 : C.v j = C.v 0 := by rw [← hh.2.1,← hkl]; exact he
        have hj0 := hh.2.2 j (by omega) 0 (by omega) h0
        right; exact ⟨hc,Or.inl ⟨hj0,hkl⟩⟩
      · left; exact hh.2.2 j (by omega) k (by omega) he
  · left
    have hh := hC.2.2
    simp only [hc] at hh
    exact hh j hj k hk he

 theorem edge_index_unique {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) {j k : ℕ} (hj : j<C.len) (hk : k<C.len)
    {e : A × I} (he : C.HasEdgeAt j e) (hf : C.HasEdgeAt k e) : j=k := by
  have hlen := hC.1
  have hh : (C.v j=C.v k ∧ C.v (j+1)=C.v (k+1)) ∨
      (C.v j=C.v (k+1) ∧ C.v (j+1)=C.v k) := by
    rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases hf with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;>
      simp_all
  rcases hh with ⟨h,_⟩ | ⟨h1,h2⟩
  · have := vertex_index_eq hC (by omega) (by omega) h
    rcases this with h | ⟨_,h⟩ <;> omega
  · have hh1 := vertex_index_eq hC (by omega) (by omega) h1
    have hh2 := vertex_index_eq hC (by omega) (by omega) h2
    by_cases hc : C.cyc = true
    · have h4 : 4 ≤ C.len := (by simpa [hc] using hC.2.2 :
        4 ≤ C.len ∧ C.v C.len = C.v 0 ∧
        ∀ j₁ < C.len, ∀ j₂ < C.len, C.v j₁=C.v j₂ → j₁=j₂).1
      rcases hh1 with h | ⟨_,h⟩ <;> rcases hh2 with h' | ⟨_,h'⟩ <;> omega
    · have h1 := hh1.resolve_right (fun h => hc h.1)
      have h2 := hh2.resolve_right (fun h => hc h.1)
      omega

 noncomputable def componentEdge {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) (j : Fin C.len) : A × I := (hC.2.1 j j.isLt).choose
 theorem componentEdge_mem {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) (j : Fin C.len) : componentEdge hC j ∈ F :=
  (hC.2.1 j j.isLt).choose_spec.1
 theorem componentEdge_at {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) (j : Fin C.len) : C.HasEdgeAt j (componentEdge hC j) :=
  (hC.2.1 j j.isLt).choose_spec.2
 theorem componentEdge_injective {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) : Function.Injective (componentEdge hC) := by
  intro j k he
  apply Fin.ext
  exact edge_index_unique hC j.isLt k.isLt (componentEdge_at hC j)
    (by rw [he]; exact componentEdge_at hC k)
 theorem componentEdge_fst {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) (j : Fin C.len) (a : A) :
    (componentEdge hC j).1 = a ↔ C.v j = Sum.inl a ∨ C.v (j+1) = Sum.inl a := by
  rcases componentEdge_at hC j with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [h1,h2]
 theorem componentEdge_snd {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) (j : Fin C.len) (i : I) :
    (componentEdge hC j).2 = i ↔ C.v j = Sum.inr i ∨ C.v (j+1) = Sum.inr i := by
  rcases componentEdge_at hC j with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [h1,h2]

 theorem edge_component_unique [DecidableEq A] [DecidableEq I] {m : ℕ}
    (C : Fin m → Comp A I)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    {k l : Fin m} {e : A × I} (hk : Occurs (C k) e) (hl : Occurs (C l) e) : k=l := by
  by_contra hn
  exact disjoint_left.mp (hd k l hn) (occurs_verts hk).1 (occurs_verts hl).1

 theorem vertex_component_unique [DecidableEq A] [DecidableEq I] {m : ℕ}
    (C : Fin m → Comp A I)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    {k l : Fin m} {x : A ⊕ I} (hk : x ∈ (C k).verts) (hl : x ∈ (C l).verts) : k=l := by
  by_contra hn
  exact disjoint_left.mp (hd k l hn) hk hl

 theorem incident_index_iff {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) {r : ℕ} (hr : r ≤ C.len)
    (hcanon : C.cyc = true → r < C.len) {a : A} (ha : C.v r = Sum.inl a)
    (j : Fin C.len) : (componentEdge hC j).1 = a ↔
      j.val=r ∨ j.val+1=r ∨ (C.cyc=true ∧ r=0 ∧ j.val+1=C.len) := by
  rw [componentEdge_fst]
  constructor
  · rintro (h | h)
    · have hh := vertex_index_eq hC (Nat.le_of_lt j.isLt) hr (h.trans ha.symm)
      rcases hh with hh | ⟨hc,hh⟩
      · exact Or.inl hh
      · have := hcanon hc
        rcases hh with hh | hh <;> omega
    · have hh := vertex_index_eq hC (by omega) hr (h.trans ha.symm)
      rcases hh with hh | ⟨hc,hh⟩
      · exact Or.inr (Or.inl hh)
      · rcases hh with hh | hh
        · omega
        · exact Or.inr (Or.inr ⟨hc,hh.2,hh.1⟩)
  · rintro (h | h | ⟨hc,hr0,hend⟩)
    · left; simpa [h] using ha
    · right; simpa [h] using ha
    · right
      have hh := hC.2.2
      simp only [hc,↓reduceIte] at hh
      rw [hend,hh.2.1,← hr0]
      exact ha

 theorem listed_fiber_card [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) {a : A} (ha : Sum.inl a ∈ (C k).verts) :
    degA H a = (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).1 = a ∧ χ k j).card := by
  classical
  let J := univ.filter (fun j : Fin (C k).len => (componentEdge (hv k) j).1=a ∧ χ k j)
  have heq : H.filter (fun e => e.1=a) = J.image (componentEdge (hv k)) := by
    ext e
    constructor
    · intro he
      obtain ⟨he,hea⟩ := mem_filter.mp he
      obtain ⟨l,j,hj,hh,hχ⟩ := (hH e).mp he
      have hl : Sum.inl a ∈ (C l).verts := by
        simpa [hea] using (occurs_verts ⟨j,hj,hh⟩).1
      have hkl := vertex_component_unique C hd ha hl
      subst l
      have hedge : componentEdge (hv k) ⟨j,hj⟩ = e :=
        hasEdgeAt_unique (C k) j (componentEdge_at (hv k) ⟨j,hj⟩) hh
      exact mem_image.mpr ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,by simpa [hedge] using ⟨hea,hχ⟩⟩,hedge⟩
    · intro he
      obtain ⟨j,hj,rfl⟩ := mem_image.mp he
      obtain ⟨_,hea,hχ⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨(hH _).mpr ⟨k,j,j.isLt,componentEdge_at (hv k) j,hχ⟩,hea⟩
  change (H.filter _).card = J.card
  rw [heq,card_image_of_injective _ (componentEdge_injective (hv k))]

 theorem filter_fin_single (n r : ℕ) (hr : r<n) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun j : Fin n => j.val=r ∧ P j.val).card = if P r then 1 else 0 := by
  have he : (univ.filter fun j : Fin n => j.val=r ∧ P j.val) =
      ({⟨r,hr⟩} : Finset (Fin n)).filter (fun j => P j.val) := by
    ext j; simp [Fin.ext_iff]
  rw [he]
  by_cases h : P r <;> simp [filter_singleton,h]

 theorem filter_fin_pair (n r s : ℕ) (hr : r<n) (hs : s<n) (hne : r≠s)
    (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun j : Fin n => (j.val=r ∨ j.val=s) ∧ P j.val).card =
      (if P r then 1 else 0) + (if P s then 1 else 0) := by
  have he : (univ.filter fun j : Fin n => (j.val=r ∨ j.val=s) ∧ P j.val) =
      ({⟨r,hr⟩,⟨s,hs⟩} : Finset (Fin n)).filter (fun j => P j.val) := by
    ext j; simp [Fin.ext_iff]
  rw [he]
  by_cases h : P r <;> by_cases h' : P s <;> simp [filter_insert,filter_singleton,h,h',hne,Fin.ext_iff]

 theorem listed_degree_interior [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) {r : ℕ} (hr : 0<r) (hrl : r<(C k).len) {a : A}
    (ha : (C k).v r=Sum.inl a) :
    degA H a = (if χ k r then 1 else 0) + (if χ k (r-1) then 1 else 0) := by
  classical
  have hav : Sum.inl a ∈ (C k).verts := mem_image.mpr ⟨r,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).1=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => (j.val=r ∨ j.val=r-1) ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff (hv k) (by omega) (fun _ => hrl) ha]
    have : j.val+1=r ↔ j.val=r-1 := by omega
    simp [show r≠0 by omega,this]
  rw [he,filter_fin_pair _ _ _ hrl (by omega) (by omega)]

 theorem listed_degree_start [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) (hc : (C k).cyc=false) {a : A} (ha : (C k).v 0=Sum.inl a) :
    degA H a = if χ k 0 then 1 else 0 := by
  classical
  have hlen := (hv k).1
  have hav : Sum.inl a ∈ (C k).verts := mem_image.mpr ⟨0,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).1=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => j.val=0 ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff (hv k) (Nat.zero_le _) (by simp [hc]) ha]
    simp [hc]
  rw [he,filter_fin_single _ _ (by omega)]

 theorem listed_degree_end [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) (hc : (C k).cyc=false) {a : A} (ha : (C k).v (C k).len=Sum.inl a) :
    degA H a = if χ k ((C k).len-1) then 1 else 0 := by
  classical
  have hlen := (hv k).1
  have hav : Sum.inl a ∈ (C k).verts := mem_image.mpr ⟨(C k).len,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).1=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => j.val=(C k).len-1 ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff (hv k) le_rfl (by simp [hc]) ha]
    have : j.val+1=(C k).len ↔ j.val=(C k).len-1 := by omega
    simp [hc,show j.val≠(C k).len by omega,this]
  rw [he,filter_fin_single _ _ (by omega)]

 theorem listed_degree_cycle_start [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) (hc : (C k).cyc=true) {a : A} (ha : (C k).v 0=Sum.inl a) :
    degA H a = (if χ k 0 then 1 else 0) + (if χ k ((C k).len-1) then 1 else 0) := by
  classical
  have hlen : 4 ≤ (C k).len := (by simpa [hc] using (hv k).2.2 :
      4 ≤ (C k).len ∧ (C k).v (C k).len=(C k).v 0 ∧
      ∀ j₁ < (C k).len, ∀ j₂ < (C k).len, (C k).v j₁=(C k).v j₂ → j₁=j₂).1
  have hav : Sum.inl a ∈ (C k).verts := mem_image.mpr ⟨0,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).1=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => (j.val=0 ∨ j.val=(C k).len-1) ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff (hv k) (Nat.zero_le _) (fun _ => by omega) ha]
    have : j.val+1=(C k).len ↔ j.val=(C k).len-1 := by omega
    simp [hc,this]
  rw [he,filter_fin_pair _ _ _ (by omega) (by omega) (by omega)]
 theorem incident_index_iff_snd {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) {r : ℕ} (hr : r ≤ C.len)
    (hcanon : C.cyc = true → r < C.len) {a : I} (ha : C.v r = Sum.inr a)
    (j : Fin C.len) : (componentEdge hC j).2 = a ↔
      j.val=r ∨ j.val+1=r ∨ (C.cyc=true ∧ r=0 ∧ j.val+1=C.len) := by
  rw [componentEdge_snd]
  constructor
  · rintro (h | h)
    · have hh := vertex_index_eq hC (Nat.le_of_lt j.isLt) hr (h.trans ha.symm)
      rcases hh with hh | ⟨hc,hh⟩
      · exact Or.inl hh
      · have := hcanon hc
        rcases hh with hh | hh <;> omega
    · have hh := vertex_index_eq hC (by omega) hr (h.trans ha.symm)
      rcases hh with hh | ⟨hc,hh⟩
      · exact Or.inr (Or.inl hh)
      · rcases hh with hh | hh
        · omega
        · exact Or.inr (Or.inr ⟨hc,hh.2,hh.1⟩)
  · rintro (h | h | ⟨hc,hr0,hend⟩)
    · left; simpa [h] using ha
    · right; simpa [h] using ha
    · right
      have hh := hC.2.2
      simp only [hc,↓reduceIte] at hh
      rw [hend,hh.2.1,← hr0]
      exact ha

 theorem listed_fiber_card_snd [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) {a : I} (ha : Sum.inr a ∈ (C k).verts) :
    degI H a = (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).2 = a ∧ χ k j).card := by
  classical
  let J := univ.filter (fun j : Fin (C k).len => (componentEdge (hv k) j).2=a ∧ χ k j)
  have heq : H.filter (fun e => e.2=a) = J.image (componentEdge (hv k)) := by
    ext e
    constructor
    · intro he
      obtain ⟨he,hea⟩ := mem_filter.mp he
      obtain ⟨l,j,hj,hh,hχ⟩ := (hH e).mp he
      have hl : Sum.inr a ∈ (C l).verts := by
        simpa [hea] using (occurs_verts ⟨j,hj,hh⟩).2
      have hkl := vertex_component_unique C hd ha hl
      subst l
      have hedge : componentEdge (hv k) ⟨j,hj⟩ = e :=
        hasEdgeAt_unique (C k) j (componentEdge_at (hv k) ⟨j,hj⟩) hh
      exact mem_image.mpr ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,by simpa [hedge] using ⟨hea,hχ⟩⟩,hedge⟩
    · intro he
      obtain ⟨j,hj,rfl⟩ := mem_image.mp he
      obtain ⟨_,hea,hχ⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨(hH _).mpr ⟨k,j,j.isLt,componentEdge_at (hv k) j,hχ⟩,hea⟩
  change (H.filter _).card = J.card
  rw [heq,card_image_of_injective _ (componentEdge_injective (hv k))]

 theorem listed_degree_interior_snd [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) {r : ℕ} (hr : 0<r) (hrl : r<(C k).len) {a : I}
    (ha : (C k).v r=Sum.inr a) :
    degI H a = (if χ k r then 1 else 0) + (if χ k (r-1) then 1 else 0) := by
  classical
  have hav : Sum.inr a ∈ (C k).verts := mem_image.mpr ⟨r,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card_snd C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).2=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => (j.val=r ∨ j.val=r-1) ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff_snd (hv k) (by omega) (fun _ => hrl) ha]
    have : j.val+1=r ↔ j.val=r-1 := by omega
    simp [show r≠0 by omega,this]
  rw [he,filter_fin_pair _ _ _ hrl (by omega) (by omega)]

 theorem listed_degree_start_snd [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) (hc : (C k).cyc=false) {a : I} (ha : (C k).v 0=Sum.inr a) :
    degI H a = if χ k 0 then 1 else 0 := by
  classical
  have hlen := (hv k).1
  have hav : Sum.inr a ∈ (C k).verts := mem_image.mpr ⟨0,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card_snd C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).2=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => j.val=0 ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff_snd (hv k) (Nat.zero_le _) (by simp [hc]) ha]
    simp [hc]
  rw [he,filter_fin_single _ _ (by omega)]

 theorem listed_degree_end_snd [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) (hc : (C k).cyc=false) {a : I} (ha : (C k).v (C k).len=Sum.inr a) :
    degI H a = if χ k ((C k).len-1) then 1 else 0 := by
  classical
  have hlen := (hv k).1
  have hav : Sum.inr a ∈ (C k).verts := mem_image.mpr ⟨(C k).len,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card_snd C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).2=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => j.val=(C k).len-1 ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff_snd (hv k) le_rfl (by simp [hc]) ha]
    have : j.val+1=(C k).len ↔ j.val=(C k).len-1 := by omega
    simp [hc,show j.val≠(C k).len by omega,this]
  rw [he,filter_fin_single _ _ (by omega)]

 theorem listed_degree_cycle_start_snd [DecidableEq A] [DecidableEq I] {F H : Finset (A × I)}
    {m : ℕ} (C : Fin m → Comp A I) (hv : ∀ k, (C k).IsPathOrCycle F)
    (hd : ∀ k l, k≠l → Disjoint (C k).verts (C l).verts)
    (χ : Fin m → ℕ → Prop) [∀ k, DecidablePred (χ k)]
    (hH : ∀ e, e ∈ H ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ χ k j)
    (k : Fin m) (hc : (C k).cyc=true) {a : I} (ha : (C k).v 0=Sum.inr a) :
    degI H a = (if χ k 0 then 1 else 0) + (if χ k ((C k).len-1) then 1 else 0) := by
  classical
  have hlen : 4 ≤ (C k).len := (by simpa [hc] using (hv k).2.2 :
      4 ≤ (C k).len ∧ (C k).v (C k).len=(C k).v 0 ∧
      ∀ j₁ < (C k).len, ∀ j₂ < (C k).len, (C k).v j₁=(C k).v j₂ → j₁=j₂).1
  have hav : Sum.inr a ∈ (C k).verts := mem_image.mpr ⟨0,mem_range.mpr (by omega),ha⟩
  rw [listed_fiber_card_snd C hv hd χ hH k hav]
  have he : (univ.filter fun j : Fin (C k).len =>
      (componentEdge (hv k) j).2=a ∧ χ k j) =
      univ.filter (fun j : Fin (C k).len => (j.val=0 ∨ j.val=(C k).len-1) ∧ χ k j) := by
    ext j
    simp only [mem_filter,mem_univ,true_and]
    rw [incident_index_iff_snd (hv k) (Nat.zero_le _) (fun _ => by omega) ha]
    have : j.val+1=(C k).len ↔ j.val=(C k).len-1 := by omega
    simp [hc,this]
  rw [he,filter_fin_pair _ _ _ (by omega) (by omega) (by omega)]
end TSMProof

open Finset OnlineStochMatching.TSM
namespace TSMProof
variable {A I : Type} [DecidableEq A] [DecidableEq I]

structure ColoringData (F blue red : Finset (A × I)) where
  m : ℕ
  C : Fin m → Comp A I
  valid : ∀ k, (C k).IsPathOrCycle F
  disjoint : ∀ k l, k ≠ l → Disjoint (C k).verts (C l).verts
  cover : ∀ e ∈ F, ∃ k, Occurs (C k) e
  blue : ∀ e, e ∈ blue ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ (C k).BlueAt j
  red : ∀ e, e ∈ red ↔ ∃ k, ∃ j < (C k).len, (C k).HasEdgeAt j e ∧ ¬(C k).BlueAt j

 theorem coloring_data {F blue red : Finset (A × I)} (h : IsTSMColoring F blue red) :
    Nonempty (ColoringData F blue red) := by
  obtain ⟨m,C,hv,hd,hc,hb,hr⟩ := h
  exact ⟨⟨m,C,hv,hd,hc,hb,hr⟩⟩

namespace ColoringData
variable {F blue red : Finset (A × I)} (D : ColoringData F blue red)
 include D in
 theorem union_eq : blue ∪ red = F := by
  ext e
  rw [mem_union,D.blue,D.red]
  constructor
  · rintro (⟨k,j,hj,he,_⟩|⟨k,j,hj,he,_⟩) <;> exact occurs_mem (D.valid k) ⟨j,hj,he⟩
  · intro he
    obtain ⟨k,j,hj,hh⟩ := D.cover e he
    by_cases hb : (D.C k).BlueAt j
    · exact Or.inl ⟨k,j,hj,hh,hb⟩
    · exact Or.inr ⟨k,j,hj,hh,hb⟩
 include D in
 theorem disjoint_colors : Disjoint blue red := by
  apply disjoint_left.mpr
  intro e he hf
  obtain ⟨k,j,hj,hh,hb⟩ := (D.blue e).mp he
  obtain ⟨l,r,hr,hf,hn⟩ := (D.red e).mp hf
  have hkl := edge_component_unique D.C D.disjoint ⟨j,hj,hh⟩ ⟨r,hr,hf⟩
  subst l
  have hjr := edge_index_unique (D.valid k) hj hr hh hf
  exact hn (hjr ▸ hb)
 include D in
 theorem degA_sum (a : A) : degA F a = degA blue a + degA red a := by
  rw [← D.union_eq]
  simp only [degA,filter_union]
  apply card_union_of_disjoint
  exact D.disjoint_colors.mono (filter_subset _ _) (filter_subset _ _)
 include D in
 theorem degI_sum (i : I) : degI F i = degI blue i + degI red i := by
  rw [← D.union_eq]
  simp only [degI,filter_union]
  apply card_union_of_disjoint
  exact D.disjoint_colors.mono (filter_subset _ _) (filter_subset _ _)

 theorem vertex_index (k : Fin D.m) {x : A ⊕ I} (hx : x ∈ (D.C k).verts) :
    ∃ r, r ≤ (D.C k).len ∧ ((D.C k).cyc=true → r<(D.C k).len) ∧ (D.C k).v r=x := by
  obtain ⟨r,hr,hx⟩ := mem_image.mp hx
  have hr' : r ≤ (D.C k).len := by have := mem_range.mp hr; omega
  by_cases hc : (D.C k).cyc=true
  · have hh := (D.valid k).2.2
    simp only [hc,↓reduceIte] at hh
    by_cases hrl : r=(D.C k).len
    · refine ⟨0,by omega,fun _ => by omega,?_⟩
      rw [← hh.2.1,← hrl]; exact hx
    · exact ⟨r,hr',fun _ => by omega,hx⟩
  · exact ⟨r,hr',fun h => False.elim (hc h),hx⟩

 theorem advertiser_vertex {a : A} (ha : 0 < degA F a) :
    ∃ k r, r ≤ (D.C k).len ∧ ((D.C k).cyc=true → r<(D.C k).len) ∧
      (D.C k).v r=Sum.inl a := by
  obtain ⟨e,he⟩ := card_pos.mp ha
  obtain ⟨he,hea⟩ := mem_filter.mp he
  obtain ⟨k,hk⟩ := D.cover e he
  obtain ⟨r,hr,hcan,hv⟩ := D.vertex_index k (by simpa [hea] using (occurs_verts hk).1)
  exact ⟨k,r,hr,hcan,hv⟩

 theorem degree_pair (k : Fin D.m) {r : ℕ} (hr : r ≤ (D.C k).len)
    (hcan : (D.C k).cyc=true → r<(D.C k).len) {a : A} (ha : (D.C k).v r=Sum.inl a) :
    ((degA blue a=1 ∧ degA red a=0) ∨ (degA blue a=0 ∧ degA red a=1) ∨
      (degA blue a=1 ∧ degA red a=1) ∨ (degA blue a=2 ∧ degA red a=0)) ∧
    (degA blue a=0 → r=(D.C k).len ∧ (D.C k).cyc=false ∧ Even (D.C k).len) := by
  classical
  have hlen := (D.valid k).1
  by_cases h0 : r=0
  · subst r
    by_cases hc : (D.C k).cyc=true
    · have hb := listed_degree_cycle_start D.C D.valid D.disjoint
        (fun k j => (D.C k).BlueAt j) D.blue k hc ha
      have hred := listed_degree_cycle_start D.C D.valid D.disjoint
        (fun k j => ¬(D.C k).BlueAt j) D.red k hc ha
      have hh := Peer.component_cycle_wrap (D.C k) (D.valid k) hc
      simp only [hh.1,hh.2,↓reduceIte,not_true_eq_false,not_false_eq_true] at hb hred
      omega
    · have hc' : (D.C k).cyc=false := Bool.eq_false_iff.mpr hc
      have hb := listed_degree_start D.C D.valid D.disjoint
        (fun k j => (D.C k).BlueAt j) D.blue k hc' ha
      have hred := listed_degree_start D.C D.valid D.disjoint
        (fun k j => ¬(D.C k).BlueAt j) D.red k hc' ha
      have hh := Peer.component_blue_zero (D.C k)
      simp only [hh,↓reduceIte,not_true_eq_false] at hb hred
      omega
  by_cases he : r=(D.C k).len
  · have hc : (D.C k).cyc=false := Bool.eq_false_iff.mpr (fun h => by have := hcan h; omega)
    subst r
    have hb := listed_degree_end D.C D.valid D.disjoint
      (fun k j => (D.C k).BlueAt j) D.blue k hc ha
    have hred := listed_degree_end D.C D.valid D.disjoint
      (fun k j => ¬(D.C k).BlueAt j) D.red k hc ha
    have hp := Peer.component_last_blue (D.C k) (D.valid k) hc (by simp [ha])
    by_cases hblue : (D.C k).BlueAt ((D.C k).len-1)
    · simp only [hblue,↓reduceIte,not_true_eq_false] at hb hred
      omega
    · have heven : Even (D.C k).len := Nat.not_odd_iff_even.mp (fun h => hblue (hp.mpr h))
      simp only [hblue,↓reduceIte,not_false_eq_true] at hb hred
      exact ⟨Or.inr (Or.inl ⟨hb,hred⟩),fun _ => ⟨rfl,hc,heven⟩⟩
  · have hri : 0<r := by omega
    have hrl : r<(D.C k).len := by omega
    have hb := listed_degree_interior D.C D.valid D.disjoint
      (fun k j => (D.C k).BlueAt j) D.blue k hri hrl ha
    have hred := listed_degree_interior D.C D.valid D.disjoint
      (fun k j => ¬(D.C k).BlueAt j) D.red k hri hrl ha
    by_cases hex : (D.C k).IsEvenImpressionPath ∧ r=1
    · obtain ⟨hex,rfl⟩ := hex
      have hh := Peer.component_exception_blue (D.C k) hex
      simp only [hh.1,hh.2,Nat.sub_self,↓reduceIte,not_true_eq_false] at hb hred
      omega
    · have hh := Peer.component_blue_pair (D.C k) r hri hex
      by_cases hb' : (D.C k).BlueAt r <;> simp_all

 include D in
 theorem advertiser_cases (a : A) :
    (degA blue a=0 ∧ degA red a=0) ∨
    (degA blue a=1 ∧ degA red a=0) ∨ (degA blue a=0 ∧ degA red a=1) ∨
    (degA blue a=1 ∧ degA red a=1) ∨ (degA blue a=2 ∧ degA red a=0) := by
  by_cases h : 0 < degA F a
  · obtain ⟨k,r,hr,hcan,ha⟩ := D.advertiser_vertex h
    exact Or.inr (D.degree_pair k hr hcan ha).1
  · have := D.degA_sum a
    left; omega

 include D in
 theorem edge_class_count [Fintype A] :
    F.card = 2*(adsBR blue red).card + 2*(adsBB blue red).card +
      (adsB blue red).card + (adsR blue red).card := by
  classical
  have hf : F.card = ∑ a : A, degA F a :=
    card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=univ) (by simp)
  rw [hf]
  have hp : ∀ a : A, degA F a =
      2*(if a∈adsBR blue red then 1 else 0) +
      2*(if a∈adsBB blue red then 1 else 0) +
      (if a∈adsB blue red then 1 else 0) + (if a∈adsR blue red then 1 else 0) := by
    intro a
    rw [D.degA_sum]
    rcases D.advertiser_cases a with ⟨hb,hr⟩ | ⟨hb,hr⟩ | ⟨hb,hr⟩ | ⟨hb,hr⟩ | ⟨hb,hr⟩ <;>
      simp [adsBR,adsBB,adsB,adsR,hb,hr]
  simp_rw [hp]
  simp [sum_add_distrib,Nat.mul_comm]

 theorem start_ad_B [Fintype A] (k : Fin D.m) (hc : (D.C k).cyc=false)
    {a : A} (ha : (D.C k).v 0=Sum.inl a) : a ∈ adsB blue red := by
  classical
  have hb := listed_degree_start D.C D.valid D.disjoint
    (fun k j => (D.C k).BlueAt j) D.blue k hc ha
  have hr := listed_degree_start D.C D.valid D.disjoint
    (fun k j => ¬(D.C k).BlueAt j) D.red k hc ha
  have hh := Peer.component_blue_zero (D.C k)
  simp only [hh,↓reduceIte,not_true_eq_false] at hb hr
  simp [adsB,hb,hr]

 theorem end_ad_B [Fintype A] (k : Fin D.m) (hc : (D.C k).cyc=false)
    (ho : Odd (D.C k).len) {a : A} (ha : (D.C k).v (D.C k).len=Sum.inl a) :
    a ∈ adsB blue red := by
  classical
  have hb := listed_degree_end D.C D.valid D.disjoint
    (fun k j => (D.C k).BlueAt j) D.blue k hc ha
  have hr := listed_degree_end D.C D.valid D.disjoint
    (fun k j => ¬(D.C k).BlueAt j) D.red k hc ha
  have hh := (Peer.component_last_blue (D.C k) (D.valid k) hc (by simp [ha])).mpr ho
  simp only [hh,↓reduceIte,not_true_eq_false] at hb hr
  simp [adsB,hb,hr]

 theorem exception_ad_BB [Fintype A] (k : Fin D.m) (hex : (D.C k).IsEvenImpressionPath)
    {a : A} (ha : (D.C k).v 1=Sum.inl a) : a ∈ adsBB blue red := by
  classical
  have hlen := (D.valid k).1
  have he := hex.2.1
  rw [Nat.even_iff] at he
  have hb := listed_degree_interior D.C D.valid D.disjoint
    (fun k j => (D.C k).BlueAt j) D.blue k (by omega : 0<1) (by omega) ha
  have hr := listed_degree_interior D.C D.valid D.disjoint
    (fun k j => ¬(D.C k).BlueAt j) D.red k (by omega : 0<1) (by omega) ha
  have hh := Peer.component_exception_blue (D.C k) hex
  simp only [Nat.sub_self,hh.1,hh.2,↓reduceIte,not_true_eq_false] at hb hr
  simp [adsBB,hb,hr]

 theorem red_partner [Fintype A] {a : A} (ha : a ∈ adsR blue red) :
    ∃ b ∈ adsB blue red, ∃ k, (D.C k).v (D.C k).len=Sum.inl a ∧ (D.C k).v 0=Sum.inl b := by
  have had : degA blue a=0 ∧ degA red a=1 := by simpa [adsR] using ha
  have hpos : 0<degA F a := by rw [D.degA_sum,had.1,had.2]; omega
  obtain ⟨k,r,hr,hcan,hva⟩ := D.advertiser_vertex hpos
  obtain ⟨he,hc,heven⟩ := (D.degree_pair k hr hcan hva).2 had.1
  subst r
  have hp := Peer.component_side_parity (D.C k) (D.valid k) (D.C k).len le_rfl
  have hstart : ((D.C k).v 0).isRight=false := by simpa [hva,heven] using hp
  obtain ⟨b,hb⟩ : ∃ b : A, (D.C k).v 0=Sum.inl b := by
    cases h : (D.C k).v 0 with
    | inl b => exact ⟨b,rfl⟩
    | inr i => simp [h] at hstart
  exact ⟨b,D.start_ad_B k hc hb,k,hva,hb⟩

 include D in
 theorem red_le_blue [Fintype A] : (adsR blue red).card ≤ (adsB blue red).card := by
  classical
  let f : {a // a∈adsR blue red} → {b // b∈adsB blue red} := fun a =>
    ⟨(D.red_partner a.property).choose,(D.red_partner a.property).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro a a' heq
    have hb : (f a).val=(f a').val := congrArg Subtype.val heq
    obtain ⟨k,hka,hkb⟩ := (D.red_partner a.property).choose_spec.2
    obtain ⟨l,hla,hlb⟩ := (D.red_partner a'.property).choose_spec.2
    have hk : Sum.inl (f a).val ∈ (D.C k).verts :=
      mem_image.mpr ⟨0,mem_range.mpr (by have := (D.valid k).1; omega),hkb⟩
    have hl : Sum.inl (f a').val ∈ (D.C l).verts :=
      mem_image.mpr ⟨0,mem_range.mpr (by have := (D.valid l).1; omega),hlb⟩
    have hkl := vertex_component_unique D.C D.disjoint hk (by simpa [hb] using hl)
    subst l
    apply Subtype.ext
    exact Sum.inl.inj (hka.symm.trans hla)
  simpa using Fintype.card_le_of_injective f hf

 theorem path_witness [Fintype A] (k : Fin D.m) (hc : (D.C k).cyc=false) :
    ∃ a, (a ∈ adsB blue red ∨ a ∈ adsBB blue red) ∧ Sum.inl a ∈ (D.C k).verts := by
  have hlen := (D.valid k).1
  cases hstart : (D.C k).v 0 with
  | inl a =>
    exact ⟨a,Or.inl (D.start_ad_B k hc hstart),
      mem_image.mpr ⟨0,mem_range.mpr (by omega),hstart⟩⟩
  | inr i =>
    by_cases he : Even (D.C k).len
    · have hex : (D.C k).IsEvenImpressionPath := ⟨hc,he,by simp [hstart]⟩
      have hh := Peer.component_exception_is_advertiser (D.C k) (D.valid k) hex
      cases h : (D.C k).v 1 with
      | inr j => simp [h] at hh
      | inl a => exact ⟨a,Or.inr (D.exception_ad_BB k hex h),
          mem_image.mpr ⟨1,mem_range.mpr (by omega),h⟩⟩
    · have ho := Nat.not_even_iff_odd.mp he
      have hp := Peer.component_side_parity (D.C k) (D.valid k) (D.C k).len le_rfl
      have hh : ((D.C k).v (D.C k).len).isRight=false := by simpa [he,hstart] using hp
      cases h : (D.C k).v (D.C k).len with
      | inr j => simp [h] at hh
      | inl a => exact ⟨a,Or.inl (D.end_ad_B k hc ho h),
          mem_image.mpr ⟨(D.C k).len,mem_range.mpr (by omega),h⟩⟩

 theorem paths_le_good [Fintype A] :
    (univ.filter fun k : Fin D.m => (D.C k).cyc=false).card ≤
      (adsB blue red).card + (adsBB blue red).card := by
  classical
  let P := univ.filter (fun k : Fin D.m => (D.C k).cyc=false)
  let G := adsB blue red ∪ adsBB blue red
  let f : {k // k∈P} → {a // a∈G} := fun k =>
    ⟨(D.path_witness k.val (mem_filter.mp k.property).2).choose,
      mem_union.mpr (D.path_witness k.val (mem_filter.mp k.property).2).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro k l heq
    apply Subtype.ext
    have hk := (D.path_witness k.val (mem_filter.mp k.property).2).choose_spec.2
    have hl := (D.path_witness l.val (mem_filter.mp l.property).2).choose_spec.2
    have he : (f k).val=(f l).val := congrArg Subtype.val heq
    change Sum.inl (f k).val ∈ (D.C k.val).verts at hk
    change Sum.inl (f l).val ∈ (D.C l.val).verts at hl
    rw [← he] at hl
    exact vertex_component_unique D.C D.disjoint hk hl
  have hh : P.card ≤ G.card := by simpa using Fintype.card_le_of_injective f hf
  exact hh.trans (card_union_le _ _)
end ColoringData
end TSMProof

open Finset OnlineStochMatching.TSM
namespace TSMProof.ColoringData
variable {A I : Type} [DecidableEq A] [DecidableEq I]
variable {F blue red : Finset (A × I)} (D : ColoringData F blue red)

 theorem impression_vertex {i : I} (hi : 0 < degI F i) :
    ∃ k r, r ≤ (D.C k).len ∧ ((D.C k).cyc=true → r<(D.C k).len) ∧
      (D.C k).v r=Sum.inr i := by
  obtain ⟨e,he⟩ := card_pos.mp hi
  obtain ⟨he,hei⟩ := mem_filter.mp he
  obtain ⟨k,hk⟩ := D.cover e he
  obtain ⟨r,hr,hcan,hv⟩ := D.vertex_index k (by simpa [hei] using (occurs_verts hk).2)
  exact ⟨k,r,hr,hcan,hv⟩

 theorem impression_degree_pair (k : Fin D.m) {r : ℕ} (hr : r ≤ (D.C k).len)
    (hcan : (D.C k).cyc=true → r<(D.C k).len) {i : I} (ha : (D.C k).v r=Sum.inr i) :
    degI blue i=1 ∧ degI red i≤1 := by
  classical
  have hlen := (D.valid k).1
  by_cases h0 : r=0
  · subst r
    by_cases hc : (D.C k).cyc=true
    · have hb := listed_degree_cycle_start_snd D.C D.valid D.disjoint
        (fun k j => (D.C k).BlueAt j) D.blue k hc ha
      have hred := listed_degree_cycle_start_snd D.C D.valid D.disjoint
        (fun k j => ¬(D.C k).BlueAt j) D.red k hc ha
      have hh := Peer.component_cycle_wrap (D.C k) (D.valid k) hc
      simp only [hh.1,hh.2,↓reduceIte,not_true_eq_false,not_false_eq_true] at hb hred
      omega
    · have hc' : (D.C k).cyc=false := Bool.eq_false_iff.mpr hc
      have hb := listed_degree_start_snd D.C D.valid D.disjoint
        (fun k j => (D.C k).BlueAt j) D.blue k hc' ha
      have hred := listed_degree_start_snd D.C D.valid D.disjoint
        (fun k j => ¬(D.C k).BlueAt j) D.red k hc' ha
      have hh := Peer.component_blue_zero (D.C k)
      simp only [hh,↓reduceIte,not_true_eq_false] at hb hred
      omega
  by_cases he : r=(D.C k).len
  · have hc : (D.C k).cyc=false := Bool.eq_false_iff.mpr (fun h => by have := hcan h; omega)
    subst r
    have hb := listed_degree_end_snd D.C D.valid D.disjoint
      (fun k j => (D.C k).BlueAt j) D.blue k hc ha
    have hred := listed_degree_end_snd D.C D.valid D.disjoint
      (fun k j => ¬(D.C k).BlueAt j) D.red k hc ha
    have hh := Peer.component_last_impression_blue (D.C k) (D.valid k) hc (by simp [ha])
    simp only [hh,↓reduceIte,not_true_eq_false] at hb hred
    omega
  · have hri : 0<r := by omega
    have hrl : r<(D.C k).len := by omega
    have hb := listed_degree_interior_snd D.C D.valid D.disjoint
      (fun k j => (D.C k).BlueAt j) D.blue k hri hrl ha
    have hred := listed_degree_interior_snd D.C D.valid D.disjoint
      (fun k j => ¬(D.C k).BlueAt j) D.red k hri hrl ha
    have hex : ¬((D.C k).IsEvenImpressionPath ∧ r=1) := by
      rintro ⟨hex,rfl⟩
      have hh := Peer.component_exception_is_advertiser (D.C k) (D.valid k) hex
      simp [ha] at hh
    have hh := Peer.component_blue_pair (D.C k) r hri hex
    by_cases hb' : (D.C k).BlueAt r <;> simp_all

 include D in
 theorem impression_bounds (i : I) : degI blue i≤1 ∧ degI red i≤degI blue i := by
  by_cases h : 0<degI F i
  · obtain ⟨k,r,hr,hcan,hv⟩ := D.impression_vertex h
    have := D.impression_degree_pair k hr hcan hv
    omega
  · have := D.degI_sum i
    omega

 include D in
 theorem total_edges_bound [Fintype I] : F.card ≤ 2*Fintype.card I := by
  have hf : F.card = ∑ i : I, degI F i :=
    card_eq_sum_card_fiberwise (f:=Prod.snd) (t:=univ) (by simp)
  rw [hf]
  have hh : ∀ i : I, degI F i≤2 := by
    intro i
    have := D.impression_bounds i
    rw [D.degI_sum]
    omega
  calc
    (∑ i : I, degI F i) ≤ ∑ _i : I, 2 := sum_le_sum (fun i _ => hh i)
    _ = 2*Fintype.card I := by simp [Nat.mul_comm]

 include D in
 theorem class_card_bound [Fintype A] [Fintype I] :
    (adsBR blue red).card + (adsBB blue red).card + (adsB blue red).card +
      (adsR blue red).card ≤ 2*Fintype.card I := by
  have h1 := D.edge_class_count
  have h2 := D.total_edges_bound
  omega
end TSMProof.ColoringData


open Finset OnlineStochMatching.TSM
namespace TSMProof

structure DPath {V : Type} (R : V → V → Prop) (S : V → Prop) (t : V) where
  len : ℕ
  v : ℕ → V
  start : S (v 0)
  finish : v len = t
  edge : ∀ j < len, R (v j) (v (j+1))

namespace DPath
variable {V : Type} {R : V → V → Prop} {S : V → Prop} {t u : V}
def single (h : S t) : DPath R S t := ⟨0,fun _ => t,h,rfl,by omega⟩
def append (p : DPath R S t) (h : R t u) : DPath R S u where
  len := p.len+1
  v j := if j ≤ p.len then p.v j else u
  start := by simpa using p.start
  finish := by simp
  edge := by
    intro j hj
    by_cases he : j = p.len
    · subst j; simpa [p.finish] using h
    · have hj' : j < p.len := by omega
      simpa [Nat.le_of_lt hj',show j+1 ≤ p.len by omega] using p.edge j hj'

def cut (p : DPath R S t) {a b : ℕ} (hab : a < b) (hb : b ≤ p.len)
    (he : p.v a = p.v b) : DPath R S t where
  len := p.len-(b-a)
  v j := if j < a then p.v j else p.v (j+(b-a))
  start := by
    by_cases ha : a = 0
    · subst a; simpa using he ▸ p.start
    · simpa [show 0 < a by omega] using p.start
  finish := by
    have hlen : a ≤ p.len-(b-a) := by omega
    simp only [not_lt.mpr hlen,↓reduceIte]
    rw [show p.len-(b-a)+(b-a) = p.len by omega]
    exact p.finish
  edge := by
    intro j hj
    by_cases ha : j+1 < a
    · simp only [ha,show j < a by omega,↓reduceIte]
      exact p.edge j (by omega)
    by_cases heq : j+1 = a
    · simp only [show j < a by omega,ha,↓reduceIte]
      have hs : j+1+(b-a) = b := by omega
      rw [hs,← he,← heq]
      exact p.edge j (by omega)
    · simp only [show ¬j < a by omega,ha,↓reduceIte]
      convert p.edge (j+(b-a)) (by omega) using 1; congr 1; omega

 theorem exists_simple (h : Nonempty (DPath R S t)) :
    ∃ p : DPath R S t, ∀ a ≤ p.len, ∀ b ≤ p.len, p.v a = p.v b → a = b := by
  classical
  let Q := fun n => ∃ p : DPath R S t, p.len = n
  have hex : ∃ n, Q n := by obtain ⟨p⟩ := h; exact ⟨p.len,p,rfl⟩
  obtain ⟨p,hp⟩ := Nat.find_spec hex
  refine ⟨p,?_⟩
  intro a ha b hb he
  by_contra hn
  wlog hab : a < b generalizing a b
  · exact this b hb a ha he.symm (Ne.symm hn) (by omega)
  have hc := Nat.find_min' hex (show Q (p.cut hab hb he).len from ⟨_,rfl⟩)
  change Nat.find hex ≤ p.len-(b-a) at hc
  omega
end DPath

variable {A I : Type} [DecidableEq A]
def residual (E F : Finset (A × I)) : (A ⊕ I) → (A ⊕ I) → Prop
  | .inl a, .inr i => (a,i) ∈ E ∧ (a,i) ∉ F
  | .inr i, .inl a => (a,i) ∈ F
  | _, _ => False

def source (F : Finset (A × I)) : (A ⊕ I) → Prop
  | .inl a => degA F a < 2
  | .inr _ => False

 theorem reach_path {E F : Finset (A × I)} {x : A ⊕ I} (h : Reach E F x) :
    Nonempty (DPath (residual E F) (source F) x) := by
  induction h with
  | source a ha => exact ⟨DPath.single ha⟩
  | forward a i _ he hf ih => obtain ⟨p⟩ := ih; exact ⟨p.append ⟨he,hf⟩⟩
  | backward a i _ hf ih => obtain ⟨p⟩ := ih; exact ⟨p.append hf⟩

 theorem reachable_simple_path {E F : Finset (A × I)} {x : A ⊕ I} (h : Reach E F x) :
    ∃ p : DPath (residual E F) (source F) x,
      ∀ a ≤ p.len, ∀ b ≤ p.len, p.v a = p.v b → a = b :=
  DPath.exists_simple (reach_path h)

section Update
variable [DecidableEq I]
 theorem degA_insert {F : Finset (A × I)} {a : A} {i : I} (hn : (a,i) ∉ F) (b : A) :
    degA (insert (a,i) F) b = degA F b + if a=b then 1 else 0 := by
  classical
  by_cases h : a=b
  · subst b; simp [degA,filter_insert,hn]
  · simp [degA,filter_insert,h]
 theorem degI_insert {F : Finset (A × I)} {a : A} {i : I} (hn : (a,i) ∉ F) (j : I) :
    degI (insert (a,i) F) j = degI F j + if i=j then 1 else 0 := by
  classical
  by_cases h : i=j
  · subst j; simp [degI,filter_insert,hn]
  · simp [degI,filter_insert,h]
 theorem degA_erase {F : Finset (A × I)} {a : A} {i : I} (he : (a,i) ∈ F) (b : A) :
    degA (F.erase (a,i)) b = degA F b - if a=b then 1 else 0 := by
  classical
  by_cases h : a=b
  · subst b; simp [degA,filter_erase,he]
  · simp [degA,filter_erase,h,show (a,i) ∉ F.filter (fun e => e.1=b) by simp [h]]
 theorem degI_erase {F : Finset (A × I)} {a : A} {i : I} (he : (a,i) ∈ F) (j : I) :
    degI (F.erase (a,i)) j = degI F j - if i=j then 1 else 0 := by
  classical
  by_cases h : i=j
  · subst j; simp [degI,filter_erase,he]
  · simp [degI,filter_erase,h,show (a,i) ∉ F.filter (fun e => e.2=j) by simp [h]]
 omit [DecidableEq I] in
 theorem edge_degA_pos {F : Finset (A × I)} {a : A} {i : I} (he : (a,i) ∈ F) :
    0 < degA F a := card_pos.mpr ⟨(a,i),by simp [he]⟩
 omit [DecidableEq A] in
 theorem edge_degI_pos {F : Finset (A × I)} {a : A} {i : I} (he : (a,i) ∈ F) :
    0 < degI F i := card_pos.mpr ⟨(a,i),by simp [he]⟩

 theorem flow_add {E F : Finset (A × I)} (ht : IsTwoMatching E F)
    {a : A} {i : I} (he : (a,i) ∈ E) (hn : (a,i) ∉ F)
    (ha : degA F a < 2) (hi : degI F i < 2) :
    IsTwoMatching E (insert (a,i) F) ∧ (insert (a,i) F).card = F.card+1 := by
  refine ⟨⟨insert_subset he ht.1,?_,?_⟩,card_insert_of_notMem hn⟩
  · intro b; rw [degA_insert hn]; split_ifs with h
    · subst b; omega
    · simpa using ht.2.1 b
  · intro j; rw [degI_insert hn]; split_ifs with h
    · subst j; omega
    · simpa using ht.2.2 j

 theorem flow_exchange {E F : Finset (A × I)} (ht : IsTwoMatching E F)
    {a b : A} {i : I} (he : (a,i) ∈ E) (hn : (a,i) ∉ F)
    (hb : (b,i) ∈ F) (ha : degA F a < 2) :
    let H := insert (a,i) (F.erase (b,i))
    IsTwoMatching E H ∧ H.card = F.card ∧ degA H b < 2 ∧
      ∀ j, j ≠ i → degI H j = degI F j := by
  have hab : a ≠ b := by rintro rfl; exact hn hb
  have hnew : (a,i) ∉ F.erase (b,i) := notMem_mono (erase_subset _ _) hn
  have hp := edge_degA_pos hb
  have hpi := edge_degI_pos hb
  dsimp only
  refine ⟨⟨insert_subset he ((erase_subset _ _).trans ht.1),?_,?_⟩,?_,?_,?_⟩
  · intro c
    rw [degA_insert hnew,degA_erase hb]
    have := ht.2.1 c
    split_ifs <;> subst_vars <;> omega
  · intro j
    rw [degI_insert hnew,degI_erase hb]
    have := ht.2.2 j
    split_ifs <;> subst_vars <;> omega
  · rw [card_insert_of_notMem hnew,card_erase_of_mem hb]
    have := card_pos.mpr ⟨(b,i),hb⟩
    omega
  · rw [degA_insert hnew,degA_erase hb]
    simp only [hab,↓reduceIte,Nat.add_zero]
    have := ht.2.1 b
    omega
  · intro j hj
    rw [degI_insert hnew,degI_erase hb]
    simp [Ne.symm hj]

 theorem residual_exchange_away (E F : Finset (A × I)) (a b : A) (i : I)
    {x y : A ⊕ I} (hx : x ≠ Sum.inr i) (hy : y ≠ Sum.inr i)
    (h : residual E F x y) : residual E (insert (a,i) (F.erase (b,i))) x y := by
  cases x <;> cases y <;> simp_all [residual,mem_insert,mem_erase]

 theorem augment_path (E : Finset (A × I)) : ∀ n : ℕ,
    ∀ (F : Finset (A × I)), IsTwoMatching E F → ∀ (i : I)
      (p : DPath (residual E F) (source F) (Sum.inr i)), p.len = n →
      (∀ a ≤ p.len, ∀ b ≤ p.len, p.v a = p.v b → a = b) →
      degI F i < 2 → ∃ H, IsTwoMatching E H ∧ F.card < H.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F ht i p hn hs hi
    have hstart := p.start
    obtain ⟨a,ha⟩ : ∃ a : A, p.v 0 = Sum.inl a := by
      cases h : p.v 0 with
      | inl a => exact ⟨a,rfl⟩
      | inr i => simp [source,h] at hstart
    have hda : degA F a < 2 := by simpa [source,ha] using hstart
    have hp : 0 < p.len := by
      by_contra h
      have hh : p.len = 0 := by omega
      have := p.finish
      simp [hh,ha] at this
    have h01 := p.edge 0 hp
    obtain ⟨j,hj⟩ : ∃ j : I, p.v 1 = Sum.inr j := by
      cases h : p.v 1 with
      | inl b => simp [residual,ha,h] at h01
      | inr j => exact ⟨j,rfl⟩
    have hnew : (a,j) ∈ E ∧ (a,j) ∉ F := by simpa [residual,ha,hj] using h01
    by_cases hlen : p.len = 1
    · have hji : j = i := by have := p.finish; simpa [hlen,hj] using this
      subst j
      obtain ⟨hm,hcard⟩ := flow_add ht hnew.1 hnew.2 hda hi
      exact ⟨_,hm,by omega⟩
    have hlong : 2 ≤ p.len := by omega
    have h12 := p.edge 1 (by omega)
    obtain ⟨b,hb⟩ : ∃ b : A, p.v 2 = Sum.inl b := by
      cases h : p.v 2 with
      | inl b => exact ⟨b,rfl⟩
      | inr j' => simp [residual,hj,h] at h12
    have hold : (b,j) ∈ F := by simpa [residual,hj,hb] using h12
    let H := insert (a,j) (F.erase (b,j))
    obtain ⟨hH,hcard,hdb,hdeg⟩ := flow_exchange ht hnew.1 hnew.2 hold hda
    have hij : i ≠ j := by
      intro heq
      have := hs p.len (le_refl _) 1 (by omega) (by rw [p.finish,hj,heq])
      omega
    have havoid : ∀ k, 2 ≤ k → k ≤ p.len → p.v k ≠ Sum.inr j := by
      intro k hk hkl heq
      have := hs k hkl 1 (by omega) (by rw [heq,hj])
      omega
    let q : DPath (residual E H) (source H) (Sum.inr i) := {
      len := p.len-2
      v := fun k => p.v (k+2)
      start := by simpa [source,hb] using hdb
      finish := by simpa [Nat.sub_add_cancel hlong] using p.finish
      edge := by
        intro k hk
        have hk' : k+2 < p.len := by omega
        have hh := residual_exchange_away E F a b j
          (havoid (k+2) (by omega) (by omega))
          (havoid (k+2+1) (by omega) (by omega)) (p.edge (k+2) hk')
        simpa [H,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh }
    have hq : ∀ a ≤ q.len, ∀ b ≤ q.len, q.v a = q.v b → a=b := by
      intro x hx y hy hxy
      have hh := hs (x+2) (by change x ≤ p.len-2 at hx; omega)
        (y+2) (by change y ≤ p.len-2 at hy; omega) hxy
      omega
    obtain ⟨K,hK,hKcard⟩ := ih q.len (by dsimp [q]; omega) H hH i q rfl hq
      (by rw [hdeg i hij]; exact hi)
    change H.card = F.card at hcard
    exact ⟨K,hK,by omega⟩

 theorem reachable_impression_saturated {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {i : I} (hi : Reach E F (Sum.inr i)) : degI F i = 2 := by
  have hle := hF.1.2.2 i
  by_contra hn
  obtain ⟨p,hp⟩ := reachable_simple_path hi
  obtain ⟨H,hH,hcard⟩ := augment_path E p.len F hF.1 i p rfl hp (by omega)
  have := hF.2 H hH
  omega
end Update

section Cut
variable [Fintype A] [Fintype I] [DecidableEq I]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem mem_cutAS (E F : Finset (A × I)) (a : A) :
    a ∈ cutAS E F ↔ Reach E F (Sum.inl a) := by simp [cutAS]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem mem_cutAT (E F : Finset (A × I)) (a : A) :
    a ∈ cutAT E F ↔ ¬Reach E F (Sum.inl a) := by simp [cutAT]
@[simp] theorem mem_cutIT (E F : Finset (A × I)) (i : I) :
    i ∈ cutIT E F ↔ ¬(Reach E F (Sum.inr i) ∨
      2 ≤ ((cutAS E F).filter fun a => (a,i) ∈ E).card) := by
  classical
  simp only [cutIT,mem_sdiff,mem_univ,true_and,cutIS,mem_filter]
  apply not_congr
  apply or_congr Iff.rfl
  apply Iff.of_eq
  congr 2
  ext a
  simp

 theorem crossing_subset_flow (E F : Finset (A × I)) : Edelta E F ⊆ F := by
  intro e he
  obtain ⟨he,ha,hi⟩ := mem_filter.mp he
  by_contra hn
  exact ((mem_cutIT E F e.2).mp hi) (Or.inl (Reach.forward _ _ (by simpa using ha) he hn))

 omit [Fintype I] in
 theorem cutAT_saturated {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {a : A} (ha : a ∈ cutAT E F) : degA F a = 2 := by
  have hl := hF.1.2.1 a
  by_contra hn
  exact (mem_cutAT E F a).mp ha (Reach.source a (by omega))

 theorem cutIS_saturated_neighbors {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {i : I} (hi : i ∈ cutIS E F) :
    degI F i = 2 ∧ ∀ a, (a,i) ∈ F → a ∈ cutAS E F := by
  classical
  have hi' : Reach E F (Sum.inr i) ∨
      2 ≤ ((cutAS E F).filter fun a => (a,i) ∈ E).card := by
    convert (mem_filter.mp hi).2 using 2; congr 2
  by_cases hr : Reach E F (Sum.inr i)
  · exact ⟨reachable_impression_saturated hF hr,fun a ha => by
      simpa using Reach.backward a i hr ha⟩
  have htwo := hi'.resolve_left hr
  let S := ((cutAS E F).filter fun a => (a,i) ∈ E).image (fun a => (a,i))
  have hS : S ⊆ F.filter (fun e => e.2=i) := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨ha,he⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨?_,rfl⟩
    by_contra hn
    exact hr (Reach.forward a i (by simpa using ha) he hn)
  have hcard : S.card = ((cutAS E F).filter fun a => (a,i) ∈ E).card := by
    apply card_image_of_injective
    intro a b h; exact congrArg Prod.fst h
  have heq : S = F.filter (fun e => e.2=i) := eq_of_subset_of_card_le hS (by
    have hh := hF.1.2.2 i
    change (F.filter (fun e => e.2=i)).card ≤ 2 at hh
    omega)
  refine ⟨?_,?_⟩
  · have hle := hF.1.2.2 i
    change (F.filter (fun e => e.2=i)).card = 2
    rw [← heq]
    change (F.filter (fun e => e.2=i)).card ≤ 2 at hle
    rw [← heq] at hle
    omega
  · intro a ha
    have hm : (a,i) ∈ S := heq ▸ mem_filter.mpr ⟨ha,rfl⟩
    obtain ⟨b,hb,hba⟩ := mem_image.mp hm
    have : b=a := congrArg Prod.fst hba
    subst b
    exact (mem_filter.mp hb).1

 theorem crossing_injective_snd (E F : Finset (A × I)) :
    Set.InjOn Prod.snd (Edelta E F : Set (A × I)) := by
  intro e he f hf hef
  obtain ⟨heE,hea,hei⟩ := mem_filter.mp he
  obtain ⟨hfE,hfa,hfi⟩ := mem_filter.mp hf
  have hn := (mem_cutIT E F e.2).mp hei
  have hcard : ((cutAS E F).filter fun a => (a,e.2) ∈ E).card ≤ 1 := by omega
  have hmem1 : e.1 ∈ (cutAS E F).filter (fun a => (a,e.2) ∈ E) := mem_filter.mpr ⟨hea,by simpa using heE⟩
  have hmem2 : f.1 ∈ (cutAS E F).filter (fun a => (a,e.2) ∈ E) :=
    mem_filter.mpr ⟨hfa,by simpa [hef] using hfE⟩
  have hh := card_le_one.mp hcard _ hmem1 _ hmem2
  exact Prod.ext hh hef

 theorem crossing_injective_fst {E F : Finset (A × I)} (hF : IsMaxFlowSet E F) :
    Set.InjOn Prod.fst (Edelta E F : Set (A × I)) := by
  intro e he f hf hef
  have heF := crossing_subset_flow E F he
  have hfF := crossing_subset_flow E F hf
  obtain ⟨_,hea,hei⟩ := mem_filter.mp he
  obtain ⟨_,_,hfi⟩ := mem_filter.mp hf
  have hr : Reach E F (Sum.inl e.1) := by simpa using hea
  have hind : e.2 = f.2 := by
    cases hr with
    | source a ha =>
      have hcard : (F.filter (fun g => g.1=e.1)).card ≤ 1 := by change degA F e.1 ≤ 1; omega
      have hh := card_le_one.mp hcard _ (mem_filter.mpr ⟨heF,rfl⟩)
        _ (mem_filter.mpr ⟨hfF,hef.symm⟩)
      exact congrArg Prod.snd hh
    | backward a i hi hai =>
      have hine : i ≠ e.2 := by
        intro h; subst i
        exact ((mem_cutIT E F e.2).mp hei) (Or.inl hi)
      have hinf : i ≠ f.2 := by
        intro h; subst i
        exact ((mem_cutIT E F f.2).mp hfi) (Or.inl hi)
      have hh := three_mem_eq (hF.1.2.1 e.1)
        (mem_filter.mpr ⟨heF,rfl⟩) (mem_filter.mpr ⟨hfF,hef.symm⟩)
        (mem_filter.mpr ⟨hai,rfl⟩)
      rcases hh with h | h | h
      · exact congrArg Prod.snd h
      · exact False.elim (hine (congrArg Prod.snd h).symm)
      · exact False.elim (hinf (congrArg Prod.snd h).symm)
  exact Prod.ext hef hind

 theorem cut_capacity {E F : Finset (A × I)} (hF : IsMaxFlowSet E F) :
    F.card = 2 * ((cutAT E F).card + (cutIS E F).card) + (Edelta E F).card := by
  classical
  let P := F.filter (fun e => e.1 ∈ cutAT E F)
  let Q := F.filter (fun e => e.2 ∈ cutIS E F)
  let D := Edelta E F
  have hP : P.card = 2 * (cutAT E F).card := by
    rw [← sum_card_fiberwise_eq_card_filter F (cutAT E F) Prod.fst]
    change (∑ a ∈ cutAT E F, degA F a) = _
    rw [sum_const_nat (fun a ha => cutAT_saturated hF ha)]
    omega
  have hQ : Q.card = 2 * (cutIS E F).card := by
    rw [← sum_card_fiberwise_eq_card_filter F (cutIS E F) Prod.snd]
    change (∑ i ∈ cutIS E F, degI F i) = _
    rw [sum_const_nat (fun i hi => (cutIS_saturated_neighbors hF hi).1)]
    omega
  have hPQ : Disjoint P Q := by
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨he,ha⟩ := mem_filter.mp he
    obtain ⟨_,hi⟩ := mem_filter.mp hf
    have hAS := (cutIS_saturated_neighbors hF hi).2 e.1 he
    exact (mem_cutAT E F e.1).mp ha ((mem_cutAS E F e.1).mp hAS)
  have hPD : Disjoint P D := by
    apply disjoint_left.mpr
    intro e he hf
    have hAT := (mem_filter.mp he).2
    have hAS := (mem_filter.mp hf).2.1
    exact (mem_cutAT E F e.1).mp hAT ((mem_cutAS E F e.1).mp hAS)
  have hQD : Disjoint Q D := by
    apply disjoint_left.mpr
    intro e he hf
    have hIS := (mem_filter.mp he).2
    have hIT := (mem_filter.mp hf).2.2
    exact (mem_sdiff.mp hIT).2 hIS
  have hu : P ∪ Q ∪ D = F := by
    ext e
    simp only [mem_union]
    constructor
    · rintro ((h|h)|h)
      · exact (mem_filter.mp h).1
      · exact (mem_filter.mp h).1
      · exact crossing_subset_flow E F h
    · intro he
      by_cases ha : e.1 ∈ cutAT E F
      · exact Or.inl (Or.inl (mem_filter.mpr ⟨he,ha⟩))
      by_cases hi : e.2 ∈ cutIS E F
      · exact Or.inl (Or.inr (mem_filter.mpr ⟨he,hi⟩))
      · right; apply mem_filter.mpr
        refine ⟨hF.1.1 he,?_,mem_sdiff.mpr ⟨mem_univ _,hi⟩⟩
        simpa [cutAT] using ha
  have hc := card_union_of_disjoint (disjoint_union_left.mpr ⟨hPD,hQD⟩)
  rw [hu,card_union_of_disjoint hPQ,hP,hQ] at hc
  dsimp [D] at hc
  omega

 theorem realization_cut_bound {E F : Finset (A × I)} {n : ℕ} (ω : Fin n → I)
    (M : Fin n → Option A) (hm : IsRealizationMatching E ω M) :
    matchSize M ≤ (cutAT E F).card + (univ.filter fun t => ω t ∈ cutIS E F).card +
      (((Edelta E F).image Prod.snd).filter fun i => ∃ t, ω t = i).card := by
  classical
  let S := univ.filter (fun t => (M t).isSome = true)
  let P := S.filter (fun t => ∃ a ∈ cutAT E F, M t = some a)
  let Q := univ.filter (fun t => ω t ∈ cutIS E F)
  let R := S.filter (fun t => ∃ a, M t = some a ∧ (a,ω t) ∈ Edelta E F)
  let T := ((Edelta E F).image Prod.snd).filter (fun i => ∃ t, ω t = i)
  have hP : P.card ≤ (cutAT E F).card := by
    have hh : P.card ≤ ((cutAT E F).image (some : A → Option A)).card := by
      apply card_le_card_of_injOn M
      · intro t ht
        obtain ⟨a,ha,hma⟩ := (mem_filter.mp ht).2
        exact mem_image.mpr ⟨a,ha,hma.symm⟩
      · intro s hs t ht heq
        obtain ⟨a,_,ha⟩ := (mem_filter.mp hs).2
        exact hm.2 s t a ha (heq ▸ ha)
    simpa [card_image_of_injective _ (Option.some_injective A)] using hh
  have hR : R.card ≤ T.card := by
    apply card_le_card_of_injOn ω
    · intro t ht
      obtain ⟨a,_,ha⟩ := (mem_filter.mp ht).2
      exact mem_filter.mpr ⟨mem_image.mpr ⟨(a,ω t),ha,rfl⟩,t,rfl⟩
    · intro s hs t ht heq
      obtain ⟨a,ha,hea⟩ := (mem_filter.mp hs).2
      obtain ⟨b,hb,heb⟩ := (mem_filter.mp ht).2
      have hh := crossing_injective_snd E F hea heb heq
      have hab : a=b := congrArg Prod.fst hh
      subst b
      exact hm.2 s t a ha hb
  have hS : S ⊆ P ∪ Q ∪ R := by
    intro t ht
    have hsome : (M t).isSome = true := (mem_filter.mp ht).2
    cases he : M t with
    | none => simp [he] at hsome
    | some a =>
      by_cases ha : a ∈ cutAT E F
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_filter.mpr ⟨ht,a,ha,he⟩))))
      by_cases hi : ω t ∈ cutIS E F
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,hi⟩))))
      · apply mem_union.mpr; right
        apply mem_filter.mpr
        refine ⟨ht,a,he,mem_filter.mpr ⟨hm.1 t a he,?_,?_⟩⟩
        · simpa [cutAT] using ha
        · exact mem_sdiff.mpr ⟨mem_univ _,hi⟩
  have h1 := card_le_card hS
  have h2 := card_union_le (P ∪ Q) R
  have h3 := card_union_le P Q
  change S.card ≤ _
  change S.card ≤ (cutAT E F).card + Q.card + T.card
  omega

 theorem OPT_cut_bound {E F : Finset (A × I)} {n : ℕ} (ω : Fin n → I) :
    OPT E ω ≤ (cutAT E F).card + (univ.filter fun t => ω t ∈ cutIS E F).card +
      (((Edelta E F).image Prod.snd).filter fun i => ∃ t, ω t = i).card := by
  classical
  apply Finset.sup_le
  intro M hM
  exact realization_cut_bound ω M (mem_filter.mp hM).2
end Cut
end TSMProof

open Finset OnlineStochMatching.TSM
namespace TSMProof
noncomputable section
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]
local instance (C : Comp A I) : DecidablePred (Occurs C) := fun _ => Classical.propDecidable _

 theorem crossing_share {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {e f : A × I} (he : e ∈ Edelta E F) (hf : f ∈ Edelta E F)
    (hs : e.1=f.1 ∨ e.2=f.2) : e=f := by
  rcases hs with h | h
  · exact crossing_injective_fst hF he hf h
  · exact crossing_injective_snd E F he hf h

 theorem adjacent_cross_impossible {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {C : Comp A I} (hC : C.IsPathOrCycle F) {j k : ℕ} (hj : j<C.len) (hk : k<C.len)
    (hne : j≠k) (hv : C.v (j+1)=C.v k) {e f : A × I}
    (he : e ∈ Edelta E F) (hf : f ∈ Edelta E F)
    (hje : C.HasEdgeAt j e) (hkf : C.HasEdgeAt k f) : False := by
  have hs : e.1=f.1 ∨ e.2=f.2 := by
    rcases hje with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      rcases hkf with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;> simp_all
  have heq := crossing_share hF he hf hs
  subst f
  exact hne (edge_index_unique hC hj hk hje hkf)

 theorem middle_cross {E F : Finset (A × I)} {C : Comp A I}
    {j k l : ℕ} (hv : C.v (j+1)=C.v k) (hw : C.v (k+1)=C.v l)
    {e g f : A × I} (he : e ∈ Edelta E F) (hf : f ∈ Edelta E F) (hg : g ∈ E)
    (hje : C.HasEdgeAt j e) (hkg : C.HasEdgeAt k g) (hlf : C.HasEdgeAt l f) :
    g ∈ Edelta E F := by
  obtain ⟨_,hea,hei⟩ := mem_filter.mp he
  obtain ⟨_,hfa,hfi⟩ := mem_filter.mp hf
  apply mem_filter.mpr
  refine ⟨hg,?_⟩
  rcases hje with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
    rcases hkg with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;>
    rcases hlf with ⟨h5,h6⟩ | ⟨h5,h6⟩ <;> simp_all

 theorem hit_spacing {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {C : Comp A I} (hC : C.IsPathOrCycle F) {j k : ℕ} (hj : j<C.len) (hk : k<C.len)
    (hjk : j<k) (he : ∃ e ∈ Edelta E F, C.HasEdgeAt j e)
    (hf : ∃ f ∈ Edelta E F, C.HasEdgeAt k f) : j+3≤k := by
  obtain ⟨e,he,hje⟩ := he
  obtain ⟨f,hf,hkf⟩ := hf
  by_contra hn
  by_cases h1 : k=j+1
  · subst k
    exact adjacent_cross_impossible hF hC hj hk (by omega) rfl he hf hje hkf
  have h2 : k=j+2 := by omega
  subst k
  obtain ⟨g,hg,hjg⟩ := hC.2.1 (j+1) (by omega)
  have hgd := middle_cross (j:=j) (k:=j+1) (l:=j+2) rfl rfl he hf (hF.1.1 hg) hje hjg hkf
  exact adjacent_cross_impossible hF hC hj (by omega) (by omega) rfl he hgd hje hjg

 omit [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I] in
 theorem cycle_next_vertex {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) (hc : C.cyc=true) {j : ℕ} (hj : j<C.len) :
    C.v (j+1)=C.v ((j+1)%C.len) := by
  have hh := hC.2.2
  simp only [hc,↓reduceIte] at hh
  by_cases he : j+1=C.len
  · simp [he,hh.2.1]
  · rw [Nat.mod_eq_of_lt (by omega)]

 theorem cycle_hit_no_one {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {C : Comp A I} (hC : C.IsPathOrCycle F) (hc : C.cyc=true) {j : ℕ} (hj : j<C.len)
    (he : ∃ e ∈ Edelta E F, C.HasEdgeAt j e) :
    ¬∃ f ∈ Edelta E F, C.HasEdgeAt ((j+1)%C.len) f := by
  intro hf
  obtain ⟨e,he,hje⟩ := he
  obtain ⟨f,hf,hkf⟩ := hf
  have hh := hC.2.2
  simp only [hc,↓reduceIte] at hh
  have hne : j≠(j+1)%C.len := by
    by_cases he : j+1=C.len
    · simp only [he,Nat.mod_self]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  apply adjacent_cross_impossible hF hC hj (Nat.mod_lt _ (by omega))
    hne (cycle_next_vertex hC hc hj) he hf hje hkf

 theorem cycle_hit_no_two {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {C : Comp A I} (hC : C.IsPathOrCycle F) (hc : C.cyc=true) {j : ℕ} (hj : j<C.len)
    (he : ∃ e ∈ Edelta E F, C.HasEdgeAt j e) :
    ¬∃ f ∈ Edelta E F, C.HasEdgeAt ((j+2)%C.len) f := by
  intro hf
  obtain ⟨e,he,hje⟩ := he
  obtain ⟨f,hf,hkf⟩ := hf
  have hh := hC.2.2
  simp only [hc,↓reduceIte] at hh
  let k := (j+1)%C.len
  have hk : k<C.len := Nat.mod_lt _ (by omega)
  obtain ⟨g,hg,hkg⟩ := hC.2.1 k hk
  have hv := cycle_next_vertex hC hc hj
  have hw : C.v (k+1)=C.v ((j+2)%C.len) := by
    rw [cycle_next_vertex hC hc hk]
    congr 1
    dsimp [k]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hgd := middle_cross hv hw he hf (hF.1.1 hg) hje hkg hkf
  exact cycle_hit_no_one hF hC hc hj ⟨e,he,hje⟩ ⟨g,hgd,hkg⟩

 omit [Fintype A] [Fintype I] in
 theorem component_edges_card {F : Finset (A × I)} {C : Comp A I}
    (hC : C.IsPathOrCycle F) : (F.filter (Occurs C)).card = C.len := by
  classical
  have he : F.filter (Occurs C) = univ.image (componentEdge hC) := by
    ext e
    constructor
    · intro he
      obtain ⟨_,j,hj,h⟩ := mem_filter.mp he
      exact mem_image.mpr ⟨⟨j,hj⟩,mem_univ _,hasEdgeAt_unique C j (componentEdge_at hC ⟨j,hj⟩) h⟩
    · intro he
      obtain ⟨j,_,rfl⟩ := mem_image.mp he
      exact mem_filter.mpr ⟨componentEdge_mem hC j,j,j.isLt,componentEdge_at hC j⟩
  rw [he,card_image_of_injective _ (componentEdge_injective hC)]
  simp

 omit [Fintype A] [Fintype I] in
 theorem listed_subset_card {F blue red H : Finset (A × I)} (D : ColoringData F blue red)
    (hH : H ⊆ F) : H.card = ∑ k : Fin D.m, (H.filter (Occurs (D.C k))).card := by
  classical
  have hu : univ.biUnion (fun k : Fin D.m => H.filter (Occurs (D.C k))) = H := by
    ext e
    simp only [mem_biUnion,mem_univ,true_and,mem_filter]
    constructor
    · rintro ⟨k,he,_⟩; exact he
    · intro he
      obtain ⟨k,hk⟩ := D.cover e (hH he)
      exact ⟨k,he,hk⟩
  rw [← hu,card_biUnion]
  · rw [hu]
  · intro k _ l _ hne
    apply disjoint_left.mpr
    intro e he hf
    exact hne (edge_component_unique D.C D.disjoint (mem_filter.mp he).2 (mem_filter.mp hf).2)

 omit [Fintype A] [Fintype I] in
 theorem listed_total_length {F blue red : Finset (A × I)} (D : ColoringData F blue red) :
    F.card = ∑ k : Fin D.m, (D.C k).len := by
  rw [listed_subset_card D (Subset.refl F)]
  apply sum_congr rfl
  intro k _; exact component_edges_card (D.valid k)

 noncomputable def cutHits (E F : Finset (A × I)) (C : Comp A I) : Finset ℕ := by
  classical
  exact (range C.len).filter (fun j => ∃ e ∈ Edelta E F, C.HasEdgeAt j e)

 theorem cutHits_card {E F : Finset (A × I)} {C : Comp A I} (hC : C.IsPathOrCycle F) :
    (cutHits E F C).card = ((Edelta E F).filter (Occurs C)).card := by
  classical
  apply card_bij (fun j hj => componentEdge hC ⟨j,mem_range.mp (mem_filter.mp hj).1⟩)
  · intro j hj
    obtain ⟨_,e,he,h⟩ := mem_filter.mp hj
    have hEq := hasEdgeAt_unique C j (componentEdge_at hC ⟨j,mem_range.mp (mem_filter.mp hj).1⟩) h
    exact mem_filter.mpr ⟨hEq ▸ he,j,mem_range.mp (mem_filter.mp hj).1,componentEdge_at hC ⟨j,mem_range.mp (mem_filter.mp hj).1⟩⟩
  · intro j hj k hk heq
    exact congrArg Fin.val (componentEdge_injective hC heq)
  · intro e he
    obtain ⟨he,j,hj,h⟩ := mem_filter.mp he
    exact ⟨j,mem_filter.mpr ⟨mem_range.mpr hj,e,he,h⟩,
      hasEdgeAt_unique C j (componentEdge_at hC ⟨j,hj⟩) h⟩

 theorem component_cut_bound {E F : Finset (A × I)} (hF : IsMaxFlowSet E F)
    {C : Comp A I} (hC : C.IsPathOrCycle F) :
    3*((Edelta E F).filter (Occurs C)).card ≤ C.len + if C.cyc=false then 2 else 0 := by
  classical
  rw [← cutHits_card hC]
  have hsub : cutHits E F C ⊆ range C.len := filter_subset _ _
  by_cases hc : C.cyc=true
  · have hh := hC.2.2
    simp only [hc,↓reduceIte] at hh
    have hb := Peer.cyclic_triple_bound (cutHits E F C) C.len (by omega) hsub (by
      intro j hj
      obtain ⟨hj,he⟩ := mem_filter.mp hj
      refine ⟨?_,?_⟩
      · intro hm
        exact cycle_hit_no_one hF hC hc (mem_range.mp hj) he (mem_filter.mp hm).2
      · intro hm
        exact cycle_hit_no_two hF hC hc (mem_range.mp hj) he (mem_filter.mp hm).2)
    simpa [hc] using hb
  · have hc' : C.cyc=false := Bool.eq_false_iff.mpr hc
    have hb := Peer.linear_triple_bound (cutHits E F C) C.len hsub (by
      intro j hj k hk hjk
      obtain ⟨hj,he⟩ := mem_filter.mp hj
      obtain ⟨hk,hf⟩ := mem_filter.mp hk
      exact hit_spacing hF hC (mem_range.mp hj) (mem_range.mp hk) hjk he hf)
    simpa [hc'] using hb

 theorem cut_packing {E F blue red : Finset (A × I)} (hF : IsMaxFlowSet E F)
    (D : ColoringData F blue red) :
    3*(Edelta E F).card ≤ 2*(adsBR blue red).card + 4*(adsBB blue red).card +
      3*(adsB blue red).card + (adsR blue red).card := by
  classical
  have hh := sum_le_sum (fun k (_ : k ∈ (univ : Finset (Fin D.m))) => component_cut_bound hF (D.valid k))
  simp only [sum_add_distrib,← mul_sum] at hh
  rw [← listed_subset_card D (crossing_subset_flow E F),← listed_total_length D] at hh
  have he : (∑ k : Fin D.m, if (D.C k).cyc=false then 2 else 0) =
      2*(univ.filter (fun k : Fin D.m => (D.C k).cyc=false)).card := by
    simp [sum_ite,Nat.mul_comm]
  rw [he] at hh
  have hp := D.paths_le_good
  have hc := D.edge_class_count
  omega
end
end TSMProof

open Finset OnlineStochMatching.TSM
noncomputable section
namespace TSMProof
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {A I : Type} [DecidableEq A] [DecidableEq I]

 theorem assigned_before_iff {n : ℕ} (blue red : Finset (A × I)) (ω : Fin n → I)
    (k : ℕ) (a : A) : a ∈ assignedBefore blue red ω k ↔
      ∃ t : Fin n, t.val<k ∧ tryAd blue red ω t=some a := by
  induction k with
  | zero => simp [assignedBefore]
  | succ k ih =>
    by_cases hk : k<n
    · rw [assignedBefore, dif_pos hk]
      cases he : tryAd blue red ω ⟨k,hk⟩ with
      | none =>
        rw [ih]
        constructor
        · rintro ⟨t,ht,he⟩; exact ⟨t,by omega,he⟩
        · rintro ⟨t,ht,ha⟩
          have hne : t.val≠k := by
            intro h
            have hte : t=⟨k,hk⟩ := Fin.ext h
            simp [hte,he] at ha
          exact ⟨t,by omega,ha⟩
      | some b =>
        rw [mem_insert,ih]
        constructor
        · rintro (rfl|⟨t,ht,ha⟩)
          · exact ⟨⟨k,hk⟩,by simp,he⟩
          · exact ⟨t,by omega,ha⟩
        · rintro ⟨t,ht,ha⟩
          by_cases h : t.val=k
          · left
            have hte : t=⟨k,hk⟩ := Fin.ext h
            simpa [hte,he] using ha.symm
          · right; exact ⟨t,by omega,ha⟩
    · rw [assignedBefore,dif_neg hk,ih]
      constructor
      · rintro ⟨t,ht,ha⟩; exact ⟨t,by omega,ha⟩
      · rintro ⟨t,_,ha⟩; exact ⟨t,by have := t.isLt; omega,ha⟩

 theorem assigned_card_prefix {n : ℕ} (blue red : Finset (A × I)) (ω : Fin n → I)
    (k : ℕ) (hk : k≤n) :
    (assignedBefore blue red ω k).card = (univ.filter fun t : Fin n => t.val<k ∧ Assigns blue red ω t).card := by
  classical
  induction k with
  | zero => simp [assignedBefore]
  | succ k ih =>
    have hkn : k<n := by omega
    have ih := ih (by omega)
    let t : Fin n := ⟨k,hkn⟩
    let S := univ.filter (fun s : Fin n => s.val<k ∧ Assigns blue red ω s)
    have ht : t ∉ S := by simp [S,t]
    have hsplit : (univ.filter fun s : Fin n => s.val<k+1 ∧ Assigns blue red ω s) =
        if Assigns blue red ω t then insert t S else S := by
      ext s
      by_cases hst : s=t
      · subst s; by_cases ha : Assigns blue red ω t <;> simp [ha,t,S] at *
      · have hne : s.val≠k := fun h => hst (Fin.ext h)
        have hh : s.val≤k ↔ s.val<k := by omega
        by_cases ha : Assigns blue red ω t <;> simp [ha,S,hst,hh]
    rw [hsplit,assignedBefore,dif_pos hkn]
    cases he : tryAd blue red ω t with
    | none =>
      have ha : ¬Assigns blue red ω t := by simp [Assigns,he]
      simp only [ha,↓reduceIte]
      exact ih
    | some a =>
      have ha : Assigns blue red ω t ↔ a ∉ assignedBefore blue red ω k := by simp [Assigns,he,t]
      dsimp only
      by_cases hm : a ∈ assignedBefore blue red ω k
      · rw [insert_eq_of_mem hm,if_neg (fun h => (ha.mp h) hm)]
        exact ih
      · rw [card_insert_of_notMem hm,if_pos (ha.mpr hm),card_insert_of_notMem ht]
        exact congrArg (fun x => x+1) ih

 theorem ALG_union [Fintype A] {n : ℕ} (blue red : Finset (A × I)) (ω : Fin n → I) :
    ALG blue red ω = (univ.filter fun a => ∃ t, tryAd blue red ω t=some a).card := by
  classical
  have hh := assigned_card_prefix blue red ω n le_rfl
  have hp : (univ.filter fun t : Fin n => t.val<n ∧ Assigns blue red ω t) =
      univ.filter (Assigns blue red ω) := by ext t; simp
  rw [hp] at hh
  change _ = ALG blue red ω at hh
  rw [← hh]
  congr 1
  ext a
  simp only [assigned_before_iff,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨t,_,ht⟩; exact ⟨t,ht⟩
  · rintro ⟨t,ht⟩; exact ⟨t,t.isLt,ht⟩

 noncomputable def typeCount {n : ℕ} (ω : Fin n → I) (i : I) : ℕ :=
    (univ.filter fun t => ω t=i).card

 theorem prevCount_rank {n : ℕ} (ω : Fin n → I) (i : I) (k : ℕ) :
    (∃ t, ω t=i ∧ prevCount ω t=k) ↔ k<typeCount ω i := by
  classical
  let S := univ.filter (fun t => ω t=i)
  have hcount : ∀ t ∈ S, prevCount ω t = (S.filter fun s => s<t).card := by
    intro t ht
    have hti : ω t=i := (mem_filter.mp ht).2
    unfold prevCount
    congr 1
    ext s; simp [S,hti,and_comm]
  constructor
  · rintro ⟨t,hti,hk⟩
    have ht : t∈S := mem_filter.mpr ⟨mem_univ _,hti⟩
    rw [hcount t ht] at hk
    have hs : S.filter (fun s => s<t) ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,by intro h; have := h ▸ ht; simp at this⟩
    have := card_lt_card hs
    change k<S.card
    omega
  · intro hk
    change k<S.card at hk
    let e := S.orderEmbOfFin rfl
    let t := e ⟨k,hk⟩
    have ht : t∈S := S.orderEmbOfFin_mem rfl ⟨k,hk⟩
    refine ⟨t,(mem_filter.mp ht).2,?_⟩
    rw [hcount t ht]
    have he : (S.filter fun s => s<t) =
        (univ.filter fun j : Fin S.card => j.val<k).image e := by
      ext s
      constructor
      · intro hs
        obtain ⟨hs,hst⟩ := mem_filter.mp hs
        obtain ⟨j,_,hj⟩ := mem_image.mp ((S.image_orderEmbOfFin_univ rfl).symm ▸ hs)
        refine mem_image.mpr ⟨j,?_,hj⟩
        have hlt : j<⟨k,hk⟩ := e.lt_iff_lt.mp (by change e j < e ⟨k,hk⟩; rw [show e j=s from hj]; exact hst)
        exact mem_filter.mpr ⟨mem_univ _,hlt⟩
      · intro hs
        obtain ⟨j,hj,rfl⟩ := mem_image.mp hs
        exact mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl j,
          e.lt_iff_lt.mpr (mem_filter.mp hj).2⟩
    rw [he,card_image_of_injective _ e.injective]
    have hh : (univ.filter fun j : Fin S.card => j.val<k) = Iio ⟨k,hk⟩ := by ext j; simp only [mem_filter,mem_univ,true_and,mem_Iio]; rfl
    rw [hh,Fin.card_Iio]

 omit [DecidableEq A] in
 theorem tried_iff {n : ℕ} (blue red : Finset (A × I)) (ω : Fin n → I) (a : A) :
    (∃ t, tryAd blue red ω t=some a) ↔
    (∃ i, 0<typeCount ω i ∧ blueAd blue i=some a) ∨
    (∃ i, 1<typeCount ω i ∧ redAd red i=some a) := by
  constructor
  · rintro ⟨t,ht⟩
    unfold tryAd at ht
    split_ifs at ht with h0 h1
    · exact Or.inl ⟨ω t,(prevCount_rank ω (ω t) 0).mp ⟨t,rfl,h0⟩,ht⟩
    · exact Or.inr ⟨ω t,(prevCount_rank ω (ω t) 1).mp ⟨t,rfl,h1⟩,ht⟩
  · rintro (⟨i,hi,ha⟩|⟨i,hi,ha⟩)
    · obtain ⟨t,hti,h0⟩ := (prevCount_rank ω i 0).mpr hi
      exact ⟨t,by simp [tryAd,h0,hti,ha]⟩
    · obtain ⟨t,hti,h1⟩ := (prevCount_rank ω i 1).mpr hi
      exact ⟨t,by simp [tryAd,h1,hti,ha]⟩

 theorem ALG_triggers [Fintype A] {n : ℕ} (blue red : Finset (A × I)) (ω : Fin n → I) :
    ALG blue red ω = (univ.filter fun a =>
      (∃ i, 0<typeCount ω i ∧ blueAd blue i=some a) ∨
      (∃ i, 1<typeCount ω i ∧ redAd red i=some a)).card := by
  rw [ALG_union]
  congr 1
  ext a
  simp only [mem_filter,mem_univ,true_and,tried_iff]

 theorem blueAd_iff [Fintype A] (blue : Finset (A × I)) (i : I)
    (hdeg : degI blue i≤1) (a : A) : blueAd blue i=some a ↔ (a,i)∈blue := by
  unfold blueAd
  split_ifs with h
  · have hc := h.choose_spec
    constructor
    · intro he; cases Option.some.inj he; exact hc
    · intro ha
      have hs : ({(h.choose,i),(a,i)} : Finset (A × I)) ⊆ blue.filter (fun b => b.2=i) := by
        intro b hb; simp only [mem_insert,mem_singleton] at hb
        rcases hb with rfl|rfl <;> simp [*]
      have hh := (card_le_card hs).trans hdeg
      have he : h.choose=a := by by_contra hne; simp [hne] at hh
      exact congrArg some he
  · simp only [false_iff]
    exact fun ha => h ⟨a,ha⟩

 theorem redAd_iff [Fintype A] (red : Finset (A × I)) (i : I)
    (hdeg : degI red i≤1) (a : A) : redAd red i=some a ↔ (a,i)∈red :=
  blueAd_iff red i hdeg a

 theorem ALG_edges [Fintype A] [Fintype I] {F blue red : Finset (A × I)}
    (D : ColoringData F blue red) {n : ℕ} (ω : Fin n → I) :
    ALG blue red ω = (univ.filter fun a =>
      (∃ i, (a,i)∈blue ∧ 0<typeCount ω i) ∨
      (∃ i, (a,i)∈red ∧ 1<typeCount ω i)).card := by
  rw [ALG_triggers]
  congr 1
  ext a
  simp only [mem_filter,mem_univ,true_and]
  apply or_congr
  · apply exists_congr; intro i
    rw [blueAd_iff blue i (D.impression_bounds i).1]
    exact and_comm
  · apply exists_congr; intro i
    rw [redAd_iff red i ((D.impression_bounds i).2.trans (D.impression_bounds i).1)]
    exact and_comm


 theorem count_update_other {n : ℕ} (ω : Fin n → I) (j : Fin n) (i x : I) (hx : x≠i) :
    typeCount (Function.update ω j i) x ≤ typeCount ω x := by
  apply card_le_card
  intro t ht
  have ht' := (mem_filter.mp ht).2
  have hne : t≠j := by intro h; subst t; simp at ht'; exact hx ht'.symm
  exact mem_filter.mpr ⟨mem_univ _,by simpa [Function.update_of_ne hne] using ht'⟩

 theorem ALG_update_le [Fintype A] {n : ℕ} (blue red : Finset (A × I))
    (ω : Fin n → I) (j : Fin n) (i : I) :
    ALG blue red (Function.update ω j i) ≤ ALG blue red ω + 2 := by
  classical
  rw [ALG_triggers,ALG_triggers]
  let S := univ.filter (fun a => (∃ x, 0<typeCount ω x ∧ blueAd blue x=some a) ∨
      (∃ x, 1<typeCount ω x ∧ redAd red x=some a))
  have hs : (univ.filter fun a =>
      (∃ x, 0<typeCount (Function.update ω j i) x ∧ blueAd blue x=some a) ∨
      (∃ x, 1<typeCount (Function.update ω j i) x ∧ redAd red x=some a)) ⊆
      S ∪ (blueAd blue i).toFinset ∪ (redAd red i).toFinset := by
    intro a ha
    rcases (mem_filter.mp ha).2 with ⟨x,hx,ha⟩|⟨x,hx,ha⟩
    · by_cases h : x=i
      · simp [h] at ha
        exact mem_union_left _ (mem_union_right _ (by simp [ha]))
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,
          Or.inl ⟨x,hx.trans_le (count_update_other ω j i x h),ha⟩⟩))
    · by_cases h : x=i
      · simp [h] at ha
        exact mem_union_right _ (by simp [ha])
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,
          Or.inr ⟨x,hx.trans_le (count_update_other ω j i x h),ha⟩⟩))
  have hb : (blueAd blue i).toFinset.card≤1 := by cases blueAd blue i <;> simp
  have hr : (redAd red i).toFinset.card≤1 := by cases redAd red i <;> simp
  have h₁ := card_le_card hs
  have h₂ := card_union_le (S ∪ (blueAd blue i).toFinset) (redAd red i).toFinset
  have h₃ := card_union_le S (blueAd blue i).toFinset
  change _ ≤ S.card+2
  omega

 theorem ALG_oscillation [Fintype A] {n : ℕ} (blue red : Finset (A × I)) :
    Oscillation n (fun ω : Fin n → I => (ALG blue red ω : ℝ)) 2 := by
  intro ω j i
  have h₁ := ALG_update_le blue red ω j i
  have h₂ := ALG_update_le blue red (Function.update ω j i) j (ω j)
  simp only [Function.update_idem,Function.update_eq_self] at h₂
  have h₁' : (ALG blue red (Function.update ω j i) : ℝ) ≤ ALG blue red ω+2 := by exact_mod_cast h₁
  have h₂' : (ALG blue red ω : ℝ) ≤ ALG blue red (Function.update ω j i)+2 := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

 omit [DecidableEq A] [DecidableEq I] in
 theorem OPT_update_le [Fintype A] {n : ℕ} (E : Finset (A × I))
    (ω : Fin n → I) (j : Fin n) (i : I) : OPT E (Function.update ω j i) ≤ OPT E ω+1 := by
  classical
  unfold OPT
  apply Finset.sup_le
  intro M hM
  let M' := Function.update M j none
  have hm := (mem_filter.mp hM).2
  have hm' : IsRealizationMatching E ω M' := by
    constructor
    · intro t a ht
      have hne : t≠j := by intro h; subst t; simp [M'] at ht
      have he : M t=some a := by simpa [M',Function.update_of_ne hne] using ht
      simpa [Function.update_of_ne hne] using hm.1 t a he
    · intro s t a hs ht
      have hsn : s≠j := by intro h; subst s; simp [M'] at hs
      have htn : t≠j := by intro h; subst t; simp [M'] at ht
      exact hm.2 s t a (by simpa [M',Function.update_of_ne hsn] using hs)
        (by simpa [M',Function.update_of_ne htn] using ht)
  have hsize : matchSize M ≤ matchSize M'+1 := by
    have he : (univ.filter fun t => (M t).isSome=true) ⊆
        insert j (univ.filter fun t => (M' t).isSome=true) := by
      intro t ht
      by_cases h : t=j
      · simp [h]
      · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,by
          simpa [M',Function.update_of_ne h] using (mem_filter.mp ht).2⟩)
    exact (card_le_card he).trans (card_insert_le _ _)
  exact hsize.trans (Nat.add_le_add_right (Finset.le_sup (mem_filter.mpr ⟨mem_univ _,hm'⟩)) 1)

 omit [DecidableEq A] [DecidableEq I] in
 theorem OPT_oscillation [Fintype A] {n : ℕ} (E : Finset (A × I)) :
    Oscillation n (fun ω : Fin n → I => (OPT E ω : ℝ)) 1 := by
  intro ω j i
  have h₁ := OPT_update_le E ω j i
  have h₂ := OPT_update_le E (Function.update ω j i) j (ω j)
  simp only [Function.update_idem,Function.update_eq_self] at h₂
  have h₁' : (OPT E (Function.update ω j i) : ℝ)≤OPT E ω+1 := by exact_mod_cast h₁
  have h₂' : (OPT E ω : ℝ)≤OPT E (Function.update ω j i)+1 := by exact_mod_cast h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end TSMProof

open Finset OnlineStochMatching.TSM
namespace TSMProof
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

 theorem expected_OPT_cut [Nonempty I] (E F : Finset (A × I)) :
    avg (Fintype.card I) (fun ω => (OPT E ω : ℝ)) ≤
    (cutAT E F).card + (cutIS E F).card +
      (Edelta E F).card*(1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I)) := by
  classical
  have hh : avg (Fintype.card I) (fun ω => (OPT E ω : ℝ)) ≤
      avg (Fintype.card I) (fun ω => ((cutAT E F).card : ℝ) +
        (Occupancy.visits (cutIS E F) ω : ℝ) +
        ((((Edelta E F).image Prod.snd).filter fun i => ∃ t,ω t=i).card : ℝ)) := by
    simp only [avg_eq_mean]
    apply mean_mono
    intro ω
    exact_mod_cast OPT_cut_bound (E:=E) (F:=F) ω
  have hc : ((Edelta E F).image Prod.snd).card = (Edelta E F).card :=
    card_image_of_injOn (crossing_injective_snd E F)
  simp only [avg_eq_mean,mean_add,mean_const] at hh
  have hv := Occupancy.avg_visits_diagonal (cutIS E F)
  have ho := Occupancy.avg_occupied_types ((Edelta E F).image Prod.snd) (Fintype.card I)
  rw [avg_eq_mean] at hv ho
  rw [hv,ho,hc] at hh
  rw [avg_eq_mean]
  exact hh

 theorem expected_OPT_bound [Nonempty I] {E F blue red : Finset (A × I)}
    (hF : IsMaxFlowSet E F) (D : ColoringData F blue red) :
    avg (Fintype.card I) (fun ω => (OPT E ω : ℝ)) ≤
      (adsBR blue red).card + (adsBB blue red).card +
      ((adsB blue red).card+(adsR blue red).card)/2 +
      (1/2-(1-1/(Fintype.card I:ℝ))^(Fintype.card I))*(Edelta E F).card := by
  have hc := cut_capacity hF
  have hd := D.edge_class_count
  have he : (2:ℝ)*((cutAT E F).card+(cutIS E F).card)+(Edelta E F).card =
      2*(adsBR blue red).card+2*(adsBB blue red).card+(adsB blue red).card+(adsR blue red).card := by
    exact_mod_cast hc.symm.trans hd
  have hh := expected_OPT_cut E F
  nlinarith

 noncomputable def neighborTypes (H : Finset (A × I)) (a : A) : Finset I :=
    univ.filter fun i => (a,i)∈H

 omit [Fintype A] in
 theorem neighborTypes_card (H : Finset (A × I)) (a : A) :
    (neighborTypes H a).card = degA H a := by
  classical
  have he : (neighborTypes H a).image (fun i => (a,i)) = H.filter (fun e => e.1=a) := by
    ext e
    simp only [mem_image,mem_filter,mem_univ,true_and,neighborTypes]
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨hi,rfl⟩
    · rintro ⟨he,ha⟩
      have heq : (a,e.2)=e := by ext <;> simp [ha]
      exact ⟨e.2,heq.symm ▸ he,heq⟩
  have hi : Function.Injective (fun i : I => (a,i)) := fun _ _ h => congrArg Prod.snd h
  rw [← card_image_of_injective _ hi,he]
  rfl

 omit [Fintype A] in
 theorem neighborTypes_disjoint {F blue red : Finset (A × I)}
    (D : ColoringData F blue red) (a : A) : Disjoint (neighborTypes blue a) (neighborTypes red a) := by
  classical
  apply disjoint_left.mpr
  intro i hi hr
  exact disjoint_left.mp D.disjoint_colors ((mem_filter.mp hi).2) ((mem_filter.mp hr).2)

 omit [Fintype A] in
 theorem neighborTypes_cases {F blue red : Finset (A × I)}
    (D : ColoringData F blue red) (a : A) :
    ((neighborTypes blue a).card=0 ∧ (neighborTypes red a).card=0) ∨
    ((neighborTypes blue a).card=1 ∧ (neighborTypes red a).card=0) ∨
    ((neighborTypes blue a).card=0 ∧ (neighborTypes red a).card=1) ∨
    ((neighborTypes blue a).card=1 ∧ (neighborTypes red a).card=1) ∨
    ((neighborTypes blue a).card=2 ∧ (neighborTypes red a).card=0) := by
  rw [neighborTypes_card,neighborTypes_card]
  exact D.advertiser_cases a


 theorem expected_ALG [Nonempty I] {F blue red : Finset (A × I)}
    (D : ColoringData F blue red) :
    avg (Fintype.card I) (fun ω => (ALG blue red ω : ℝ)) =
      (1-(1-2/(Fintype.card I:ℝ))^(Fintype.card I))*(adsBB blue red).card +
      (1-(1-2/(Fintype.card I:ℝ))^(Fintype.card I)-(1-2/(Fintype.card I:ℝ))^(Fintype.card I-1))*(adsBR blue red).card +
      (1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I))*(adsB blue red).card +
      (1-(1-1/(Fintype.card I:ℝ))^(Fintype.card I)-(1-1/(Fintype.card I:ℝ))^(Fintype.card I-1))*(adsR blue red).card := by
  classical
  have ha : ∀ ω : Fin (Fintype.card I) → I, ALG blue red ω =
      (univ.filter fun a => Occupancy.Success (neighborTypes blue a) (neighborTypes red a) ω).card := by
    intro ω
    rw [ALG_edges D]
    apply congrArg Finset.card
    apply filter_congr
    intro a _
    simp only [Occupancy.Success,neighborTypes,mem_filter,mem_univ,true_and]
    rfl
  simp_rw [ha]
  rw [Occupancy.avg_card_filter]
  have hh := fun a => Occupancy.success_classes (neighborTypes blue a) (neighborTypes red a)
    (neighborTypes_disjoint D a) (neighborTypes_cases D a)
  simp only [neighborTypes_card] at hh
  simp_rw [hh]
  rw [sum_add_distrib,sum_add_distrib,sum_add_distrib]
  simp only [← sum_filter]
  simp only [sum_const,nsmul_eq_mul]
  unfold adsBB adsBR adsB adsR
  ring

end TSMProof

namespace OnlineStochMatching.TSM

/-- **Theorem 5**, first sentence, for `e_i = 1` (Feldman, Mehta, Mirrokni, Muthukrishnan, *Online
Stochastic Matching: Beating 1-1/e*, arXiv:0905.4100v1, §4.2, p. 6; proof §4.2.4, p. 9). Let
`α = (1 - 2/e²)/(4/3 - 2/(3e))`. The statement is the conjunction of
* (a) the two suggested matchings algorithm is well defined: every maximum flow edge set `E_f` of
  the boosted flow graph admits a TSM colouring;
* (b) for every `ε > 0` and `c > 0` there are `δ > 0` and `N` such that for every instance with
  `e_i = 1` and `n = |I| ≥ N`, every maximum flow edge set `E_f` and every TSM colouring of it, with
  probability at least `1 - e^{-δ n}` over the `n` i.i.d. uniform arrivals: if `OPT ≥ c n` then
  `ALG ≥ (α - ε) OPT`;
* (c) `α > 1 - 1/e`.

Correction to the page: the theorem prints `ALG/OPT - ε ≥ α`; its proof ends with
`ALG/OPT + ε ≥ α` (p. 9), and the tightness family of §4.2.5 has ratio close to `α`, so the
printed form is false. "As long as OPT = Ω(n)" is the event `OPT ≥ c n` with `c > 0` arbitrary;
`δ` and `N` depend on `ε` and `c` only. -/
theorem theorem_5 :
    (∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F : Finset (A × I)),
        IsMaxFlowSet E F → ∃ blue red : Finset (A × I), IsTSMColoring F blue red) ∧
    (∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F blue red : Finset (A × I)),
        N ≤ Fintype.card I → IsMaxFlowSet E F → IsTSMColoring F blue red →
        1 - Real.exp (-δ * Fintype.card I) ≤
          prob (Fintype.card I) (fun ω : Fin (Fintype.card I) → I =>
            c * Fintype.card I ≤ (OPT E ω : ℝ) →
              (alpha - ε) * (OPT E ω : ℝ) ≤ (ALG blue red ω : ℝ))) ∧
    1 - Real.exp (-1) < alpha := by
  classical
  refine ⟨?_,?_,TSMProof.alpha_beats_classical⟩
  · intro A I _ _ _ _ E F hF
    exact TSMProof.coloring_exists E F hF.1
  · intro ε hε c hc
    obtain ⟨δ,hδ,N,hN,hall⟩ := TSMProof.probability_closure ε c hε hc
    refine ⟨δ,hδ,N,?_⟩
    intro A I _ _ _ _ E F blue red hn hF hcol
    have hn0 : 0 < Fintype.card I := by omega
    let : Nonempty I := Fintype.card_pos_iff.mp hn0
    obtain ⟨D⟩ := TSMProof.coloring_data hcol
    apply hall I (Fintype.card I) hn
      (fun ω => (ALG blue red ω : ℝ)) (fun ω => (OPT E ω : ℝ))
      (adsBR blue red).card (adsBB blue red).card (adsB blue red).card
      (adsR blue red).card (Edelta E F).card
    · exact TSMProof.ALG_oscillation blue red
    · exact TSMProof.OPT_oscillation E
    · positivity
    · positivity
    · positivity
    · positivity
    · positivity
    · exact_mod_cast D.red_le_blue
    · exact_mod_cast D.class_card_bound
    · exact_mod_cast (Finset.card_le_card (TSMProof.crossing_subset_flow E F)).trans D.total_edges_bound
    · exact_mod_cast TSMProof.cut_packing hF D
    · exact TSMProof.expected_ALG D
    · exact TSMProof.expected_OPT_bound hF D


end OnlineStochMatching.TSM

open OnlineStochMatching.TSM
theorem solution :
    (∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F : Finset (A × I)),
        IsMaxFlowSet E F → ∃ blue red : Finset (A × I), IsTSMColoring F blue red) ∧
    (∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E F blue red : Finset (A × I)),
        N ≤ Fintype.card I → IsMaxFlowSet E F → IsTSMColoring F blue red →
        1 - Real.exp (-δ * Fintype.card I) ≤
          prob (Fintype.card I) (fun ω : Fin (Fintype.card I) → I =>
            c * Fintype.card I ≤ (OPT E ω : ℝ) →
              (alpha - ε) * (OPT E ω : ℝ) ≤ (ALG blue red ω : ℝ))) ∧
    1 - Real.exp (-1) < alpha := OnlineStochMatching.TSM.theorem_5
