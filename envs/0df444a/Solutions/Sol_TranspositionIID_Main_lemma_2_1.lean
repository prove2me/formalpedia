-- Prove2me | solution 1 for TranspositionIID.Main.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:35:33.634297+00:00
-- url     : https://prove2.me/submissions/0ca900db-7bae-4237-ad75-073bf38afd8f

import Mathlib
import Definitions.Def_TranspositionIID_Main_Buffer

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L21
open TranspositionIID.Main Set

variable {n : ℕ}

noncomputable def Phi (p : Fin n → ℝ) (x r : ℝ) : ℝ := ∑ i, max (r - |x - Real.log (p i)|) 0

def Sset (p : Fin n → ℝ) (x : ℝ) : Set ℝ := {r | 0 ≤ r ∧ 1 ≤ Phi p x r}

lemma root_eq (p : Fin n → ℝ) (x : ℝ) : bufferRoot p x = sInf (Sset p x) := rfl

lemma Phi_cont (p : Fin n → ℝ) (x : ℝ) : Continuous (Phi p x) := by
  unfold Phi; fun_prop

lemma Phi_zero (p : Fin n → ℝ) (x : ℝ) : Phi p x 0 = 0 := by
  unfold Phi
  apply Finset.sum_eq_zero; intro i _
  apply max_eq_right; linarith [abs_nonneg (x - Real.log (p i))]

lemma Phi_le (p : Fin n → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) : Phi p x r ≤ n * r := by
  unfold Phi
  calc ∑ i, max (r - |x - Real.log (p i)|) 0 ≤ ∑ _i : Fin n, r :=
        Finset.sum_le_sum fun i _ => max_le (by linarith [abs_nonneg (x - Real.log (p i))]) hr
    _ = n * r := by simp

lemma Phi_ge (p : Fin n → ℝ) (x : ℝ) (i0 : Fin n) (r : ℝ) :
    r - |x - Real.log (p i0)| ≤ Phi p x r := by
  unfold Phi
  exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (r - |x - Real.log (p i)|) 0)
    (fun i _ => le_max_right _ _) (Finset.mem_univ i0))

lemma Sset_nonempty (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : (Sset p x).Nonempty := by
  refine ⟨1 + |x - Real.log (p ⟨0, hn⟩)|, by positivity, ?_⟩
  have := Phi_ge p x ⟨0, hn⟩ (1 + |x - Real.log (p ⟨0, hn⟩)|)
  linarith

lemma Sset_closed (p : Fin n → ℝ) (x : ℝ) : IsClosed (Sset p x) :=
  isClosed_Ici.inter (isClosed_le continuous_const (Phi_cont p x))

lemma Sset_bdd (p : Fin n → ℝ) (x : ℝ) : BddBelow (Sset p x) := ⟨0, fun r hr => hr.1⟩

lemma root_le (p : Fin n → ℝ) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) (h : 1 ≤ Phi p x r) :
    bufferRoot p x ≤ r := csInf_le (Sset_bdd p x) ⟨hr, h⟩

lemma root_spec (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) :
    0 < bufferRoot p x ∧ Phi p x (bufferRoot p x) = 1 := by
  have hmem := (Sset_closed p x).csInf_mem (Sset_nonempty hn p x) (Sset_bdd p x)
  rw [← root_eq] at hmem
  obtain ⟨hR0, h1⟩ := hmem
  set R := bufferRoot p x with hR
  have hivt := intermediate_value_Icc hR0 (Phi_cont p x).continuousOn
  have h1mem : (1 : ℝ) ∈ Icc (Phi p x 0) (Phi p x R) := by
    rw [Phi_zero]; exact ⟨zero_le_one, h1⟩
  obtain ⟨r, hr, hr1⟩ := hivt h1mem
  have hRr : R ≤ r := root_le p x hr.1 (by rw [hr1])
  have hrR : r = R := le_antisymm hr.2 hRr
  have hPhi : Phi p x R = 1 := by rw [← hrR]; exact hr1
  refine ⟨lt_of_le_of_ne hR0 (fun h0 => ?_), hPhi⟩
  rw [← h0, Phi_zero] at hPhi; norm_num at hPhi

lemma root_lip (hn : 1 ≤ n) (p : Fin n → ℝ) (x z : ℝ) :
    bufferRoot p z ≤ bufferRoot p x + |z - x| := by
  obtain ⟨hR0, hPhi⟩ := root_spec hn p x
  apply root_le p z (by positivity)
  have : Phi p x (bufferRoot p x) ≤ Phi p z (bufferRoot p x + |z - x|) := by
    unfold Phi
    apply Finset.sum_le_sum; intro i _
    apply max_le_max _ le_rfl
    have h1 : |z - Real.log (p i)| ≤ |z - x| + |x - Real.log (p i)| := by
      have := abs_add_le (z - x) (x - Real.log (p i))
      simpa using this
    linarith
  linarith

lemma root_abs (hn : 1 ≤ n) (p : Fin n → ℝ) (x z : ℝ) :
    |bufferRoot p x - bufferRoot p z| ≤ |x - z| := by
  have h1 := root_lip hn p x z
  have h2 := root_lip hn p z x
  rw [abs_sub_comm z x] at h1
  rw [abs_le]; constructor <;> linarith

lemma buffer_lip (hn : 1 ≤ n) (p : Fin n → ℝ) : LipschitzWith (1 / 2 : NNReal) (buffer p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [Real.dist_eq, buffer]
  have h := abs_min_sub_min_le_max 1 (bufferRoot p x) 1 (bufferRoot p z)
  have h2 := root_abs hn p x z
  have : max |(1:ℝ) - 1| |bufferRoot p x - bufferRoot p z| ≤ |x - z| := by
    apply max_le (by simp) h2
  calc |1 / 2 * min 1 (bufferRoot p x) - 1 / 2 * min 1 (bufferRoot p z)|
      = 1 / 2 * |min 1 (bufferRoot p x) - min 1 (bufferRoot p z)| := by
        rw [← mul_sub, abs_mul]; norm_num
    _ ≤ 1 / 2 * |x - z| := by
        apply mul_le_mul_of_nonneg_left (h.trans this) (by norm_num)
    _ = ((1 / 2 : NNReal) : ℝ) * |x - z| := by norm_num

lemma buffer_le (p : Fin n → ℝ) (x : ℝ) : buffer p x ≤ 1 / 2 := by
  unfold buffer; have := min_le_left 1 (bufferRoot p x); linarith

lemma buffer_ge (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : 1 / (2 * (n : ℝ)) ≤ buffer p x := by
  obtain ⟨hR0, hPhi⟩ := root_spec hn p x
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 ≤ (n : ℝ) * bufferRoot p x := by
    have := Phi_le p x hR0.le; linarith
  have h2 : 1 / (n : ℝ) ≤ bufferRoot p x := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h3 : 1 / (n : ℝ) ≤ min 1 (bufferRoot p x) := by
    apply le_min _ h2
    rw [div_le_one (by linarith)]; exact hn'
  unfold buffer
  calc 1 / (2 * (n : ℝ)) = 1 / 2 * (1 / (n : ℝ)) := by field_simp
    _ ≤ 1 / 2 * min 1 (bufferRoot p x) := mul_le_mul_of_nonneg_left h3 (by norm_num)

lemma buffer_pos (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) : 0 < buffer p x := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (buffer_ge hn p x)

end TranspositionIID.Main.Dev.L21
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L21
open MeasureTheory Set

noncomputable def Bf (θ y x : ℝ) : ℝ := 8 * θ / (max θ |x - y|) ^ 2

lemma Bf_nonneg {θ : ℝ} (hθ : 0 < θ) (y x : ℝ) : 0 ≤ Bf θ y x := by
  unfold Bf; positivity

lemma Bf_cont {θ : ℝ} (hθ : 0 < θ) (y : ℝ) : Continuous (Bf θ y) := by
  unfold Bf
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x; have : 0 < max θ |x - y| := lt_max_of_lt_left hθ
  positivity

lemma Bf_le {θ : ℝ} (hθ : 0 < θ) (y x : ℝ) : Bf θ y x ≤ 8 * (θ + 1 / θ) * (1 + (x - y) ^ 2)⁻¹ := by
  unfold Bf
  have hM : θ ≤ max θ |x - y| := le_max_left _ _
  have hM2 : |x - y| ≤ max θ |x - y| := le_max_right _ _
  have hMpos : 0 < max θ |x - y| := lt_of_lt_of_le hθ hM
  rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (x - y) ^ 2 ≤ (max θ |x - y|) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM2 2
  have h2 : θ ^ 2 ≤ (max θ |x - y|) ^ 2 := pow_le_pow_left₀ hθ.le hM 2
  have e : 8 * (θ + 1 / θ) * (max θ |x - y|) ^ 2 = 8 * θ * (max θ |x - y|) ^ 2 + 8 / θ * (max θ |x - y|) ^ 2 := by
    field_simp
  rw [e]
  have h3 : 8 * θ * (1 + (x - y) ^ 2) ≤ 8 * θ * (max θ |x - y|) ^ 2 + 8 / θ * (max θ |x - y|) ^ 2 := by
    have h4 : 8 * θ * (1 + (x - y) ^ 2) = 8 * θ + 8 * θ * (x - y) ^ 2 := by ring
    have h5 : 8 * θ ≤ 8 / θ * (max θ |x - y|) ^ 2 := by
      have : 8 * θ = 8 / θ * θ ^ 2 := by field_simp
      rw [this]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    have h6 : 8 * θ * (x - y) ^ 2 ≤ 8 * θ * (max θ |x - y|) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  exact h3

lemma Bf_integrable {θ : ℝ} (hθ : 0 < θ) (y : ℝ) : Integrable (Bf θ y) := by
  have h1 : Integrable (fun x : ℝ => (1 + (x - y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_sub_right y
  have h2 := h1.const_mul (8 * (θ + 1 / θ))
  refine Integrable.mono' h2 (Bf_cont hθ y).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Bf_nonneg hθ y x)]
  exact Bf_le hθ y x

lemma Bf_integral {θ : ℝ} (hθ : 0 < θ) (y : ℝ) : ∫ x, Bf θ y x = 32 := by
  have e1 : ∫ x, Bf θ y x = ∫ u, (fun v : ℝ => 8 * θ / (max θ v) ^ 2) |u| := by
    have := integral_sub_right_eq_self (μ := volume) (fun u : ℝ => 8 * θ / (max θ |u|) ^ 2) y
    exact this
  rw [e1, integral_comp_abs (f := fun v : ℝ => 8 * θ / (max θ v) ^ 2)]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 θ ∪ Ioi θ := (Set.Ioc_union_Ioi_eq_Ioi hθ.le).symm
  have hfa : ∀ x ∈ Ioc 0 θ, 8 * θ / (max θ x) ^ 2 = 8 / θ := by
    intro x hx
    rw [max_eq_left hx.2]; field_simp
  have hfb : ∀ x ∈ Ioi θ, 8 * θ / (max θ x) ^ 2 = 8 * θ * x ^ (-2 : ℝ) := by
    intro x hx
    have hx' : θ < x := hx
    rw [max_eq_right hx'.le, Real.rpow_neg (by linarith), Real.rpow_two]
    field_simp
  have hI1 : IntegrableOn (fun v : ℝ => 8 * θ / (max θ v) ^ 2) (Ioc 0 θ) := by
    have : IntegrableOn (fun _ : ℝ => 8 / θ) (Ioc 0 θ) := by
      apply integrableOn_const (by simp)
    exact this.congr_fun (fun x hx => (hfa x hx).symm) measurableSet_Ioc
  have hI2 : IntegrableOn (fun v : ℝ => 8 * θ / (max θ v) ^ 2) (Ioi θ) := by
    have : IntegrableOn (fun x : ℝ => 8 * θ * x ^ (-2 : ℝ)) (Ioi θ) :=
      (integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hθ).const_mul (8 * θ)
    exact this.congr_fun (fun x hx => (hfb x hx).symm) measurableSet_Ioi
  rw [hsplit, setIntegral_union (Set.disjoint_left.2 fun x hx hx' => by
      have := hx.2; have := hx'; simp only [mem_Ioi] at *; linarith) measurableSet_Ioi hI1 hI2]
  rw [setIntegral_congr_fun measurableSet_Ioc hfa, setIntegral_congr_fun measurableSet_Ioi hfb]
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hθ]
  simp only [setIntegral_const, Real.volume_real_Ioc, smul_eq_mul]
  rw [max_eq_left (by linarith)]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp
  ring

end TranspositionIID.Main.Dev.L21
end

section
set_option autoImplicit false

namespace TranspositionIID.Main.Dev.L21
open TranspositionIID.Main MeasureTheory Set

variable {n : ℕ}

lemma buffer_dist (hn : 1 ≤ n) (p : Fin n → ℝ) (x y : ℝ) :
    |buffer p x - buffer p y| ≤ 1 / 2 * |x - y| := by
  have h := (buffer_lip hn p).dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at h
  have e : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  rw [e] at h; exact h

lemma term_bound (hn : 1 ≤ n) (p : Fin n → ℝ) (hpos : ∀ i, 0 < p i) (i : Fin n) (x : ℝ) :
    Real.exp x * (max (2 * buffer p x - |x - Real.log (p i)|) 0 / buffer p x ^ 2) ≤
      Real.exp 1 * p i * Bf (buffer p (Real.log (p i))) (Real.log (p i)) x := by
  set y := Real.log (p i) with hy
  set θx := buffer p x with hθx
  set θi := buffer p y with hθi
  have hθip : 0 < θi := buffer_pos hn p y
  have hθxp : 0 < θx := buffer_pos hn p x
  have hθxle : θx ≤ 1 / 2 := buffer_le p x
  by_cases h : 2 * θx - |x - y| ≤ 0
  · rw [max_eq_right h]
    have := Bf_nonneg hθip y x
    have := hpos i
    simp only [zero_div, mul_zero]; positivity
  · push Not at h
    rw [max_eq_left h.le]
    set δ := |x - y| with hδ
    have hδ1 : δ < 1 := by linarith
    have hexp : Real.exp x ≤ Real.exp 1 * p i := by
      have h1 : x ≤ y + 1 := by linarith [le_abs_self (x - y)]
      calc Real.exp x ≤ Real.exp (y + 1) := Real.exp_le_exp.2 h1
        _ = Real.exp 1 * p i := by rw [Real.exp_add, hy, Real.exp_log (hpos i)]; ring
    have hlip := buffer_dist hn p x y
    rw [← hδ] at hlip
    have hlip' := (abs_le.1 hlip)
    have hnum : 2 * θx - δ ≤ 2 * θi := by linarith [hlip'.2]
    have hden : max θi δ ≤ 2 * θx := by
      rcases le_total δ θi with hc | hc
      · rw [max_eq_left hc]; linarith [hlip'.1]
      · rw [max_eq_right hc]; linarith
    have hMpos : 0 < max θi δ := lt_of_lt_of_le hθip (le_max_left _ _)
    have hθx2 : (max θi δ / 2) ^ 2 ≤ θx ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have hq : (2 * θx - δ) / θx ^ 2 ≤ 8 * θi / (max θi δ) ^ 2 := by
      calc (2 * θx - δ) / θx ^ 2 ≤ (2 * θi) / ((max θi δ / 2) ^ 2) :=
            div_le_div₀ (by positivity) hnum (by positivity) hθx2
        _ = 8 * θi / (max θi δ) ^ 2 := by field_simp; ring
    unfold Bf
    rw [← hδ]
    calc Real.exp x * ((2 * θx - δ) / θx ^ 2)
        ≤ (Real.exp 1 * p i) * (8 * θi / (max θi δ) ^ 2) :=
          mul_le_mul hexp hq (by positivity) (by have := hpos i; positivity)
      _ = _ := by ring

lemma sum_bound (hn : 1 ≤ n) (p : Fin n → ℝ) (x : ℝ) :
    Real.exp x / buffer p x ^ 2 ≤ 4 * Real.exp x +
      ∑ i, Real.exp x * (max (2 * buffer p x - |x - Real.log (p i)|) 0 / buffer p x ^ 2) := by
  have hnn : 0 ≤ ∑ i, Real.exp x * (max (2 * buffer p x - |x - Real.log (p i)|) 0 / buffer p x ^ 2) :=
    Finset.sum_nonneg fun i _ => by
      have := buffer_pos hn p x
      positivity
  by_cases hR : 1 ≤ bufferRoot p x
  · have : buffer p x = 1 / 2 := by
      unfold buffer; rw [min_eq_left hR]; norm_num
    have e : Real.exp x / buffer p x ^ 2 = 4 * Real.exp x := by rw [this]; ring
    linarith
  · push Not at hR
    have hb : buffer p x = 1 / 2 * bufferRoot p x := by
      unfold buffer; rw [min_eq_right hR.le]
    have h2 : 2 * buffer p x = bufferRoot p x := by rw [hb]; ring
    obtain ⟨_, hPhi⟩ := root_spec hn p x
    have hsum : ∑ i, Real.exp x * (max (2 * buffer p x - |x - Real.log (p i)|) 0 / buffer p x ^ 2) =
        Real.exp x / buffer p x ^ 2 := by
      rw [h2]
      have : ∑ i, Real.exp x * (max (bufferRoot p x - |x - Real.log (p i)|) 0 / buffer p x ^ 2) =
          Real.exp x / buffer p x ^ 2 * Phi p x (bufferRoot p x) := by
        unfold Phi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [this, hPhi, mul_one]
    rw [hsum]
    have := Real.exp_pos x
    linarith

end TranspositionIID.Main.Dev.L21
end

section
set_option autoImplicit false

namespace TranspositionIID.Main
open TranspositionIID.Main.Dev.L21 MeasureTheory Set

theorem chk_lemma_2_1 {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ)
    (hp : ActuarialValuation.isFiniteStateDistribution p)
    (hsort : Decreasing p) (hpos : ∀ i, 0 < p i) :
    LipschitzWith (1 / 2 : NNReal) (buffer p) ∧
    (∀ x : ℝ, 1 / (2 * (n : ℝ)) ≤ buffer p x ∧ buffer p x ≤ 1 / 2) ∧
    MeasureTheory.IntegrableOn (fun x : ℝ => Real.exp x / buffer p x ^ 2) (Set.Iic 0) ∧
    (∫ x : ℝ in Set.Iic 0, Real.exp x / buffer p x ^ 2) ≤ 4 + 32 * Real.exp 1 := by
  have hlip := buffer_lip hn p
  refine ⟨hlip, fun x => ⟨buffer_ge hn p x, buffer_le p x⟩, ?_⟩
  set F : ℝ → ℝ := fun x => 4 * Real.exp x +
    ∑ i, Real.exp 1 * p i * Bf (buffer p (Real.log (p i))) (Real.log (p i)) x with hF
  have hθpos : ∀ x, 0 < buffer p x := buffer_pos hn p
  have hfcont : Continuous (fun x : ℝ => Real.exp x / buffer p x ^ 2) := by
    apply Continuous.div Real.continuous_exp (hlip.continuous.pow 2)
    intro x; exact (pow_pos (hθpos x) 2).ne'
  have hfle : ∀ x, Real.exp x / buffer p x ^ 2 ≤ F x := by
    intro x
    have h1 := sum_bound hn p x
    have h2 : ∑ i, Real.exp x * (max (2 * buffer p x - |x - Real.log (p i)|) 0 / buffer p x ^ 2) ≤
        ∑ i, Real.exp 1 * p i * Bf (buffer p (Real.log (p i))) (Real.log (p i)) x :=
      Finset.sum_le_sum fun i _ => term_bound hn p hpos i x
    simp only [hF]; linarith
  have hBint : ∀ i, Integrable (fun x => Real.exp 1 * p i * Bf (buffer p (Real.log (p i))) (Real.log (p i)) x) :=
    fun i => (Bf_integrable (hθpos _) _).const_mul _
  have hFint : IntegrableOn F (Iic 0) := by
    have h1 : IntegrableOn (fun x : ℝ => 4 * Real.exp x) (Iic 0) :=
      (integrableOn_exp_Iic 0).const_mul 4
    have h2 : IntegrableOn (fun x : ℝ => ∑ i, Real.exp 1 * p i *
        Bf (buffer p (Real.log (p i))) (Real.log (p i)) x) (Iic 0) :=
      (integrable_finsetSum _ fun i _ => hBint i).integrableOn
    exact h1.add h2
  have hfint : IntegrableOn (fun x : ℝ => Real.exp x / buffer p x ^ 2) (Iic 0) := by
    refine Integrable.mono' hFint hfcont.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have := hθpos x
    rw [Real.norm_of_nonneg (by positivity)]
    exact hfle x
  refine ⟨hfint, ?_⟩
  have hmono : ∫ x in Iic 0, Real.exp x / buffer p x ^ 2 ≤ ∫ x in Iic 0, F x :=
    setIntegral_mono hfint hFint hfle
  refine hmono.trans ?_
  have h1 : IntegrableOn (fun x : ℝ => 4 * Real.exp x) (Iic 0) :=
    (integrableOn_exp_Iic 0).const_mul 4
  have h2 : IntegrableOn (fun x : ℝ => ∑ i, Real.exp 1 * p i *
      Bf (buffer p (Real.log (p i))) (Real.log (p i)) x) (Iic 0) :=
    (integrable_finsetSum _ fun i _ => hBint i).integrableOn
  simp only [hF]
  rw [integral_add h1 h2, integral_const_mul, integral_exp_Iic_zero,
    integral_finsetSum _ fun i _ => (hBint i).integrableOn]
  have hi : ∀ i, ∫ x in Iic 0, Real.exp 1 * p i * Bf (buffer p (Real.log (p i))) (Real.log (p i)) x ≤
      Real.exp 1 * p i * 32 := by
    intro i
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (by have := hpos i; positivity)
    calc ∫ x in Iic 0, Bf (buffer p (Real.log (p i))) (Real.log (p i)) x
        ≤ ∫ x, Bf (buffer p (Real.log (p i))) (Real.log (p i)) x :=
          setIntegral_le_integral (Bf_integrable (hθpos _) _)
            (ae_of_all _ fun x => Bf_nonneg (hθpos _) _ x)
      _ = 32 := Bf_integral (hθpos _) _
  calc 4 * 1 + ∑ i, ∫ x in Iic 0, Real.exp 1 * p i * Bf (buffer p (Real.log (p i))) (Real.log (p i)) x
      ≤ 4 * 1 + ∑ i, Real.exp 1 * p i * 32 := by
        apply add_le_add le_rfl (Finset.sum_le_sum fun i _ => hi i)
    _ = 4 + 32 * Real.exp 1 := by
        have : ∑ i, Real.exp 1 * p i * 32 = Real.exp 1 * 32 * ∑ i, p i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        rw [this, hp.2]; ring

end TranspositionIID.Main
end

theorem solution : type_of% @TranspositionIID.Main.chk_lemma_2_1 := @TranspositionIID.Main.chk_lemma_2_1
