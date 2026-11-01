-- Prove2me | solution 1 for PGDMap20261031.pgd_prefix_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-01T04:05:06.143986+00:00
-- url     : https://prove2.me/submissions/64c2ffb7-c624-44c4-9737-b113eff4de97

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Curves
import Definitions.Def_PGDMap20261031_PGD
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxRecDepth 4000

open PGDMap20261031 Set
open scoped BigOperators
noncomputable section
namespace Prefix

def ss (n : ℕ) (a : ℝ) : ℝ := ∑ j ∈ Finset.range n, a ^ j
def ee (b t : ℝ) (n : ℕ) : ℝ := (b / t) * (b / t - 1) * ss n ((b / t) ^ 2)
def aa (b : ℝ) (n : ℕ) : ℝ := b * (b + 1) * ss n (b ^ 2)
def tt (b t : ℝ) (n : ℕ) : ℝ := aa b n - ee b t n

lemma ss_zero (a : ℝ) : ss 0 a = 0 := by simp [ss]
lemma ss_succ (n : ℕ) (a : ℝ) : ss (n+1) a = ss n a + a^n := by
  simp [ss, Finset.sum_range_succ]
lemma ss_rec (n : ℕ) (a : ℝ) : ss (n+1) a = a * ss n a + 1 := by
  simp [ss, Finset.sum_range_succ', pow_succ, Finset.mul_sum, mul_comm]
lemma ss_geom (n : ℕ) (a : ℝ) : (a-1)*ss n a = a^n-1 := by
  induction n with
  | zero => simp [ss]
  | succ n ih => rw [ss_succ, mul_add, ih, pow_succ]; ring
lemma ss_nonneg (n : ℕ) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ ss n a := by
  exact Finset.sum_nonneg (fun j _ => pow_nonneg ha j)
lemma ss_pos (n : ℕ) (a : ℝ) (hn : 1 ≤ n) (ha : 0 ≤ a) : 0 < ss n a := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [ss_rec]
  positivity [ss_nonneg m a ha]
lemma ss_mono (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : ss n a ≤ ss n b := by
  exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ ha hab j)

lemma ss_cross (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ss n b * ss (n+1) a ≤ ss (n+1) b * ss n a := by
  have H : a^n * ss n b ≤ b^n * ss n a := by
    rw [ss, ss, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    have hp := pow_le_pow_left₀ ha hab (n-j)
    have hf := mul_nonneg (pow_nonneg ha j) (pow_nonneg (le_trans ha hab) j)
    have hm := mul_le_mul_of_nonneg_left hp hf
    have he : n = j + (n-j) := by omega
    rw [he, pow_add, pow_add]
    nlinarith only [hm]
  rw [ss_succ, ss_succ]
  nlinarith only [H]

lemma aa_pos (b : ℝ) (hb : 1 ≤ b) (n : ℕ) (hn : 1 ≤ n) : 0 < aa b n := by
  unfold aa
  exact mul_pos (mul_pos (by linarith) (by linarith)) (ss_pos n _ hn (sq_nonneg b))
lemma ee_nonneg (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1) (n : ℕ) :
    0 ≤ ee b t n := by
  have hu : 1 ≤ b/t := (le_div_iff₀ ht.1).2 (by linarith [ht.2])
  unfold ee
  exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (ss_nonneg _ _ (sq_nonneg _))
lemma ee_rec (b t : ℝ) (ht : t ≠ 0) (n : ℕ) :
    ee b t (n+1) = b^2/t^2 * ee b t n + b*(b-t)/t^2 := by
  unfold ee
  rw [ss_rec]
  field_simp
  <;> ring
lemma aa_rec (b : ℝ) (n : ℕ) : aa b (n+1) = b^2*aa b n+b*(b+1) := by
  unfold aa
  rw [ss_rec]
  ring
lemma tt_rec (b t : ℝ) (n : ℕ) :
    tt b t (n+1) = b^2*(ee b t n + tt b t n)+b*(b+1)-ee b t (n+1) := by
  simp only [tt, aa_rec]
  ring

lemma ratios_mono (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1) :
    Monotone (fun n : ℕ => ee b t (n+1) / aa b (n+1)) := by
  have hub : b ≤ b/t := (le_div_iff₀ ht.1).2 (by nlinarith [ht.2])
  have huu : 1 ≤ b/t := le_trans hb hub
  have hsq : b^2 ≤ (b/t)^2 := by nlinarith
  apply monotone_nat_of_le_succ
  intro n
  apply (div_le_div_iff₀ (aa_pos b hb _ (by omega)) (aa_pos b hb _ (by omega))).2
  have H := ss_cross (n+1) (sq_nonneg b) hsq
  have hc : 0 ≤ (b/t)*(b/t-1) * (b*(b+1)) := by positivity
  have Hm := mul_le_mul_of_nonneg_left H hc
  dsimp [ee,aa]
  nlinarith only [Hm]

lemma tt_nonneg_prefix (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1)
    (k : ℕ) (hk : 1 ≤ k) (hTk : 0 ≤ tt b t k) (i : ℕ) (hi : i ≤ k) :
    0 ≤ tt b t i := by
  by_cases hz : i=0
  · subst i; simp [tt,aa,ee,ss]
  · have hip : 1 ≤ i := by omega
    have H := ratios_mono b t hb ht (show i-1 ≤ k-1 by omega)
    dsimp only at H
    rw [Nat.sub_add_cancel hip, Nat.sub_add_cancel hk] at H
    have Hk : ee b t k / aa b k ≤ 1 := by
      apply (div_le_one (aa_pos b hb k hk)).2
      dsimp [tt] at hTk
      linarith
    have Hi := le_trans H Hk
    have Hie := (div_le_one (aa_pos b hb i hip)).1 Hi
    unfold tt
    linarith

lemma delta_nonneg (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1) (n : ℕ) :
    0 ≤ (1+t)*ee b t n - (b-1)*tt b t n := by
  have hu : b ≤ b/t := (le_div_iff₀ ht.1).2 (by nlinarith [ht.2])
  have hs : b^2 ≤ (b/t)^2 := by nlinarith
  have Hp := pow_le_pow_left₀ (sq_nonneg b) hs n
  have G1 := ss_geom n ((b/t)^2)
  have G2 := ss_geom n (b^2)
  have H1 : (b+t)*ee b t n = b*((b/t)^(2*n)-1) := by
    unfold ee
    rw [pow_mul]
    calc
      _ = b*(((b/t)^2-1)*ss n ((b/t)^2)) := by field_simp [ht.1.ne'] <;> ring
      _ = _ := by rw [G1]
  have H2 : (b-1)*aa b n = b*(b^(2*n)-1) := by
    unfold aa
    rw [pow_mul]
    calc
      _ = b*((b^2-1)*ss n (b^2)) := by ring
      _ = _ := by rw [G2]
  rw [← pow_mul, ← pow_mul] at Hp
  unfold tt
  nlinarith only [mul_nonneg (by linarith : 0 ≤ b) (sub_nonneg.mpr Hp),H1,H2]

lemma ee_antitone (b : ℝ) (hb : 1 ≤ b) : AntitoneOn (fun t => ee b t) (Ioo (0:ℝ) 1) := by
  intro t ht u hu htu n
  have hdiv : b/u ≤ b/t := div_le_div_of_nonneg_left (by linarith) ht.1 htu
  have hlu : 1 ≤ b/u := (le_div_iff₀ hu.1).2 (by linarith [hu.2])
  have hsq : (b/u)^2 ≤ (b/t)^2 := by nlinarith
  have hc : (b/u)*(b/u-1) ≤ (b/t)*(b/t-1) := by nlinarith
  exact mul_le_mul hc (ss_mono n (sq_nonneg _) hsq)
    (ss_nonneg _ _ (sq_nonneg _)) (by nlinarith)

lemma crossing_exists (b : ℝ) (hb : 1 ≤ b) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t ∈ Ioo (0:ℝ) 1, ee b t k = aa b k := by
  let l := b/(b+1)
  have hb0 : 0 < b := by linarith
  have hbp : 0 < b+1 := by linarith
  have hl : 0 < l := div_pos hb0 hbp
  have hl1 : l < 1 := (div_lt_one hbp).2 (by linarith)
  have he : b/l = b+1 := by dsimp [l]; field_simp <;> ring
  have Hl : aa b k ≤ ee b l k := by
    dsimp [ee,aa]
    rw [he]
    have H := ss_mono k (sq_nonneg b) (show b^2 ≤ (b+1)^2 by nlinarith)
    have Hm := mul_le_mul_of_nonneg_left H (show 0 ≤ b*(b+1) by positivity)
    nlinarith only [Hm]
  have H1 : ee b 1 k < aa b k := by
    dsimp [ee,aa]
    simp only [div_one]
    have Hs := ss_pos k (b^2) hk (sq_nonneg b)
    nlinarith only [mul_pos hb0 Hs]
  have hc : ContinuousOn (fun t => ee b t k) (Icc l 1) := by
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt (lt_of_lt_of_le hl hz.1)
    unfold ee ss
    fun_prop
  obtain ⟨t,ht,Ht⟩ := intermediate_value_Icc' (le_of_lt hl1) hc ⟨H1.le,Hl⟩
  refine ⟨t,⟨lt_of_lt_of_le hl ht.1,?_⟩,Ht⟩
  by_contra hn
  have heq : t=1 := by linarith [ht.2]
  rw [heq] at Ht
  linarith

lemma sum_pairs (k : ℕ) (a : ℝ) :
    (∑ j ∈ Finset.Icc 1 (2*k), a^j) = a*(a+1)*ss k (a^2) := by
  induction k with
  | zero => simp [ss]
  | succ k ih =>
    rw [show 2*(k+1)=2*k+1+1 by omega,
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih,
      ss_succ, pow_add a (2*k) 1, pow_add a (2*k) 2, pow_mul]
    simp only [pow_one]
    ring

lemma geometric_aa (b : ℝ) (k : ℕ) : geometricSum k (1/b) = aa b k := by
  simp only [geometricSum,one_div,inv_pow,inv_inv]
  exact sum_pairs k b

lemma geometric_ee (b t : ℝ) (k : ℕ) : geometricSum k (-t/b) = ee b t k := by
  simp only [geometricSum,← inv_pow]
  rw [sum_pairs]
  have hinv : (-t/b)⁻¹ = -(b/t) := by simp [div_eq_mul_inv,mul_comm]
  rw [hinv,neg_sq]
  unfold ee
  ring

lemma choose_parameters (h q : ℝ) (hh : validStep h) (hq : 0 ≤ q)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ t ∈ Ioo (0:ℝ) 1, h ≤ 1+t ∧ 0 ≤ tt (base h q) t k ∧
      prefixCoefficient k h q ≤ base h q/(2*h)*ee (base h q) t k := by
  let b := base h q
  have hb : 1 ≤ b := by dsimp [b,base]; nlinarith [hh.1]
  have hbpos : 0 < b := by linarith
  have hc : 0 ≤ b/(2*h) := by positivity [hh.1]
  obtain ⟨t,ht,Ht⟩ := crossing_exists b hb k hk
  by_cases hsmall : h ≤ 1+t
  · refine ⟨t,ht,hsmall,?_,?_⟩
    · change 0 ≤ aa b k - ee b t k
      rw [Ht]
      simp
    · change prefixCoefficient k h q ≤ b/(2*h)*ee b t k
      rw [Ht]
      unfold prefixCoefficient
      change b/(2*h)*(if h=1 then geometricSum k (1/b) else
        min (geometricSum k (1/b)) (geometricSum k ((1-h)/b))) ≤ b/(2*h)*aa b k
      apply mul_le_mul_of_nonneg_left _ hc
      by_cases hz : h=1
      · simp only [if_pos hz,geometric_aa]; exact le_rfl
      · rw [if_neg hz,← geometric_aa b k]
        exact min_le_left _ _
  · let u := h-1
    have hu : u ∈ Ioo (0:ℝ) 1 := ⟨by dsimp [u]; linarith [ht.1],by dsimp [u]; linarith [hh.2]⟩
    have htu : t ≤ u := by dsimp [u]; linarith
    have He : ee b u k ≤ aa b k := by
      rw [← Ht]
      exact ee_antitone b hb ht hu htu k
    refine ⟨u,hu,by dsimp [u]; linarith,sub_nonneg.mpr He,?_⟩
    have hz : h ≠ 1 := by intro he; rw [he] at hsmall; linarith [ht.1]
    unfold prefixCoefficient
    rw [if_neg hz]
    change b/(2*h)*min (geometricSum k (1/b)) (geometricSum k ((1-h)/b)) ≤
      b/(2*h)*ee b u k
    apply mul_le_mul_of_nonneg_left _ hc
    calc
      _ ≤ geometricSum k ((1-h)/b) := min_le_right _ _
      _ = geometricSum k (-u/b) := by congr 1; dsimp [u]; ring
      _ = ee b u k := geometric_ee b u k

end Prefix

open PGDMap20261031 Set
open scoped BigOperators
noncomputable section
namespace Prefix
set_option maxRecDepth 2000
set_option maxHeartbeats 1200000

def en (b t E : ℝ) : ℝ := b^2/t^2*E+b*(b-t)/t^2
def tn (b t E T : ℝ) : ℝ := b^2*(E+T)+b*(b+1)-en b t E
def al (b t E T : ℝ) : ℝ := 1+t/b*en b t E+(b-1)/(2*(1+t))*T-(b-t)/(2*b*(1+t))*tn b t E T
def be (b t E T : ℝ) : ℝ := t/b*en b t E+(b-t)/(2*(1+t))*T-t*(b-1)/(2*b*(1+t))*tn b t E T
def atl (b t E T : ℝ) : ℝ := 1+t/b*en b t E+(b-1)/(2*(1+t))*T
def betl (b t E T : ℝ) : ℝ := t/b*en b t E+(b-t)/(2*(1+t))*T
def uc (b t E T : ℝ) : ℝ := tn b t E T/(2*(1+t))
def pc (b t E T : ℝ) : ℝ := (b*(1-t)+t)/(2*t)+(b*(1-t)+2*t)/(2*t*(1+t))*((1+t)*E-(b-1)*T)+((1-t)*(b-1)^3+(2-t^2)*(b-1)^2+(1+2*t-t^2)*(b-1)+t*(1-t))/(2*b*t*(1+t))*T
def psc (b t E T : ℝ) : ℝ := (b*(1-t)+t^2)/(t*(1+t))+(b*(1-t)+t*(1+t))/(t*(1+t)^2)*((1+t)*E-(b-1)*T)+(2*(1-t)*(b-1)^3+2*(2-t)*(b-1)^2+(1+t)*(t^2-t+2)*(b-1)+t*(1-t))/(2*b*t*(1+t)^2)*T
def wc (b t E T : ℝ) : ℝ := b^2*(b*(1-t)+t^2+1)/(2*t^2)*E+b*(-b^2+b*t+b-1)/(2*(1+t))*T+b*(b^2*(1-t)+b*(t^2-t+1)+t^2-t)/(2*t^2)

lemma al_nonneg (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1) (n : ℕ) :
    0 ≤ al b t (ee b t n) (tt b t n) := by
  have he : al b t (ee b t n) (tt b t n) =
      ((1 * (b-1) ^ 4 * t ^ 0 * (1-t) ^ 0 + 5 * (b-1) ^ 3 * t ^ 2 * (1-t) ^ 0 + 8 * (b-1) ^ 3 * t ^ 1 * (1-t) ^ 1 + 4 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 2 + 8 * (b-1) ^ 2 * t ^ 3 * (1-t) ^ 0 + 21 * (b-1) ^ 2 * t ^ 2 * (1-t) ^ 1 + 18 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 2 + 6 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 3 + 4 * (b-1) ^ 1 * t ^ 3 * (1-t) ^ 0 + 15 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 1 + 12 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 2 + 4 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 3 + 4 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 1 + 3 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 2 + 1 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 3) / (2 * (t ^ 4) * (1 + t))) * (ss n ((b/t)^2) - ss n (b^2)) + ((2 * (b-1) ^ 4 * t ^ 2 * (1-t) ^ 1 + 2 * (b-1) ^ 4 * t ^ 1 * (1-t) ^ 2 + 1 * (b-1) ^ 4 * t ^ 0 * (1-t) ^ 3 + 1 * (b-1) ^ 3 * t ^ 4 * (1-t) ^ 0 + 9 * (b-1) ^ 3 * t ^ 3 * (1-t) ^ 1 + 17 * (b-1) ^ 3 * t ^ 2 * (1-t) ^ 2 + 12 * (b-1) ^ 3 * t ^ 1 * (1-t) ^ 3 + 4 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 4 + 3 * (b-1) ^ 2 * t ^ 4 * (1-t) ^ 0 + 14 * (b-1) ^ 2 * t ^ 3 * (1-t) ^ 1 + 27 * (b-1) ^ 2 * t ^ 2 * (1-t) ^ 2 + 18 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 3 + 6 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 4 + 2 * (b-1) ^ 1 * t ^ 4 * (1-t) ^ 0 + 8 * (b-1) ^ 1 * t ^ 3 * (1-t) ^ 1 + 19 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 2 + 12 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 3 + 4 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 4 + 1 * (b-1) ^ 0 * t ^ 3 * (1-t) ^ 1 + 5 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 2 + 3 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 3 + 1 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 4) / (2 * (t ^ 4))) * ss n (b^2) + ((1 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 1 + 1 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 0 + 2 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 1 + 2 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 2 + 2 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 0 + 1 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 1 + 1 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 2) / (2 * (t ^ 2))) := by
    simp only [al,tn,en,tt,ee,aa]
    field_simp [ne_of_gt (show 0 < b by linarith), ht.1.ne', ne_of_gt (show 0 < 1+t by linarith [ht.1])]
    <;> ring
  rw [he]
  have hu : 0 ≤ b-1 := by linarith
  have hv : 0 ≤ 1-t := by linarith [ht.2]
  have ht0 : 0 < t := ht.1
  have hbt : b ≤ b/t := (le_div_iff₀ ht.1).2 (by nlinarith [ht.2])
  have hsq : b^2 ≤ (b/t)^2 := by nlinarith
  have hsum : 0 ≤ ss n ((b/t)^2) - ss n (b^2) := sub_nonneg.mpr (ss_mono n (sq_nonneg b) hsq)
  have hs := ss_nonneg n (b^2) (sq_nonneg b)
  positivity

lemma be_nonneg (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1) (n : ℕ) :
    0 ≤ be b t (ee b t n) (tt b t n) := by
  have he : be b t (ee b t n) (tt b t n) =
      ((1 * (b-1) ^ 4 * t ^ 0 * (1-t) ^ 0 + 5 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 0 + 8 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 0 + 9 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 1 + 4 * (b-1) ^ 1 * t ^ 3 * (1-t) ^ 0 + 17 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 1 + 19 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 2 + 7 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 3 + 4 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 1 + 5 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 2 + 2 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 3) / (2 * (t ^ 3) * (1 + t))) * (ss n ((b/t)^2) - ss n (b^2)) + ((2 * (b-1) ^ 4 * t ^ 2 * (1-t) ^ 1 + 2 * (b-1) ^ 4 * t ^ 1 * (1-t) ^ 2 + 1 * (b-1) ^ 4 * t ^ 0 * (1-t) ^ 3 + 1 * (b-1) ^ 3 * t ^ 3 * (1-t) ^ 0 + 10 * (b-1) ^ 3 * t ^ 2 * (1-t) ^ 1 + 10 * (b-1) ^ 3 * t ^ 1 * (1-t) ^ 2 + 5 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 3 + 3 * (b-1) ^ 2 * t ^ 3 * (1-t) ^ 0 + 17 * (b-1) ^ 2 * t ^ 2 * (1-t) ^ 1 + 17 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 2 + 9 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 3 + 2 * (b-1) ^ 1 * t ^ 3 * (1-t) ^ 0 + 12 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 1 + 12 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 2 + 7 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 3 + 3 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 1 + 3 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 2 + 2 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 3) / (2 * (t ^ 3))) * ss n (b^2) + ((1 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 1 + 1 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 0 + 3 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 1 + 2 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 1) / (2 * t)) := by
    simp only [be,tn,en,tt,ee,aa]
    field_simp [ne_of_gt (show 0 < b by linarith), ht.1.ne', ne_of_gt (show 0 < 1+t by linarith [ht.1])]
    <;> ring
  rw [he]
  have hu : 0 ≤ b-1 := by linarith
  have hv : 0 ≤ 1-t := by linarith [ht.2]
  have ht0 : 0 < t := ht.1
  have hbt : b ≤ b/t := (le_div_iff₀ ht.1).2 (by nlinarith [ht.2])
  have hsq : b^2 ≤ (b/t)^2 := by nlinarith
  have hsum : 0 ≤ ss n ((b/t)^2) - ss n (b^2) := sub_nonneg.mpr (ss_mono n (sq_nonneg b) hsq)
  have hs := ss_nonneg n (b^2) (sq_nonneg b)
  positivity

lemma wc_nonneg (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1) (n : ℕ) :
    0 ≤ wc b t (ee b t n) (tt b t n) := by
  have he : wc b t (ee b t n) (tt b t n) =
      ((1 * (b-1) ^ 5 * t ^ 0 * (1-t) ^ 0 + 6 * (b-1) ^ 4 * t ^ 0 * (1-t) ^ 0 + 13 * (b-1) ^ 3 * t ^ 1 * (1-t) ^ 0 + 14 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 1 + 12 * (b-1) ^ 2 * t ^ 3 * (1-t) ^ 0 + 42 * (b-1) ^ 2 * t ^ 2 * (1-t) ^ 1 + 45 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 2 + 16 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 3 + 4 * (b-1) ^ 1 * t ^ 3 * (1-t) ^ 0 + 21 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 1 + 24 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 2 + 9 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 3 + 4 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 1 + 5 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 2 + 2 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 3) / (2 * (t ^ 4) * (1 + t))) * (ss n ((b/t)^2) - ss n (b^2)) + ((2 * (b-1) ^ 5 * t ^ 2 * (1-t) ^ 1 + 2 * (b-1) ^ 5 * t ^ 1 * (1-t) ^ 2 + 1 * (b-1) ^ 5 * t ^ 0 * (1-t) ^ 3 + 1 * (b-1) ^ 4 * t ^ 4 * (1-t) ^ 0 + 12 * (b-1) ^ 4 * t ^ 3 * (1-t) ^ 1 + 24 * (b-1) ^ 4 * t ^ 2 * (1-t) ^ 2 + 18 * (b-1) ^ 4 * t ^ 1 * (1-t) ^ 3 + 6 * (b-1) ^ 4 * t ^ 0 * (1-t) ^ 4 + 4 * (b-1) ^ 3 * t ^ 4 * (1-t) ^ 0 + 26 * (b-1) ^ 3 * t ^ 3 * (1-t) ^ 1 + 54 * (b-1) ^ 3 * t ^ 2 * (1-t) ^ 2 + 41 * (b-1) ^ 3 * t ^ 1 * (1-t) ^ 3 + 14 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 4 + 5 * (b-1) ^ 2 * t ^ 4 * (1-t) ^ 0 + 25 * (b-1) ^ 2 * t ^ 3 * (1-t) ^ 1 + 58 * (b-1) ^ 2 * t ^ 2 * (1-t) ^ 2 + 45 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 3 + 16 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 4 + 2 * (b-1) ^ 1 * t ^ 4 * (1-t) ^ 0 + 10 * (b-1) ^ 1 * t ^ 3 * (1-t) ^ 1 + 30 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 2 + 24 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 3 + 9 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 4 + 1 * (b-1) ^ 0 * t ^ 3 * (1-t) ^ 1 + 6 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 2 + 5 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 3 + 2 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 4) / (2 * (t ^ 4))) * ss n (b^2) + ((1 * (b-1) ^ 3 * t ^ 0 * (1-t) ^ 1 + 1 * (b-1) ^ 2 * t ^ 2 * (1-t) ^ 0 + 4 * (b-1) ^ 2 * t ^ 1 * (1-t) ^ 1 + 4 * (b-1) ^ 2 * t ^ 0 * (1-t) ^ 2 + 2 * (b-1) ^ 1 * t ^ 2 * (1-t) ^ 0 + 4 * (b-1) ^ 1 * t ^ 1 * (1-t) ^ 1 + 5 * (b-1) ^ 1 * t ^ 0 * (1-t) ^ 2 + 1 * (b-1) ^ 0 * t ^ 2 * (1-t) ^ 0 + 1 * (b-1) ^ 0 * t ^ 1 * (1-t) ^ 1 + 2 * (b-1) ^ 0 * t ^ 0 * (1-t) ^ 2) / (2 * (t ^ 2))) := by
    simp only [wc,tn,en,tt,ee,aa]
    field_simp [ne_of_gt (show 0 < b by linarith), ht.1.ne', ne_of_gt (show 0 < 1+t by linarith [ht.1])]
    <;> ring
  rw [he]
  have hu : 0 ≤ b-1 := by linarith
  have hv : 0 ≤ 1-t := by linarith [ht.2]
  have ht0 : 0 < t := ht.1
  have hbt : b ≤ b/t := (le_div_iff₀ ht.1).2 (by nlinarith [ht.2])
  have hsq : b^2 ≤ (b/t)^2 := by nlinarith
  have hsum : 0 ≤ ss n ((b/t)^2) - ss n (b^2) := sub_nonneg.mpr (ss_mono n (sq_nonneg b) hsq)
  have hs := ss_nonneg n (b^2) (sq_nonneg b)
  positivity

lemma other_weights_nonneg (b t E T : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1)
    (hT : 0 ≤ T) (hE : 0 ≤ en b t E) (hTn : 0 ≤ tn b t E T)
    (hD : 0 ≤ (1+t)*E-(b-1)*T) :
    0 ≤ atl b t E T ∧ 0 ≤ betl b t E T ∧ 0 ≤ uc b t E T ∧
    0 ≤ pc b t E T ∧ 0 ≤ psc b t E T := by
  have ht0 := ht.1
  have hu : 0 ≤ b-1 := by linarith
  have hv : 0 ≤ 1-t := by linarith [ht.2]
  have hbt : 0 ≤ b-t := by linarith [ht.2]
  have h2 : 0 ≤ 2-t^2 := by nlinarith [ht.2]
  have h3 : 0 ≤ 1+2*t-t^2 := by nlinarith [ht.2]
  have h4 : 0 ≤ 2-t := by linarith [ht.2]
  have h5 : 0 ≤ t^2-t+2 := by nlinarith [sq_nonneg t]
  refine ⟨?_,?_,?_,?_,?_⟩
  · unfold atl; positivity
  · unfold betl; positivity
  · unfold uc; positivity
  · unfold pc; positivity
  · unfold psc; positivity
end Prefix

open PGDMap20261031 Set
open scoped RealInnerProductSpace BigOperators
noncomputable section
namespace Prefix
set_option maxRecDepth 4000
set_option maxHeartbeats 0

def Q {d : ℕ} (b t h : ℝ) (a c ap cp u v : Space d) (fa fc : ℝ) : ℝ :=
  let Y := a - b • ap - (c - b • cp)
  fa-fc-inner ℝ v (a-c)-(1/2:ℝ)*‖u-v‖^2 +
    (1/2:ℝ)*‖(1/(1+t)) • Y - (u-v)‖^2 +
    (1+t-h)/(2*h*(1+t)^2)*‖Y‖^2

def R {d : ℕ} (b h : ℝ) (a c prev v : Space d) (ra rc : ℝ) : ℝ :=
  ra-rc-inner ℝ ((1/h) • (prev-c)-v) (a-c)-(b-1)/(2*h)*‖a-c‖^2

def terminal {d : ℕ} (b t h E T : ℝ) (a c d0 u v : Space d)
    (fa fb ra rb rc : ℝ) : ℝ :=
  atl b t E T * Q b t h a c c d0 u v fa fb +
  betl b t E T * Q b t h c a d0 c v u fb fa +
  psc b t E T * R b h a c a u ra rb +
  b*(atl b t E T+betl b t E T)/(1+t) * R b h d0 c a u rc rb +
  t*tn b t E T/(b*(1+t)^2) * R b h a d0 c v ra rc +
  ((b-t)*atl b t E T+(b+1)*betl b t E T)/(1+t) * R b h c d0 c v rb rc

def interior {d : ℕ} (b t h E T : ℝ) (a c d0 e u v w : Space d)
    (fa fb fc ra rb rc rd : ℝ) : ℝ :=
  al b t E T * Q b t h a c c d0 u v fa fb +
  be b t E T * Q b t h c a d0 c v u fb fa +
  uc b t E T * Q b t h a d0 c e u w fa fc +
  t*uc b t E T * Q b t h d0 a e c w u fc fa +
  pc b t E T * R b h a c a u ra rb +
  wc b t E T * R b h d0 c a u rc rb +
  b*uc b t E T * R b h e c a u rd rb +
  t*tn b t E T/(2*b*(1+t)) * R b h a d0 c v ra rc

def remainder {d : ℕ} (b t h T : ℝ) (a c d0 : Space d) : ℝ :=
  b*T/(2*h*(1+t)^2) * ‖(c-d0)+(t/b) • (a-c)‖^2

lemma base_identity {d : ℕ} (b t h : ℝ) (hb : b ≠ 0) (ht : t ≠ 0)
    (hh : h ≠ 0) (hH : 1+t ≠ 0) (a c d0 u v : Space d) (fa fb ra rb rc : ℝ) :
    terminal b t h 0 0 a c d0 u v fa fb ra rb rc +
      remainder b t h (tn b t 0 0) a c d0 =
      fa+ra-fb-rb-b*en b t 0/(2*h)*‖c-d0‖^2 := by
  simp only [terminal,remainder,Q,R,atl,betl,psc,tn,en,
    ← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right]
  simp only [real_inner_comm]
  field_simp [hb,ht,hh,hH]
  <;> ring

lemma increment_identity {d : ℕ} (b t h E T : ℝ) (hb : b ≠ 0) (ht : t ≠ 0)
    (hh : h ≠ 0) (hH : 1+t ≠ 0) (a c d0 e u v w : Space d)
    (fa fb fc ra rb rc rd : ℝ) :
    interior b t h E T a c d0 e u v w fa fb fc ra rb rc rd +
    terminal b t h (en b t E) (tn b t E T) c d0 e v w fb fc rb rc rd -
    terminal b t h E T a c d0 u v fa fb ra rb rc +
    remainder b t h (tn b t (en b t E) (tn b t E T)) c d0 e -
    remainder b t h (tn b t E T) a c d0 =
    fb+rb-fc-rc-b/(2*h)*(en b t (en b t E)*‖d0-e‖^2-en b t E*‖c-d0‖^2) := by
  simp only [interior,terminal,remainder,Q,R,al,be,atl,betl,uc,pc,psc,wc,tn,en,
    ← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    real_inner_smul_left,real_inner_smul_right]
  simp only [real_inner_comm]
  field_simp [hb,ht,hh,hH]
  <;> ring

end Prefix

open PGDMap20261031 Set
open scoped RealInnerProductSpace BigOperators
noncomputable section
namespace Prefix
def IAt {d : ℕ} (b t h : ℝ) (x g : ℕ → Space d) (f r : ℕ → ℝ) (i : ℕ) : ℝ :=
  interior b t h (ee b t i) (tt b t i) (x i) (x (i+1)) (x (i+2)) (x (i+3))
    (g i) (g (i+1)) (g (i+2)) (f i) (f (i+1)) (f (i+2))
    (r i) (r (i+1)) (r (i+2)) (r (i+3))

def TAt {d : ℕ} (b t h : ℝ) (x g : ℕ → Space d) (f r : ℕ → ℝ) (i : ℕ) : ℝ :=
  terminal b t h (ee b t i) (tt b t i) (x i) (x (i+1)) (x (i+2))
    (g i) (g (i+1)) (f i) (f (i+1)) (r i) (r (i+1)) (r (i+2))

def RAt {d : ℕ} (b t h : ℝ) (x : ℕ → Space d) (i : ℕ) : ℝ :=
  remainder b t h (tt b t (i+1)) (x i) (x (i+1)) (x (i+2))

lemma ee_next (b t : ℝ) (ht : t ≠ 0) (i : ℕ) : ee b t (i+1)=en b t (ee b t i) :=
  ee_rec b t ht i
lemma tt_next (b t : ℝ) (ht : t ≠ 0) (i : ℕ) : tt b t (i+1)=tn b t (ee b t i) (tt b t i) := by
  rw [tt_rec,ee_next b t ht]; rfl

lemma telescoping {d : ℕ} (b t h : ℝ) (hb : b ≠ 0) (ht : t ≠ 0)
    (hh : h ≠ 0) (hH : 1+t ≠ 0) (x g : ℕ → Space d) (f r : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, IAt b t h x g f r i) + TAt b t h x g f r n + RAt b t h x n =
    f 0+r 0-f (n+1)-r (n+1)-b*ee b t (n+1)/(2*h)*‖x (n+1)-x (n+2)‖^2 := by
  induction n with
  | zero =>
    have H := base_identity b t h hb ht hh hH (x 0) (x 1) (x 2) (g 0) (g 1)
      (f 0) (f 1) (r 0) (r 1) (r 2)
    simp only [Finset.sum_range_zero,zero_add,TAt,RAt]
    rw [ee_next b t ht 0,tt_next b t ht 0]
    simpa only [ee,tt,aa,ss_zero,mul_zero,sub_self] using H
  | succ n ih =>
    have H := increment_identity b t h (ee b t n) (tt b t n) hb ht hh hH
      (x n) (x (n+1)) (x (n+2)) (x (n+3)) (g n) (g (n+1)) (g (n+2))
      (f n) (f (n+1)) (f (n+2)) (r n) (r (n+1)) (r (n+2)) (r (n+3))
    rw [← ee_next b t ht n,← tt_next b t ht n,← ee_next b t ht (n+1),
      ← tt_next b t ht (n+1)] at H
    change IAt b t h x g f r n + TAt b t h x g f r (n+1) - TAt b t h x g f r n +
      RAt b t h x (n+1) - RAt b t h x n = _ at H
    rw [Finset.sum_range_succ]
    linear_combination ih + H

end Prefix

open PGDMap20261031 Set Filter
open scoped Topology RealInnerProductSpace BigOperators
noncomputable section

private lemma line_deriv {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (hgrad : ∀ x, HasGradientAt f (g x) x) (x v : Space d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (g (x + t • v)) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    convert ((hasDerivAt_id t).smul_const v).const_add x using 1 <;> first | rfl | simp
  convert (hgrad (x + t • v)).hasFDerivAt.comp_hasDerivAt t hl using 1 <;> rfl

private lemma smooth_descent {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (L : ℝ) (hf : SmoothConvex f g L) (x y : Space d) :
    f y ≤ f x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  let v := y - x
  let φ := fun t : ℝ => f (x + t • v) - t * inner ℝ (g x) v -
    (L / 2 * ‖v‖ ^ 2) * t ^ 2
  have hd (t : ℝ) : HasDerivAt φ
      (inner ℝ (g (x + t • v)) v - inner ℝ (g x) v - L * t * ‖v‖ ^ 2) t := by
    convert ((line_deriv f g hf.2.1 x v t).sub
      ((hasDerivAt_id t).mul_const (inner ℝ (g x) v))).sub
        (((hasDerivAt_id t).pow 2).const_mul (L / 2 * ‖v‖ ^ 2)) using 1 <;> try rfl
    simp only [id_eq, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by omega, pow_one, mul_one]
    ring
  have hanti : AntitoneOn φ (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro t _
      exact (hd t).continuousAt.continuousWithinAt
    · intro t _
      exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t).deriv]
      have hinner := real_inner_le_norm (g (x + t • v) - g x) v
      have hLip := hf.2.2 (x + t • v) x
      have hnorm : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hnorm] at hLip
      have hmul := mul_le_mul_of_nonneg_right hLip (norm_nonneg v)
      rw [inner_sub_left] at hinner
      nlinarith only [hinner, hmul]
  have hval := hanti (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, by norm_num⟩)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, le_rfl⟩) (by norm_num)
  have hv : x + v = y := by dsimp [v]; abel
  dsimp [φ] at hval
  simp only [zero_smul, one_smul, add_zero, zero_mul, mul_zero, one_mul,
    zero_pow (by norm_num : 2 ≠ 0), one_pow, mul_one, sub_zero, hv] at hval
  dsimp [v] at hval
  linarith

private lemma proximal_support {d : ℕ} (r : Penalty d) (μ γ : ℝ) (hr : IsPenalty r)
    (hstrong : StrongPenalty r μ) (hγ : 0 < γ) (c y : Space d) (hy : y ∈ r.domain)
    (hmin : ∀ z ∈ r.domain, r.value y + ‖y - c‖ ^ 2 / (2 * γ) ≤
      r.value z + ‖z - c‖ ^ 2 / (2 * γ)) :
    ∀ z ∈ r.domain, r.value y - inner ℝ (y - c) (z - y) / γ +
      μ / 2 * ‖z - y‖ ^ 2 ≤ r.value z := by
  intro z hz
  let A := 2 * γ * (r.value y - r.value z) - 2 * inner ℝ (y - c) (z - y) +
    γ * μ * ‖z - y‖ ^ 2
  let C := (γ * μ + 1) * ‖z - y‖ ^ 2
  have ht_bound (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : A - t * C ≤ 0 := by
    let w := t • z + (1 - t) • y
    have hw : w ∈ r.domain := hr.2.2.1 hz hy ht.1.le (by linarith [ht.2]) (by ring)
    have hopt := hmin w hw
    have hconv := hstrong z hz y hy t ⟨ht.1.le, ht.2.le⟩
    have hnorm : ‖w - c‖ ^ 2 = ‖y - c‖ ^ 2 +
        2 * t * inner ℝ (y - c) (z - y) + t ^ 2 * ‖z - y‖ ^ 2 := by
      have hv : w - c = (y - c) + t • (z - y) := by dsimp [w]; module
      rw [hv, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs]
      ring
    have hopt' := mul_le_mul_of_nonneg_left hopt (show 0 ≤ 2 * γ by positivity)
    have hconv' := mul_le_mul_of_nonneg_left hconv (show 0 ≤ 2 * γ by positivity)
    rw [hnorm] at hopt'
    field_simp [ne_of_gt hγ] at hopt'
    have hprod : t * (A - t * C) ≤ 0 := by
      dsimp [A, C, w]
      nlinarith only [hopt', hconv']
    by_contra hn
    exact (not_lt_of_ge hprod) (mul_pos ht.1 (lt_of_not_ge hn))
  have hlim : Tendsto (fun t : ℝ => A - t * C) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_right nhdsWithin_le_nhds
    simpa only [zero_mul, sub_zero] using (hid.mul_const C).const_sub A
  have hA : A ≤ 0 := by
    apply le_of_tendsto hlim
    have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from Iio_mem_nhds (by norm_num)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hlt1, self_mem_nhdsWithin] with t ht1 ht0
    exact ht_bound t ⟨ht0, ht1⟩
  have htarget : (r.value y - inner ℝ (y - c) (z - y) / γ +
      μ / 2 * ‖z - y‖ ^ 2 - r.value z) * (2 * γ) = A := by
    dsimp [A]
    field_simp [ne_of_gt hγ]
    <;> ring
  have hprod : (r.value y - inner ℝ (y - c) (z - y) / γ +
      μ / 2 * ‖z - y‖ ^ 2 - r.value z) * (2 * γ) ≤ 0 := by rw [htarget]; exact hA
  apply sub_nonpos.mp
  by_contra hn
  exact (not_lt_of_ge hprod) (mul_pos (lt_of_not_ge hn) (by positivity : 0 < 2 * γ))

private lemma convex_support {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (L : ℝ) (hf : SmoothConvex f g L) (x y : Space d) :
    f x + inner ℝ (g x) (y - x) ≤ f y := by
  let φ := fun t : ℝ => f (x + t • (y - x))
  have hc : ConvexOn ℝ univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro a ha b hb u v hu hv huv
    have H := hf.1.2 (mem_univ (x + a • (y - x))) (mem_univ (x + b • (y - x))) hu hv huv
    have Heq : u • (x + a • (y - x)) + v • (x + b • (y - x)) =
        x + (u * a + v * b) • (y - x) := by
      have Hvec : u • x + v • x = x := by rw [← add_smul, huv, one_smul]
      calc
        _ = (u • x + v • x) + (u * a + v * b) • (y - x) := by module
        _ = _ := by rw [Hvec]
    simpa only [φ, smul_eq_mul, Heq] using H
  have hd := line_deriv f g hf.2.1 x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have H := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hd
  have Hxy : x + (y - x) = y := by abel
  simp only [slope_def_field, φ, one_smul, zero_smul, add_zero, Hxy, sub_zero, div_one] at H
  linarith only [H]

private lemma smooth_interpolation {d : ℕ} (f : Space d → ℝ) (g : Space d → Space d)
    (hf : SmoothConvex f g 1) (x y : Space d) :
    0 ≤ f x - f y - inner ℝ (g y) (x - y) - (1 / 2 : ℝ) * ‖g x - g y‖ ^ 2 := by
  let z := x - (g x - g y)
  have Hc := convex_support f g 1 hf y z
  have Hd := smooth_descent f g 1 hf x z
  have Hz : z - x = -(g x - g y) := by dsimp [z]; abel
  have Hzy : z - y = (x - y) - (g x - g y) := by dsimp [z]; abel
  rw [Hz, inner_neg_right, norm_neg] at Hd
  rw [Hzy, inner_sub_right] at Hc
  have Hi : inner ℝ (g x) (g x - g y) - inner ℝ (g y) (g x - g y) = ‖g x - g y‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  nlinarith only [Hc, Hd, Hi]

namespace Prefix
set_option maxHeartbeats 1200000

lemma Q_nonneg {d : ℕ} (b t h : ℝ) (hh : 0 < h) (ht : 0 < t) (hH : h ≤ 1+t)
    (f : Space d → ℝ) (g : Space d → Space d) (hf : SmoothConvex f g 1)
    (a c ap cp : Space d) : 0 ≤ Q b t h a c ap cp (g a) (g c) (f a) (f c) := by
  have H := smooth_interpolation f g hf a c
  unfold Q
  dsimp only
  exact add_nonneg (add_nonneg H (by positivity)) (by positivity)

lemma R_nonneg {d : ℕ} (r : Penalty d) (q h b : ℝ) (hr : IsPenalty r)
    (hq : StrongPenalty r q) (hh : 0 < h) (hb : b=1+h*q)
    (a c prev v : Space d) (ha : a ∈ r.domain) (hc : c ∈ r.domain)
    (hmin : ∀ z ∈ r.domain, r.value c + ‖c-(prev-h • v)‖^2/(2*h) ≤
      r.value z+‖z-(prev-h • v)‖^2/(2*h)) :
    0 ≤ R b h a c prev v (r.value a) (r.value c) := by
  have H := proximal_support r q h hr hq hh (prev-h • v) c hc hmin a ha
  have He : R b h a c prev v (r.value a) (r.value c) = r.value a -
      (r.value c-inner ℝ (c-(prev-h • v)) (a-c)/h+q/2*‖a-c‖^2) := by
    unfold R
    rw [hb]
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left]
    field_simp [hh.ne']
    <;> ring
  rw [He]
  exact sub_nonneg.mpr H

lemma weights_at_nonneg (b t : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1)
    (k i : ℕ) (hk : 1 ≤ k) (hTk : 0 ≤ tt b t k) (hi : i < k) :
    0 ≤ tn b t (ee b t i) (tt b t i) ∧
    0 ≤ atl b t (ee b t i) (tt b t i) ∧ 0 ≤ betl b t (ee b t i) (tt b t i) ∧
    0 ≤ uc b t (ee b t i) (tt b t i) ∧ 0 ≤ pc b t (ee b t i) (tt b t i) ∧
    0 ≤ psc b t (ee b t i) (tt b t i) := by
  have hT := tt_nonneg_prefix b t hb ht k hk hTk i (by omega)
  have hT1 := tt_nonneg_prefix b t hb ht k hk hTk (i+1) (by omega)
  have hE1 := ee_nonneg b t hb ht (i+1)
  rw [tt_next b t ht.1.ne'] at hT1
  rw [ee_next b t ht.1.ne'] at hE1
  exact ⟨hT1,other_weights_nonneg b t _ _ hb ht hT hE1 hT1 (delta_nonneg b t hb ht i)⟩

lemma terminal_nonneg {d : ℕ} (b t h : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1)
    (k i : ℕ) (hk : 1 ≤ k) (hTk : 0 ≤ tt b t k) (hi : i < k)
    (x g : ℕ → Space d) (f r : ℕ → ℝ)
    (hQ : ∀ a c, 0 ≤ Q b t h (x a) (x c) (x (a+1)) (x (c+1)) (g a) (g c) (f a) (f c))
    (hR : ∀ a ≤ k+1, ∀ j < k+1,
      0 ≤ R b h (x a) (x (j+1)) (x j) (g j) (r a) (r (j+1))) :
    0 ≤ TAt b t h x g f r i := by
  obtain ⟨hTn,ha,hbe,hu,hp,hps⟩ := weights_at_nonneg b t hb ht k i hk hTk hi
  have hQ1 := hQ i (i+1)
  have hQ2 := hQ (i+1) i
  have hR1 := hR i (by omega) i (by omega)
  have hR2 := hR (i+2) (by omega) i (by omega)
  have hR3 := hR i (by omega) (i+1) (by omega)
  have hR4 := hR (i+1) (by omega) (i+1) (by omega)
  have ht0 := ht.1
  have hbt : 0 ≤ b-t := by linarith [ht.2]
  unfold TAt terminal
  positivity

lemma interior_nonneg {d : ℕ} (b t h : ℝ) (hb : 1 ≤ b) (ht : t ∈ Ioo (0:ℝ) 1)
    (k i : ℕ) (hk : 1 ≤ k) (hTk : 0 ≤ tt b t k) (hi : i+1 < k)
    (x g : ℕ → Space d) (f r : ℕ → ℝ)
    (hQ : ∀ a c, 0 ≤ Q b t h (x a) (x c) (x (a+1)) (x (c+1)) (g a) (g c) (f a) (f c))
    (hR : ∀ a ≤ k+1, ∀ j < k+1,
      0 ≤ R b h (x a) (x (j+1)) (x j) (g j) (r a) (r (j+1))) :
    0 ≤ IAt b t h x g f r i := by
  obtain ⟨hTn,ha,hbe,hu,hp,hps⟩ := weights_at_nonneg b t hb ht k i hk hTk (by omega)
  have hal := al_nonneg b t hb ht i
  have hbel := be_nonneg b t hb ht i
  have hw := wc_nonneg b t hb ht i
  have hQ1 := hQ i (i+1)
  have hQ2 := hQ (i+1) i
  have hQ3 := hQ i (i+2)
  have hQ4 := hQ (i+2) i
  have hR1 := hR i (by omega) i (by omega)
  have hR2 := hR (i+2) (by omega) i (by omega)
  have hR3 := hR (i+3) (by omega) i (by omega)
  have hR4 := hR i (by omega) (i+1) (by omega)
  have ht0 := ht.1
  unfold IAt interior
  positivity

lemma prefix_with_parameters {d : ℕ} (r : Penalty d) (q h t : ℝ) (k : ℕ)
    (f : Space d → ℝ) (g : Space d → Space d) (x : ℕ → Space d)
    (hr : IsPenalty r) (hq : 0 ≤ q) (hstrong : StrongPenalty r q) (hh : validStep h)
    (ht : t ∈ Ioo (0:ℝ) 1) (hH : h ≤ 1+t) (hk : 1 ≤ k)
    (hf : SmoothConvex f g 1) (hx : IsPGDTrajectory r g h (k+1) x)
    (hTk : 0 ≤ tt (base h q) t k) :
    base h q/(2*h)*ee (base h q) t k*‖x k-x (k+1)‖^2 ≤ decrease r f x k := by
  let b := base h q
  have hb : 1 ≤ b := by dsimp [b,base]; nlinarith [hh.1]
  have hb0 : 0 < b := by linarith
  have ht0 := ht.1
  have hH0 : 0 < 1+t := by linarith
  have hQ : ∀ a c, 0 ≤ Q b t h (x a) (x c) (x (a+1)) (x (c+1))
      (g (x a)) (g (x c)) (f (x a)) (f (x c)) := by
    intro a c
    exact Q_nonneg b t h hh.1 ht.1 hH f g hf _ _ _ _
  have hR : ∀ a ≤ k+1, ∀ j < k+1, 0 ≤ R b h (x a) (x (j+1)) (x j)
      (g (x j)) (r.value (x a)) (r.value (x (j+1))) := by
    intro a ha j hj
    exact R_nonneg r q h b hr hstrong hh.1 rfl _ _ _ _
      (hx.1 a ha) (hx.1 (j+1) (by omega)) (hx.2 j hj)
  have Hsum : 0 ≤ ∑ i ∈ Finset.range (k-1), IAt b t h x (g ∘ x) (f ∘ x) (r.value ∘ x) i := by
    apply Finset.sum_nonneg
    intro i hi
    exact interior_nonneg b t h hb ht k i hk hTk (by have := Finset.mem_range.mp hi; omega)
      x (g ∘ x) (f ∘ x) (r.value ∘ x) hQ hR
  have Hterm := terminal_nonneg b t h hb ht k (k-1) hk hTk (by omega)
    x (g ∘ x) (f ∘ x) (r.value ∘ x) hQ hR
  have Hrem : 0 ≤ RAt b t h x (k-1) := by
    unfold RAt remainder
    rw [Nat.sub_add_cancel hk]
    have hh0 := hh.1
    positivity
  have Htel := telescoping b t h hb0.ne' ht0.ne' hh.1.ne' hH0.ne'
    x (g ∘ x) (f ∘ x) (r.value ∘ x) (k-1)
  have hindex : k-1+1=k := Nat.sub_add_cancel hk
  have hindex2 : k-1+2=k+1 := by omega
  rw [hindex,hindex2] at Htel
  change b/(2*h)*ee b t k*‖x k-x (k+1)‖^2 ≤ _
  unfold decrease totalValue
  dsimp only [Function.comp_apply] at Htel
  have Hnonneg := add_nonneg (add_nonneg Hsum Hterm) Hrem
  rw [Htel] at Hnonneg
  calc
    _ = b*ee b t k/(2*h)*‖x k-x (k+1)‖^2 := by ring
    _ ≤ f (x 0)+r.value (x 0)-f (x k)-r.value (x k) := by linarith only [Hnonneg]
    _ = _ := by ring

end Prefix

theorem solution : PrefixCertificateClaim := by
  intro d r q h k f g x hr hq hstrong hh hk hf hx
  obtain ⟨t,ht,hH,hTk,hco⟩ := Prefix.choose_parameters h q hh hq k hk
  have H := Prefix.prefix_with_parameters r q h t k f g x hr hq hstrong hh ht hH hk hf hx hTk
  exact le_trans (mul_le_mul_of_nonneg_right hco (sq_nonneg ‖x k-x (k+1)‖)) H

#print axioms solution
