-- Prove2me | solution 1 for YeIPA.MCP.central_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:33:46.878875+00:00
-- url     : https://prove2.me/submissions/8ddae26f-1d92-4487-bc1f-4dc6dc6f0a78

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel
import Theorems.Thm_YeIPA_MCP_new_iterate_residual_gap
import Theorems.Thm_YeIPA_MCP_direction_inner_product

open Matrix

namespace YeIPA.MCP.CS

lemma norm2_le_l1 {N : ℕ} (w : Fin N → ℝ) : norm2 w ≤ ∑ i, |w i| := by
  unfold norm2
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  calc ∑ i, w i ^ 2 = ∑ i, |w i| ^ 2 := by simp [sq_abs]
    _ ≤ (∑ i, |w i|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

lemma abs_le_of_sq {t c : ℝ} (hc : 0 ≤ c) (h : t ^ 2 ≤ c ^ 2) : |t| ≤ c :=
  (sq_le_sq.mp h).trans_eq (abs_of_nonneg hc)

lemma quad_nonneg {N : ℕ} (g : (Fin N → ℝ) → (Fin N → ℝ)) (v : ℝ → ℝ)
    (hψ : ScaledLipschitz g v) (x : Fin N → ℝ) (hx : x ∈ posOrthant N) (d : Fin N → ℝ) :
    0 ≤ d ⬝ᵥ fderiv ℝ g x d := by
  set M := ∑ i, |d i / x i| with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set t : ℝ := 1 / (2 * (M + 1)) with htdef
  have ht : 0 < t := by positivity
  have hb : ∀ i, |(t • d) i / x i| ≤ 1 / 2 := by
    intro i
    have hi : |d i / x i| ≤ M :=
      Finset.single_le_sum (f := fun i => |d i / x i|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ i)
    rw [Pi.smul_apply, smul_eq_mul, mul_div_assoc, abs_mul, abs_of_pos ht, htdef,
      div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have h := hψ.2.2 x hx (t • d) (1 / 2) (by norm_num) (by norm_num) hb
  have h0 : 0 ≤ ∑ i, |x i * (g (x + t • d) i - g x i - fderiv ℝ g x (t • d) i)| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hv := hψ.1 (1 / 2) (by norm_num) (by norm_num)
  simp only [map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h h0
  by_contra hneg
  push Not at hneg
  have : v (1 / 2) * (t * (t * (d ⬝ᵥ fderiv ℝ g x d))) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (mul_neg_of_pos_of_neg ht (mul_neg_of_pos_of_neg ht hneg))
  linarith

lemma amgm_abs {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * b = p ^ 2) : |p| ≤ (a + b) / 2 := by
  apply abs_le_of_sq (by positivity)
  nlinarith [sq_nonneg (a - b)]

lemma ratio_aux {t m R B : ℝ} (hm : 0 < m) (h1 : t * m ≤ R) (h2 : R * m ≤ B)
    (h3 : B ≤ 1 / 2 * m * m) : t ≤ 1 / 2 := by
  have h4 : t * m * m ≤ 1 / 2 * m * m := le_trans (le_trans (mul_le_mul_of_nonneg_right h1 hm.le) h2) h3
  exact le_of_mul_le_mul_right (le_of_mul_le_mul_right h4 hm) hm

lemma dx_aux {d x c : ℝ} (hx : 0 < x) (hc : c < 1) (h : |d / x| ≤ c) : |d| ≤ x ∧ -d < x := by
  rw [abs_div, abs_of_pos hx, div_le_iff₀ hx] at h
  have : c * x < x := by nlinarith
  have := neg_abs_le d
  constructor <;> linarith

lemma beta_aux {v0 β : ℝ} (hv0 : 1 < v0) (hβv : β * (3 + 4 * v0) = 1) : 0 < β ∧ β < 1 / 7 := by
  have hpos : 0 < β := by
    by_contra h; push Not at h; nlinarith
  refine ⟨hpos, ?_⟩
  nlinarith

lemma final_aux {R A Q v0 β μ γ : ℝ} (hRA : R = A + 2 * Q) (hQA : Q ≤ A / 2) (hQ : 0 ≤ Q)
    (hv0 : 1 < v0) (hRm : R * ((1 - β) * μ) ≤ 2 * β ^ 2 * μ ^ 2) (hβv : β * (3 + 4 * v0) = 1)
    (hγβ : 1 - β ≤ γ) (hμ : 0 < μ) (hβ : 0 < β) (hβ7 : β < 1 / 7) :
    A / 2 + 2 * (v0 * Q) ≤ β * (γ * μ) := by
  have hm : 0 < (1 - β) * μ := by apply mul_pos _ hμ; linarith
  have h2 : A / 2 + 2 * (v0 * Q) ≤ R * (1 + v0) / 2 := by
    have : v0 * Q ≤ v0 * (A / 2) := mul_le_mul_of_nonneg_left hQA (by linarith)
    rw [hRA]; nlinarith
  have hkey : β * (1 + v0) ≤ (1 - β) ^ 2 := by nlinarith
  have h5 : (R * ((1 - β) * μ)) * (1 + v0) / 2 ≤ (2 * β ^ 2 * μ ^ 2) * (1 + v0) / 2 := by
    have : 0 < 1 + v0 := by linarith
    have := mul_le_mul_of_nonneg_right hRm this.le
    linarith
  have h6 : (2 * β ^ 2 * μ ^ 2) * (1 + v0) / 2 ≤ β * ((1 - β) * μ) * ((1 - β) * μ) := by
    have : β * ((1 - β) * μ) * ((1 - β) * μ) - (2 * β ^ 2 * μ ^ 2) * (1 + v0) / 2
        = β * μ ^ 2 * ((1 - β) ^ 2 - β * (1 + v0)) := by ring
    nlinarith [mul_nonneg (mul_nonneg hβ.le (sq_nonneg μ)) (sub_nonneg.mpr hkey)]
  have h3 : R * (1 + v0) / 2 * ((1 - β) * μ) ≤ β * ((1 - β) * μ) * ((1 - β) * μ) := by
    have : R * (1 + v0) / 2 * ((1 - β) * μ) = (R * ((1 - β) * μ)) * (1 + v0) / 2 := by ring
    rw [this]; exact le_trans h5 h6
  have h4 : R * (1 + v0) / 2 ≤ β * ((1 - β) * μ) := le_of_mul_le_mul_right h3 hm
  have : β * ((1 - β) * μ) ≤ β * (γ * μ) := by
    apply mul_le_mul_of_nonneg_left _ hβ.le
    exact mul_le_mul_of_nonneg_right hγβ hμ.le
  linarith

end YeIPA.MCP.CS

open YeIPA.MCP

theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (hf_diff : DifferentiableOn ℝ f (posOrthant n))
    (v : ℝ → ℝ) (hψ : ScaledLipschitz (psi f) v)
    (β η γ : ℝ) (hβ : β = 1 / (3 + 4 * v (Real.sqrt 2 / 2)))
    (hη : η = β / Real.sqrt ((n : ℝ) + 1)) (hγ : γ = 1 - η)
    (x s dx ds : Fin (n + 1) → ℝ) (hx : x ∈ posOrthant (n + 1)) (hs : s ∈ posOrthant (n + 1))
    (hnbhd : norm2 (fun i => x i * s i - mu x s) ≤ β * mu x s)
    (hdir : IsDirection f η γ x s dx ds) :
    β ≤ 1 / 3 ∧
    newX x dx 1 ∈ posOrthant (n + 1) ∧
    newS f x s dx ds 1 = psi f (newX x dx 1) + (1 - η) • residual f x s ∧
    newS f x s dx ds 1 ∈ posOrthant (n + 1) ∧
    norm2 (fun i => newX x dx 1 i * newS f x s dx ds 1 i -
        mu (newX x dx 1) (newS f x s dx ds 1)) ≤
      β * mu (newX x dx 1) (newS f x s dx ds 1) := by
  -- constants
  have hs2pos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hs2lt : Real.sqrt 2 / 2 < 1 := by
    have : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hs2sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  set v0 := v (Real.sqrt 2 / 2) with hv0def
  have hv0 : 1 < v0 := hψ.1 _ hs2pos hs2lt
  have hβv : β * (3 + 4 * v0) = 1 := by rw [hβ]; field_simp
  obtain ⟨hβpos, hβ7⟩ := YeIPA.MCP.CS.beta_aux hv0 hβv
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hsq1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := Real.one_le_sqrt.mpr hn1
  have hsqpos : 0 < Real.sqrt ((n : ℝ) + 1) := by linarith
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηβ : η ≤ β := by rw [hη]; exact div_le_self hβpos.le hsq1
  have hη1 : η < 1 := by linarith
  have hγpos : 0 < γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  have hηsq : η ^ 2 * ((n : ℝ) + 1) = β ^ 2 := by
    rw [hη, div_pow, Real.sq_sqrt (by linarith)]; field_simp
  have hxp : ∀ i, 0 < x i := hx
  have hsp : ∀ i, 0 < s i := hs
  -- μ
  set μ := mu x s with hμdef
  have hsum : ∑ i, x i * s i = ((n : ℝ) + 1) * μ := by
    rw [hμdef, mu]; simp only [dotProduct]; field_simp
  have hμpos : 0 < μ := by
    rw [hμdef, mu]; apply div_pos _ (by linarith)
    exact Finset.sum_pos (fun i _ => mul_pos (hxp i) (hsp i)) Finset.univ_nonempty
  -- Q
  set Q := dx ⬝ᵥ fderiv ℝ (psi f) x dx with hQdef
  have hdd : dx ⬝ᵥ ds = Q := by
    have := direction_inner_product f hf_cont hf_mono hf_diff η γ hηpos hη1 hγpos hγ1 x s dx ds
      hx hs hdir
    rw [this, show 1 - η - γ = 0 by rw [hγ]; ring]; ring
  have hQ : 0 ≤ Q := YeIPA.MCP.CS.quad_nonneg (psi f) v hψ x hx dx
  have hddsum : ∑ i, dx i * ds i = Q := by rw [← hdd]; rfl
  -- neighbourhood
  have hS : ∑ i, (x i * s i - μ) ^ 2 ≤ β ^ 2 * μ ^ 2 := by
    have h1 := hnbhd
    unfold norm2 at h1
    have h2 := (Real.sqrt_le_iff.mp h1).2
    exact h2.trans_eq (by ring)
  have hwlow : ∀ i, (1 - β) * μ ≤ x i * s i := by
    intro i
    have : (x i * s i - μ) ^ 2 ≤ β ^ 2 * μ ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun i => (x i * s i - μ) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)) hS
    have h2 := YeIPA.MCP.CS.abs_le_of_sq (t := x i * s i - μ) (mul_pos hβpos hμpos).le
      (by rw [mul_pow]; exact this)
    have h3 := neg_abs_le (x i * s i - μ)
    linarith
  have hcomb : ∀ i, x i * ds i + s i * dx i = γ * μ - x i * s i := hdir.2
  have hm : 0 < (1 - β) * μ := by apply mul_pos _ hμpos; linarith
  -- sum of squares of γμ - w
  have hT : ∑ i, (γ * μ - x i * s i) ^ 2 ≤ 2 * β ^ 2 * μ ^ 2 := by
    have key : ∀ i, (γ * μ - x i * s i) ^ 2 =
        (x i * s i - μ) ^ 2 + (2 * η * μ) * (x i * s i) + (η ^ 2 * μ ^ 2 - 2 * η * μ ^ 2) := by
      intro i; rw [hγ]; ring
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    push_cast
    have : ((n : ℝ) + 1) * (η ^ 2 * μ ^ 2 - 2 * η * μ ^ 2) + 2 * η * μ * (((n : ℝ) + 1) * μ)
        = β ^ 2 * μ ^ 2 := by rw [← hηsq]; ring
    linarith
  -- a, b, R
  set R := ∑ i, (γ * μ - x i * s i) ^ 2 / (x i * s i) with hRdef
  have hRm : R * ((1 - β) * μ) ≤ 2 * β ^ 2 * μ ^ 2 := by
    refine le_trans ?_ hT
    rw [hRdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hw := mul_pos (hxp i) (hsp i)
    rw [div_mul_eq_mul_div, div_le_iff₀ hw]
    exact mul_le_mul_of_nonneg_left (hwlow i) (sq_nonneg _)
  have hab : ∀ i, s i * dx i ^ 2 / x i + x i * ds i ^ 2 / s i + 2 * (dx i * ds i) =
      (γ * μ - x i * s i) ^ 2 / (x i * s i) := by
    intro i
    rw [← hcomb i]
    have := hxp i; have := hsp i
    field_simp; ring
  have habs_dd : ∀ i, |dx i * ds i| ≤ (s i * dx i ^ 2 / x i + x i * ds i ^ 2 / s i) / 2 := by
    intro i
    have hxi := hxp i; have hsi := hsp i
    have ha : 0 ≤ s i * dx i ^ 2 / x i := by positivity
    have hb : 0 ≤ x i * ds i ^ 2 / s i := by positivity
    have hprod : (s i * dx i ^ 2 / x i) * (x i * ds i ^ 2 / s i) = (dx i * ds i) ^ 2 := by
      field_simp
    exact YeIPA.MCP.CS.amgm_abs ha hb hprod
  set A := ∑ i, (s i * dx i ^ 2 / x i + x i * ds i ^ 2 / s i) with hAdef
  have hRA : R = A + 2 * Q := by
    rw [hRdef, hAdef, ← hddsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (hab i).symm)
  have hddabs : ∑ i, |dx i * ds i| ≤ A / 2 := by
    rw [hAdef, Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => habs_dd i)
  have hQA : Q ≤ A / 2 := by
    rw [← hddsum]
    exact le_trans (Finset.sum_le_sum (fun i _ => le_abs_self _)) hddabs
  have hA0 : 0 ≤ A := by linarith
  -- ratio bound
  have hratio : ∀ i, |dx i / x i| ≤ Real.sqrt 2 / 2 := by
    intro i
    have hxi := hxp i; have hsi := hsp i
    apply YeIPA.MCP.CS.abs_le_of_sq hs2pos.le
    rw [hs2sq]
    have hai : s i * dx i ^ 2 / x i ≤ A := by
      have h1 : s i * dx i ^ 2 / x i ≤ s i * dx i ^ 2 / x i + x i * ds i ^ 2 / s i := by
        have : 0 ≤ x i * ds i ^ 2 / s i := by positivity
        linarith
      refine le_trans h1 ?_
      exact Finset.single_le_sum (f := fun i => s i * dx i ^ 2 / x i + x i * ds i ^ 2 / s i)
        (fun j _ => by have := hxp j; have := hsp j; positivity) (Finset.mem_univ i)
    have heq : (dx i / x i) ^ 2 * (x i * s i) = s i * dx i ^ 2 / x i := by field_simp
    have h3 : 2 * β ^ 2 * μ ^ 2 ≤ (1 / 2) * ((1 - β) * μ) * ((1 - β) * μ) := by
      have h4b : 4 * β ^ 2 ≤ (1 - β) ^ 2 := by
        have := mul_pos (by linarith : (0:ℝ) < 1 - 3 * β) (by linarith : (0:ℝ) < 1 + β)
        linarith
      have hμ2 := sq_nonneg μ
      have he : (1 / 2) * ((1 - β) * μ) * ((1 - β) * μ) - 2 * β ^ 2 * μ ^ 2
          = ((1 - β) ^ 2 - 4 * β ^ 2) * μ ^ 2 / 2 := by ring
      linarith [mul_nonneg (sub_nonneg.mpr h4b) hμ2]
    have ht0 : 0 ≤ (dx i / x i) ^ 2 := sq_nonneg _
    have h1 : (dx i / x i) ^ 2 * ((1 - β) * μ) ≤ R := by
      have := mul_le_mul_of_nonneg_left (hwlow i) ht0
      linarith
    exact YeIPA.MCP.CS.ratio_aux hm h1 hRm h3
  have hdxle : ∀ i, |dx i| ≤ x i := fun i => (YeIPA.MCP.CS.dx_aux (hxp i) hs2lt (hratio i)).1
  have hdxlt : ∀ i, -dx i < x i := fun i => (YeIPA.MCP.CS.dx_aux (hxp i) hs2lt (hratio i)).2
  -- new X
  have hnX : ∀ i, newX x dx 1 i = x i + dx i := by intro i; simp [newX]
  have hXpos : newX x dx 1 ∈ posOrthant (n + 1) := by
    intro i; rw [hnX]; linarith [hdxlt i]
  -- Lemma 8.28
  obtain ⟨hr, hgap⟩ := new_iterate_residual_gap f hf_cont hf_mono hf_diff η γ hηpos hη1 hγpos
    hγ1 x s dx ds hx hs hdir 1 one_pos hXpos
  have hpart3 : newS f x s dx ds 1 = psi f (newX x dx 1) + (1 - η) • residual f x s := by
    rw [sub_eq_iff_eq_add'] at hr; rw [hr, one_mul]
  have hμp : mu (newX x dx 1) (newS f x s dx ds 1) = γ * μ := by
    rw [mu, hgap, show 1 - η - γ = 0 by rw [hγ]; ring, hμdef, mu]
    field_simp; ring
  -- scaled Lipschitz
  set err : Fin (n + 1) → ℝ := fun i => psi f (x + dx) i - psi f x i - fderiv ℝ (psi f) x dx i
    with herrdef
  have hL : ∑ i, |x i * err i| ≤ v0 * Q := hψ.2.2 x hx dx _ hs2pos hs2lt hratio
  have hnS : ∀ i, newS f x s dx ds 1 i = s i + ds i + err i := by
    intro i
    have : newX x dx 1 = x + dx := by ext j; exact hnX j
    simp only [newS, this, herrdef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      one_mul]
    ring
  have hcoord : ∀ i, newX x dx 1 i * newS f x s dx ds 1 i -
      mu (newX x dx 1) (newS f x s dx ds 1) = dx i * ds i + (x i + dx i) * err i := by
    intro i
    rw [hnX, hnS, hμp]
    linear_combination hcomb i
  have hL1 : ∑ i, |newX x dx 1 i * newS f x s dx ds 1 i -
      mu (newX x dx 1) (newS f x s dx ds 1)| ≤ β * (γ * μ) := by
    simp only [hcoord]
    have h1 : ∑ i, |dx i * ds i + (x i + dx i) * err i| ≤
        ∑ i, |dx i * ds i| + 2 * ∑ i, |x i * err i| := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      refine le_trans (abs_add_le _ _) ?_
      have hxe : |(x i + dx i) * err i| ≤ 2 * |x i * err i| := by
        rw [abs_mul, abs_mul, abs_of_pos (hxp i)]
        have : |x i + dx i| ≤ 2 * x i := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_of_pos (hxp i)]; linarith [hdxle i]
        have := mul_le_mul_of_nonneg_right this (abs_nonneg (err i))
        linarith
      linarith
    have hγβ : 1 - β ≤ γ := by rw [hγ]; linarith
    have := YeIPA.MCP.CS.final_aux hRA hQA hQ hv0 hRm hβv hγβ hμpos hβpos hβ7
    have h2 : 2 * ∑ i, |x i * err i| ≤ 2 * (v0 * Q) := by linarith
    linarith
  refine ⟨by linarith, hXpos, hpart3, ?_, ?_⟩
  · intro i
    have hi : |newX x dx 1 i * newS f x s dx ds 1 i - mu (newX x dx 1) (newS f x s dx ds 1)|
        ≤ β * (γ * μ) :=
      le_trans (Finset.single_le_sum (f := fun i => |newX x dx 1 i * newS f x s dx ds 1 i -
        mu (newX x dx 1) (newS f x s dx ds 1)|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)) hL1
    rw [hμp] at hi
    have hlow := neg_abs_le (newX x dx 1 i * newS f x s dx ds 1 i - γ * μ)
    have hprod : 0 < newX x dx 1 i * newS f x s dx ds 1 i := by
      have : 0 < γ * μ := mul_pos hγpos hμpos
      have : β * (γ * μ) < γ * μ := mul_lt_of_lt_one_left this (by linarith)
      linarith
    exact pos_of_mul_pos_right hprod (hXpos i).le
  · rw [hμp]
    rw [hμp] at hL1
    exact le_trans (YeIPA.MCP.CS.norm2_le_l1 _) hL1
