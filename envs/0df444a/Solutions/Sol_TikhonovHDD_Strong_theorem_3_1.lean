-- Prove2me | solution 1 for TikhonovHDD.Strong.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:39:07.896276+00:00
-- url     : https://prove2.me/submissions/d1dfbc5b-cf2b-453b-9a02-b4596e5e2042

import Mathlib
import Definitions.Def_TikhonovHDD_Strong_Setting
import Theorems.Thm_TikhonovHDD_Strong_lemma_A_1

open Set Filter Topology
open TikhonovHDD.Strong

namespace TikhCaseIAux
theorem young2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 ≤ ε) :
    -(ε * inner ℝ u v) ≤ inner ℝ u u / a + a / 4 * ε ^ 2 * inner ℝ v v := by
  have h : -inner ℝ u v ≤ ‖u‖ * ‖v‖ := (neg_le_abs _).trans (abs_real_inner_le_norm u v)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h1 : ε * (-inner ℝ u v) ≤ ε * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left h hε
  have hid : ‖u‖ ^ 2 / a + a / 4 * ε ^ 2 * ‖v‖ ^ 2 - ε * (‖u‖ * ‖v‖)
      = a * (‖u‖ / a - ε * ‖v‖ / 2) ^ 2 := by
    field_simp; ring
  have := mul_nonneg ha.le (sq_nonneg (‖u‖ / a - ε * ‖v‖ / 2))
  linarith


end TikhCaseIAux

namespace TikhKey2Aux
theorem grad_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (hconv : ConvexOn ℝ univ g) (w u : H) (hd : DifferentiableAt ℝ g w) :
    fderiv ℝ g w (u - w) ≤ g u - g w := by
  set h : ℝ → ℝ := fun s => g (w + s • (u - w)) with hh
  have hline : HasDerivAt (fun s : ℝ => w + s • (u - w)) (u - w) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (u - w)).const_add w
  have hder : HasDerivAt h (fderiv ℝ g w (u - w)) 0 := by
    have hd' : HasFDerivAt g (fderiv ℝ g w) (w + (0:ℝ) • (u - w)) := by
      simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0:ℝ) hline
  have hlim := hder.tendsto_slope_zero_right
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hc := hconv.2 (mem_univ w) (mem_univ u) (show (0:ℝ) ≤ 1 - t by linarith) ht0.le
    (show (1 - t) + t = 1 by ring)
  have heq : (1 - t) • w + t • u = w + t • (u - w) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [heq] at hc
  simp only [smul_eq_mul] at hc
  have h0 : h 0 = g w := by simp [hh]
  have ht' : h (0 + t) = g (w + t • (u - w)) := by simp [hh]
  rw [ht', h0, smul_eq_mul]
  rw [inv_mul_le_iff₀ ht0]
  linarith


end TikhKey2Aux

namespace Tikh31Aux


theorem alg_a (α β a t ε ε' e xx vv gg xv xg vg sv sg sx ss b κ : ℝ)
    (hb : b = (α + 1) / 2) (hκ : κ = β * (b + 2 - α))
    (hα : 3 ≤ α) (hβ : 0 ≤ β) (ha : 1 < a) (ht : 0 < t) (ht2 : 2 * β ≤ t)
    (hta : β ≤ (1 - 1 / a) * t)
    (hε : 0 ≤ ε) (hε' : ε' ≤ -(a * β / 2) * ε ^ 2) (he : 0 ≤ e)
    (hxx : 0 ≤ xx) (hvv : 0 ≤ vv) (hgg : 0 ≤ gg) (hn : 0 ≤ xx + 2 * sx + ss)
    (hgrad : e ≤ xg)
    (hy2 : -(ε * (xg + sg)) ≤ gg / a + a / 4 * ε ^ 2 * (xx + 2 * sx + ss)) :
    (2 * t - κ) * e + (t ^ 2 - κ * t) * vg
      + ((2 * t * ε + t ^ 2 * ε') / 2 * (xx + 2 * sx + ss) + t ^ 2 * ε / 2 * (2 * (xv + sv)))
      + ((b + 1 - α) * b * xv + (b + 1 - α) * t * vv + (b + 1 - α) * t * β * vg
          + (β - t) * b * xg + (β - t) * t * vg + (β - t) * t * β * gg
          - t * ε * b * xx - t * ε * t * xv - t * ε * t * β * xg
          - t * ε * b * sx - t * ε * t * sv - t * ε * t * β * sg)
      + b * (α - 1 - b) / 2 * (2 * xv)
      ≤ β * e + b / 2 * t * ε * ss := by
  subst hb hκ
  have N1 : ((2 - (α + 1) / 2) * t + β * (α - 2) - β) * e ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ he
    have : (2 - (α + 1) / 2) * t + β * (α - 2) - β = (α - 3) * (β - t / 2) := by ring
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have N2 : (t ^ 2 * (ε' / 2 + a * β * ε ^ 2 / 4) + (2 - (α + 1) / 2) * t * ε / 2)
      * (xx + 2 * sx + ss) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hn
    have h1 : t ^ 2 * (ε' / 2 + a * β * ε ^ 2 / 4) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by nlinarith)
    have h2 : (2 - (α + 1) / 2) * t * ε / 2 ≤ 0 := by
      have : 0 ≤ t * ε := by positivity
      nlinarith
    linarith
  have N3 : -((α + 1) / 2 * t * ε / 2 * xx) ≤ 0 := by
    have : 0 ≤ (α + 1) / 2 * t * ε / 2 * xx := by
      have : 0 ≤ (α + 1) / 2 := by linarith
      positivity
    linarith
  have N4 : ((α + 1) / 2 + 1 - α) * t * vv ≤ 0 := by
    have : ((α + 1) / 2 + 1 - α) * t * vv = -((α - 3) / 2 * (t * vv)) := by ring
    rw [this]
    have : 0 ≤ (α - 3) / 2 * (t * vv) := mul_nonneg (by linarith) (by positivity)
    linarith
  have N5 : (β ^ 2 * t - β * (1 - 1 / a) * t ^ 2) * gg ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hgg
    have : β ^ 2 * t - β * (1 - 1 / a) * t ^ 2 = β * t * (β - (1 - 1 / a) * t) := by ring
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have S1 : (α + 1) / 2 * (t - β) * e ≤ (α + 1) / 2 * (t - β) * xg :=
    mul_le_mul_of_nonneg_left hgrad (mul_nonneg (by linarith) (by linarith))
  have S2 : β * t ^ 2 * (-(ε * (xg + sg))) ≤ β * t ^ 2 * (gg / a + a / 4 * ε ^ 2 * (xx + 2 * sx + ss)) :=
    mul_le_mul_of_nonneg_left hy2 (by positivity)
  linear_combination N1 + N2 + N3 + N4 + N5 + S1 + S2

theorem alg_b (α β a t ε ε' e xx vv gg xv xg vg sv sg sx ss b κ : ℝ)
    (hb : b = (α + 1) / 2) (hκ : κ = β * (b + 2 - α))
    (hα : 3 ≤ α) (hβ : 0 ≤ β) (ha : 0 < a) (ht : 0 < t) (ht2 : 2 * β ≤ t)
    (hε : 0 ≤ ε) (hεb : t * ε ≤ a) (hε' : ε' ≤ 0) (he : 0 ≤ e)
    (hxx : 0 ≤ xx) (hvv : 0 ≤ vv) (hgg : 0 ≤ gg) (hn : 0 ≤ xx + 2 * sx + ss)
    (hgrad : e ≤ xg)
    (hy3 : -(t * sg) ≤ t ^ 2 / (2 * a) * gg + a / 2 * ss) :
    (2 * t - κ) * e + (t ^ 2 - κ * t) * vg
      + ((2 * t * ε + t ^ 2 * ε') / 2 * (xx + 2 * sx + ss) + t ^ 2 * ε / 2 * (2 * (xv + sv)))
      + ((b + 1 - α) * b * xv + (b + 1 - α) * t * vv + (b + 1 - α) * t * β * vg
          + (β - t) * b * xg + (β - t) * t * vg + (β - t) * t * β * gg
          - t * ε * b * xx - t * ε * t * xv - t * ε * t * β * xg
          - t * ε * b * sx - t * ε * t * sv - t * ε * t * β * sg)
      + b * (α - 1 - b) / 2 * (2 * xv)
      ≤ β * e + (b + a * β) / 2 * t * ε * ss := by
  subst hb hκ
  have N1 : ((2 - (α + 1) / 2) * t + β * (α - 2) - β) * e ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ he
    have : (2 - (α + 1) / 2) * t + β * (α - 2) - β = (α - 3) * (β - t / 2) := by ring
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have N2 : (t ^ 2 * ε' / 2 + (2 - (α + 1) / 2) * t * ε / 2) * (xx + 2 * sx + ss) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hn
    have h1 : t ^ 2 * ε' / 2 ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0:ℝ) ≤ t ^ 2) hε'
      linarith
    have h2 : (2 - (α + 1) / 2) * t * ε / 2 ≤ 0 := by
      have : 0 ≤ t * ε := by positivity
      nlinarith
    linarith
  have N3 : -((α + 1) / 2 * t * ε / 2 * xx) ≤ 0 := by
    have : 0 ≤ (α + 1) / 2 * t * ε / 2 * xx := by
      have : 0 ≤ (α + 1) / 2 := by linarith
      positivity
    linarith
  have N4 : ((α + 1) / 2 + 1 - α) * t * vv ≤ 0 := by
    have : ((α + 1) / 2 + 1 - α) * t * vv = -((α - 3) / 2 * (t * vv)) := by ring
    rw [this]
    have : 0 ≤ (α - 3) / 2 * (t * vv) := mul_nonneg (by linarith) (by positivity)
    linarith
  have N5 : (β ^ 2 * t - β * t ^ 2 / 2) * gg ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hgg
    have : β ^ 2 * t - β * t ^ 2 / 2 = β * t * (β - t / 2) := by ring
    rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have S1 : (α + 1) / 2 * (t - β) * e ≤ (α + 1) / 2 * (t - β) * xg :=
    mul_le_mul_of_nonneg_left hgrad (mul_nonneg (by linarith) (by linarith))
  have S2 : 0 ≤ β * ε * t ^ 2 * xg := mul_nonneg (by positivity) (by linarith)
  have S3 : β * ε * t * (-(t * sg)) ≤ β * ε * t * (t ^ 2 / (2 * a) * gg + a / 2 * ss) :=
    mul_le_mul_of_nonneg_left hy3 (by positivity)
  have S4 : 0 ≤ β * t ^ 2 / 2 * gg * (1 - t * ε / a) := by
    have : 0 ≤ 1 - t * ε / a := by
      rw [sub_nonneg, div_le_one ha]; exact hεb
    positivity
  linear_combination N1 + N2 + N3 + N4 + N5 + S1 + S2 + S3 + S4


theorem young3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) (t a : ℝ)
    (ht : 0 ≤ t) (ha : 0 < a) :
    -(t * inner ℝ u v) ≤ t ^ 2 / (2 * a) * inner ℝ u u + a / 2 * inner ℝ v v := by
  have h : -inner ℝ u v ≤ ‖u‖ * ‖v‖ := (neg_le_abs _).trans (abs_real_inner_le_norm u v)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h1 : t * (-inner ℝ u v) ≤ t * (‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left h ht
  have hid : t ^ 2 / (2 * a) * ‖u‖ ^ 2 + a / 2 * ‖v‖ ^ 2 - t * (‖u‖ * ‖v‖)
      = (t * ‖u‖ - a * ‖v‖) ^ 2 / (2 * a) := by
    field_simp; ring
  have : 0 ≤ (t * ‖u‖ - a * ‖v‖) ^ 2 / (2 * a) := by positivity
  linarith

theorem deriv_nonpos_of_antitone (ε : ℝ → ℝ) (d t₀ s : ℝ) (hs : t₀ < s)
    (hd : HasDerivWithinAt ε d (Ici t₀) s) (hanti : AntitoneOn ε (Ici t₀)) : d ≤ 0 := by
  have h := (hd.hasDerivAt (Ici_mem_nhds hs)).tendsto_slope_zero_right
  refine le_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : (0:ℝ) < τ := hτ
  have : ε (s + τ) ≤ ε s := hanti (show t₀ ≤ s from hs.le) (show t₀ ≤ s + τ by linarith)
    (by linarith)
  rw [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hτ'.le) (by linarith)

/-- `Ė_b` expressed with the vectors `x, ẋ, ∇g(x), x⋆, ẍ, ∇²g(x)ẋ`. -/
theorem alg_vec_a {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (xs V Gv S A HV : H) (α β a s ε ε' e b κ : ℝ)
    (hb : b = (α + 1) / 2) (hκ : κ = β * (b + 2 - α))
    (hα : 3 ≤ α) (hβ : 0 ≤ β) (ha : 1 < a) (hs : 0 < s) (hs2 : 2 * β ≤ s)
    (hsa : β ≤ (1 - 1 / a) * s)
    (hε : 0 ≤ ε) (hε' : ε' ≤ -(a * β / 2) * ε ^ 2) (he : 0 ≤ e)
    (hgrad : e ≤ inner ℝ Gv (xs - S))
    (hode : A + (α / s) • V + β • HV + Gv + ε • xs = 0) :
    (2 * s - κ) * e + (s ^ 2 - κ * s) * inner ℝ Gv V
      + ((2 * s * ε + s ^ 2 * ε') / 2 * ‖xs‖ ^ 2 + s ^ 2 * ε / 2 * (2 * inner ℝ xs V))
      + 2 * inner ℝ (b • (xs - S) + s • (V + β • Gv))
          (b • V + (s • (A + β • HV) + (V + β • Gv))) / 2
      + b * (α - 1 - b) / 2 * (2 * inner ℝ (xs - S) V)
      ≤ β * e + b / 2 * s * ε * ‖S‖ ^ 2 := by
  obtain ⟨X, rfl⟩ : ∃ X, xs = X + S := ⟨xs - S, by abel⟩
  simp only [add_sub_cancel_right] at hgrad ⊢
  have hsA : s • (A + β • HV) = -(α • V + s • Gv + (s * ε) • (X + S)) := by
    have hA : A + β • HV = -((α / s) • V + Gv + ε • (X + S)) := by
      rw [eq_neg_iff_add_eq_zero, ← hode]; abel
    rw [hA, smul_neg, smul_add, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hs.ne']
  rw [hsA]
  have hn : 0 ≤ inner ℝ X X + 2 * inner ℝ S X + inner ℝ S S := by
    have h1 : 0 ≤ inner ℝ (X + S) (X + S) := real_inner_self_nonneg
    simp only [inner_add_left, inner_add_right, real_inner_comm] at h1
    linarith
  have hy2 := TikhCaseIAux.young2 Gv (X + S) a ε (by linarith) hε
  have key := alg_a α β a s ε ε' e (inner ℝ X X) (inner ℝ V V) (inner ℝ Gv Gv) (inner ℝ X V)
    (inner ℝ Gv X) (inner ℝ Gv V) (inner ℝ S V) (inner ℝ Gv S) (inner ℝ S X) (inner ℝ S S) b κ
    hb hκ hα hβ ha hs hs2 hsa hε hε' he (real_inner_self_nonneg) (real_inner_self_nonneg)
    (real_inner_self_nonneg) hn hgrad
    (by simp only [inner_add_left, inner_add_right, real_inner_comm] at hy2 ⊢; linarith)
  simp only [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm] at key ⊢
  linarith

theorem alg_vec_b {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (xs V Gv S A HV : H) (α β a s ε ε' e b κ : ℝ)
    (hb : b = (α + 1) / 2) (hκ : κ = β * (b + 2 - α))
    (hα : 3 ≤ α) (hβ : 0 ≤ β) (ha : 0 < a) (hs : 0 < s) (hs2 : 2 * β ≤ s)
    (hε : 0 ≤ ε) (hεb : s * ε ≤ a) (hε' : ε' ≤ 0) (he : 0 ≤ e)
    (hgrad : e ≤ inner ℝ Gv (xs - S))
    (hode : A + (α / s) • V + β • HV + Gv + ε • xs = 0) :
    (2 * s - κ) * e + (s ^ 2 - κ * s) * inner ℝ Gv V
      + ((2 * s * ε + s ^ 2 * ε') / 2 * ‖xs‖ ^ 2 + s ^ 2 * ε / 2 * (2 * inner ℝ xs V))
      + 2 * inner ℝ (b • (xs - S) + s • (V + β • Gv))
          (b • V + (s • (A + β • HV) + (V + β • Gv))) / 2
      + b * (α - 1 - b) / 2 * (2 * inner ℝ (xs - S) V)
      ≤ β * e + (b + a * β) / 2 * s * ε * ‖S‖ ^ 2 := by
  obtain ⟨X, rfl⟩ : ∃ X, xs = X + S := ⟨xs - S, by abel⟩
  simp only [add_sub_cancel_right] at hgrad ⊢
  have hsA : s • (A + β • HV) = -(α • V + s • Gv + (s * ε) • (X + S)) := by
    have hA : A + β • HV = -((α / s) • V + Gv + ε • (X + S)) := by
      rw [eq_neg_iff_add_eq_zero, ← hode]; abel
    rw [hA, smul_neg, smul_add, smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hs.ne']
  rw [hsA]
  have hn : 0 ≤ inner ℝ X X + 2 * inner ℝ S X + inner ℝ S S := by
    have h1 : 0 ≤ inner ℝ (X + S) (X + S) := real_inner_self_nonneg
    simp only [inner_add_left, inner_add_right, real_inner_comm] at h1
    linarith
  have hy3 := young3 Gv S s a hs.le ha
  have key := alg_b α β a s ε ε' e (inner ℝ X X) (inner ℝ V V) (inner ℝ Gv Gv) (inner ℝ X V)
    (inner ℝ Gv X) (inner ℝ Gv V) (inner ℝ S V) (inner ℝ Gv S) (inner ℝ S X) (inner ℝ S S) b κ
    hb hκ hα hβ ha hs hs2 hε hεb hε' he (real_inner_self_nonneg) (real_inner_self_nonneg)
    (real_inner_self_nonneg) hn hgrad hy3
  simp only [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm] at key ⊢
  linarith

end Tikh31Aux

namespace Tikh31Aux

theorem core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H) (S : H)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hGA : GeneralAssumption g t₀ ε ε')
    (hx : IsSolution g α β t₀ ε u₀ v₀ x xd xdd) (hS : S ∈ argminSet g)
    (b κ : ℝ) (hb : b = (α + 1) / 2) (hκ : κ = β * (b + 2 - α)) (M : ℝ) (hM : 0 ≤ M)
    (ts : ℝ) (hts : t₀ < ts) (hts2 : 2 * β ≤ ts)
    (hĖ : ∀ s, ts ≤ s →
      (2 * s - κ) * (g (x s) - g S) + (s ^ 2 - κ * s) * inner ℝ (gradient g (x s)) (xd s)
      + ((2 * s * ε s + s ^ 2 * ε' s) / 2 * ‖x s‖ ^ 2 + s ^ 2 * ε s / 2 * (2 * inner ℝ (x s) (xd s)))
      + 2 * inner ℝ (b • (x s - S) + s • (xd s + β • gradient g (x s)))
          (b • xd s + (s • (xdd s + β • (fderiv ℝ (gradient g) (x s)) (xd s))
            + (xd s + β • gradient g (x s)))) / 2
      + b * (α - 1 - b) / 2 * (2 * inner ℝ (x s - S) (xd s))
      ≤ β * (g (x s) - g S) + M * s * ε s * ‖S‖ ^ 2)
    (hJ : Tendsto (fun T => (T ^ 2)⁻¹ * ∫ τ in ts..T, τ * ε τ) atTop (𝓝 0)) :
    Tendsto (fun t => g (x t)) atTop (𝓝 (g S)) := by
  have hgi : ∀ z v : H, fderiv ℝ g z v = inner ℝ (gradient g z) v := fun z v => by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hts0 : 0 < ts := lt_trans ht₀ hts
  have hκβ : κ ≤ β := by rw [hκ, hb]; nlinarith
  have hbα : 0 ≤ b * (α - 1 - b) := by rw [hb]; nlinarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, E = fun s => (s ^ 2 - κ * s) * (g (x s) - g S)
      + s ^ 2 * ε s / 2 * ‖x s‖ ^ 2
      + ‖b • (x s - S) + s • (xd s + β • gradient g (x s))‖ ^ 2 / 2
      + b * (α - 1 - b) / 2 * ‖x s - S‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ed, hEd⟩ : ∃ Ed : ℝ → ℝ, Ed = fun s =>
      (2 * s - κ) * (g (x s) - g S) + (s ^ 2 - κ * s) * inner ℝ (gradient g (x s)) (xd s)
      + ((2 * s * ε s + s ^ 2 * ε' s) / 2 * ‖x s‖ ^ 2 + s ^ 2 * ε s / 2 * (2 * inner ℝ (x s) (xd s)))
      + 2 * inner ℝ (b • (x s - S) + s • (xd s + β • gradient g (x s)))
          (b • xd s + (s • (xdd s + β • (fderiv ℝ (gradient g) (x s)) (xd s))
            + (xd s + β • gradient g (x s)))) / 2
      + b * (α - 1 - b) / 2 * (2 * inner ℝ (x s - S) (xd s)) := ⟨_, rfl⟩
  have hĖ' : ∀ s, ts ≤ s → Ed s ≤ β * (g (x s) - g S) + M * s * ε s * ‖S‖ ^ 2 := by
    intro s hs; rw [hEd]; exact hĖ s hs
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun s => s * ε s := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * M * ‖S‖ ^ 2 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hεc : ContinuousOn ε (Ici t₀) := fun s hs =>
    (hGA.hasDerivWithinAt_eps s hs).continuousWithinAt
  have hfc : ContinuousOn f (Ici t₀) := by
    rw [hf]; exact continuousOn_id.mul hεc
  have hfii : ∀ u v, t₀ ≤ u → t₀ ≤ v → IntervalIntegrable f MeasureTheory.volume u v := by
    intro u v hu hv
    refine (hfc.mono fun w hw => ?_).intervalIntegrable
    rcases Set.mem_uIcc.1 hw with h | h
    · exact le_trans hu h.1
    · exact le_trans hv h.1
  have he0 : ∀ s, 0 ≤ g (x s) - g S := fun s => by have := hS (x s); linarith
  have hElow : ∀ s, ts ≤ s → s * (s - β) * (g (x s) - g S) ≤ E s := by
    intro s hs
    have hs0 : 0 < s := by linarith
    rw [hE]
    have e1 : s * (s - β) * (g (x s) - g S) ≤ (s ^ 2 - κ * s) * (g (x s) - g S) := by
      apply mul_le_mul_of_nonneg_right _ (he0 s); nlinarith
    have e2 : 0 ≤ s ^ 2 * ε s / 2 * ‖x s‖ ^ 2 := by
      have := hGA.eps_nonneg s (show t₀ ≤ s by linarith); positivity
    have e3 : 0 ≤ ‖b • (x s - S) + s • (xd s + β • gradient g (x s))‖ ^ 2 / 2 := by positivity
    have e4 : 0 ≤ b * (α - 1 - b) / 2 * ‖x s - S‖ ^ 2 := by positivity
    simp only
    linarith
  -- derivatives
  have hEder : ∀ s, t₀ < s → HasDerivAt E (Ed s) s := by
    intro s hs
    have hsI : s ∈ Ici t₀ := le_of_lt hs
    have hmem : Ici t₀ ∈ 𝓝 s := Ici_mem_nhds hs
    obtain ⟨hd1, hd2, -⟩ := hx.1 s hsI
    have hxs : HasDerivAt x (xd s) s := hd1.hasDerivAt hmem
    have hxds : HasDerivAt xd (xdd s) s := hd2.hasDerivAt hmem
    have hεs : HasDerivAt ε (ε' s) s := (hGA.hasDerivWithinAt_eps s hsI).hasDerivAt hmem
    have hG : HasDerivAt (fun s => gradient g (x s)) (fderiv ℝ (gradient g) (x s) (xd s)) s :=
      (hGA.differentiable_gradient (x s)).hasFDerivAt.comp_hasDerivAt s hxs
    have hgd : HasDerivAt (fun s => g (x s)) (fderiv ℝ g (x s) (xd s)) s :=
      (hGA.differentiable (x s)).hasFDerivAt.comp_hasDerivAt s hxs
    have hu := ((hxs.sub_const S).const_smul b).add
      ((hasDerivAt_id' s).smul (hxds.add (hG.const_smul β)))
    have h := ((((hasDerivAt_pow 2 s).sub ((hasDerivAt_id' s).const_mul κ)).mul
      (hgd.sub_const (g S))).add
      ((((hasDerivAt_pow 2 s).mul hεs).div_const 2).mul hxs.norm_sq)).add
      (hu.norm_sq.div_const 2) |>.add ((hxs.sub_const S).norm_sq.const_mul (b * (α - 1 - b) / 2))
    rw [hE, hEd]
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply', one_smul,
      Nat.reduceSub, pow_one, Nat.cast_ofNat, hgi, mul_one]
    try ring
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ, Ψ = fun s => s / (s - β) * E s - K * ∫ τ in ts..s, f τ :=
    ⟨_, rfl⟩
  have hΨd : ∀ s, ts ≤ s → ∃ D, HasDerivAt Ψ D s ∧ D ≤ 0 := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have hq : 0 < s - β := by linarith
    have hst : t₀ < s := by linarith
    have hmem : Ici t₀ ∈ 𝓝 s := Ici_mem_nhds hst
    have hw : HasDerivAt (fun s => s / (s - β)) ((1 * (s - β) - s * 1) / (s - β) ^ 2) s :=
      (hasDerivAt_id' s).div ((hasDerivAt_id' s).sub_const β) hq.ne'
    have hI : HasDerivAt (fun u => ∫ τ in ts..u, f τ) (f s) s :=
      intervalIntegral.integral_hasDerivAt_right (hfii ts s hts.le hst.le)
        ((hfc.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi s hst)
        (hfc.continuousAt hmem)
    have hΦ := (hw.mul (hEder s hst)).sub (hI.const_mul K)
    rw [hΨ]
    refine ⟨_, hΦ, ?_⟩
    have h1 : β * (s * (s - β) * (g (x s) - g S)) ≤ β * E s :=
      mul_le_mul_of_nonneg_left (hElow s hs) hβ
    have h2 : s * (s - β) * Ed s ≤ s * (s - β) * (β * (g (x s) - g S) + M * s * ε s * ‖S‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hĖ' s hs) (by positivity)
    have hεs0 : 0 ≤ ε s := hGA.eps_nonneg s hst.le
    have h3 : M * ‖S‖ ^ 2 * s * ε s * (s - β) * (2 * β - s) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have key : -β * E s + s * (s - β) * Ed s - K * f s * (s - β) ^ 2 ≤ 0 := by
      rw [hK, hf]; simp only; nlinarith
    have hexp : (1 * (s - β) - s * 1) / (s - β) ^ 2 * E s + s / (s - β) * Ed s - K * f s
        = (-β * E s + s * (s - β) * Ed s - K * f s * (s - β) ^ 2) / (s - β) ^ 2 := by
      field_simp; ring
    rw [hexp]
    exact div_nonpos_of_nonpos_of_nonneg key (sq_nonneg _)
  have hanti : AntitoneOn Ψ (Ici ts) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro s hs
      obtain ⟨D, hD, -⟩ := hΨd s hs
      exact hD.continuousAt.continuousWithinAt
    · rw [interior_Ici]
      intro s hs
      obtain ⟨D, hD, -⟩ := hΨd s (le_of_lt hs)
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro s hs
      obtain ⟨D, hD, hle⟩ := hΨd s (le_of_lt hs)
      rw [hD.deriv]; exact hle
  have hup : ∀ T, ts ≤ T → g (x T) - g S ≤
      (ts / (ts - β) * E ts) * (T ^ 2)⁻¹ + K * ((T ^ 2)⁻¹ * ∫ τ in ts..T, τ * ε τ) := by
    intro T hT
    have h1 := hanti (show ts ∈ Ici ts from le_refl ts) hT hT
    rw [hΨ] at h1
    simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at h1
    have hT0 : 0 < T := by linarith
    have hq : 0 < T - β := by linarith
    have h2 : T ^ 2 * (g (x T) - g S) ≤ T / (T - β) * E T := by
      have := mul_le_mul_of_nonneg_left (hElow T hT) (div_nonneg hT0.le hq.le)
      have e : T / (T - β) * (T * (T - β) * (g (x T) - g S)) = T ^ 2 * (g (x T) - g S) := by
        field_simp
      linarith
    rw [hf] at h1
    have h3 : T ^ 2 * (g (x T) - g S) ≤ ts / (ts - β) * E ts + K * ∫ τ in ts..T, τ * ε τ := by
      linarith
    have hT2 : 0 < T ^ 2 := by positivity
    have e : (ts / (ts - β) * E ts) * (T ^ 2)⁻¹ + K * ((T ^ 2)⁻¹ * ∫ τ in ts..T, τ * ε τ)
        = (ts / (ts - β) * E ts + K * ∫ τ in ts..T, τ * ε τ) / T ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ hT2]
    linarith
  have hlim : Tendsto (fun T => (ts / (ts - β) * E ts) * (T ^ 2)⁻¹
      + K * ((T ^ 2)⁻¹ * ∫ τ in ts..T, τ * ε τ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun T : ℝ => (T ^ 2)⁻¹) atTop (𝓝 0) :=
      (tendsto_pow_atTop two_ne_zero).inv_tendsto_atTop
    have h0 := ((tendsto_const_nhds (x := ts / (ts - β) * E ts)).mul hinv).add
      ((tendsto_const_nhds (x := K)).mul hJ)
    simp only [mul_zero, add_zero] at h0
    exact h0
  have he : Tendsto (fun T => g (x T) - g S) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall he0) ((eventually_ge_atTop ts).mono hup)
  have := he.add_const (g S)
  simpa using this

end Tikh31Aux

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (g : H → ℝ) (α β t₀ : ℝ) (ε ε' : ℝ → ℝ) (u₀ v₀ : H) (x xd xdd : ℝ → H)
    (ht₀ : 0 < t₀) (hα : 3 ≤ α) (hβ : 0 ≤ β)
    (hGA : GeneralAssumption g t₀ ε ε')
    (hx : IsSolution g α β t₀ ε u₀ v₀ x xd xdd)
    (hcond :
      (MeasureTheory.IntegrableOn (fun t => ε t / t) (Ici t₀) ∧
        ∃ a > (1 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε' t ≤ -(a * β / 2) * ε t ^ 2) ∨
      (∃ a > (0 : ℝ), ∃ t₁ ≥ t₀, ∀ t ≥ t₁, ε t ≤ a / t)) :
    Tendsto (fun t => g (x t)) atTop (𝓝 (minValue g)) := by
  obtain ⟨S, hS⟩ := hGA.argmin_nonempty
  have hmin : minValue g = g S :=
    IsLeast.csInf_eq ⟨⟨S, rfl⟩, by rintro _ ⟨u, rfl⟩; exact hS u⟩
  rw [hmin]
  have hgi : ∀ z v : H, fderiv ℝ g z v = inner ℝ (gradient g z) v := fun z v => by
    rw [gradient, InnerProductSpace.toDual_symm_apply]
  have hεc : ContinuousOn ε (Ici t₀) := fun s hs =>
    (hGA.hasDerivWithinAt_eps s hs).continuousWithinAt
  have hgrad : ∀ s, g (x s) - g S ≤ inner ℝ (gradient g (x s)) (x s - S) := by
    intro s
    have h1 := TikhKey2Aux.grad_ineq g hGA.convex (x s) S (hGA.differentiable (x s))
    rw [hgi, inner_sub_right] at h1
    rw [inner_sub_right]
    linarith
  have he0 : ∀ s, 0 ≤ g (x s) - g S := fun s => by have := hS (x s); linarith
  rcases hcond with ⟨hint, a, ha, t₁, ht₁, hεd⟩ | ⟨a, ha, t₁, ht₁, hεb⟩
  · have h1a : 0 < 1 - 1 / a := by
      have : 1 / a < 1 := (div_lt_one (by linarith)).2 ha
      linarith
    set ts := max (t₀ + 1) (max t₁ (max (2 * β) (β / (1 - 1 / a)))) with hts
    have hts0 : t₀ + 1 ≤ ts := le_max_left _ _
    have hts1 : t₁ ≤ ts := le_trans (le_max_left _ _) (le_max_right _ _)
    have hts2 : 2 * β ≤ ts :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hts3 : β / (1 - 1 / a) ≤ ts :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    refine Tikh31Aux.core g α β t₀ ε ε' u₀ v₀ x xd xdd S ht₀ hα hβ hGA hx hS ((α + 1) / 2)
      (β * ((α + 1) / 2 + 2 - α)) rfl rfl ((α + 1) / 2 / 2) (by linarith) ts (by linarith) hts2
      ?_ ?_
    · intro s hs
      have hs0 : 0 < s := by linarith
      have hsI : s ∈ Ici t₀ := show t₀ ≤ s by linarith
      obtain ⟨-, -, hode⟩ := hx.1 s hsI
      have hsa : β ≤ (1 - 1 / a) * s := by
        have := mul_le_mul_of_nonneg_left (le_trans hts3 hs) h1a.le
        rwa [mul_div_cancel₀ _ h1a.ne'] at this
      exact Tikh31Aux.alg_vec_a (x s) (xd s) (gradient g (x s)) S (xdd s)
        (fderiv ℝ (gradient g) (x s) (xd s)) α β a s (ε s) (ε' s) (g (x s) - g S)
        ((α + 1) / 2) (β * ((α + 1) / 2 + 2 - α)) rfl rfl hα hβ ha hs0 (le_trans hts2 hs) hsa
        (hGA.eps_nonneg s hsI) (hεd s (le_trans hts1 hs)) (he0 s) (hgrad s) hode
    · have htsp : 0 < ts := by linarith
      have hA := TikhonovHDD.Strong.lemma_A_1 ts htsp (fun s => ε s / s) (fun s => s ^ 2)
        (hint.mono_set (fun u hu => show t₀ ≤ u by have : ts < u := hu; linarith))
        (fun u hu => div_nonneg (hGA.eps_nonneg u (show t₀ ≤ u by have : ts < u := hu; linarith))
          (by have : ts < u := hu; linarith))
        ((hεc.mono (fun u hu => show t₀ ≤ u by have : ts < u := hu; linarith)).div continuousOn_id
          (fun u hu => by have : ts < u := hu; exact ne_of_gt (by linarith)))
        (fun u _ => sq_nonneg u)
        (fun u hu v _ huv => pow_le_pow_left₀ (by have : ts ≤ u := hu; linarith) huv 2)
        (tendsto_pow_atTop two_ne_zero)
      refine hA.congr' ?_
      filter_upwards [eventually_ge_atTop ts] with T hT
      congr 1
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le hT] at hu
      have hu0 : u ≠ 0 := ne_of_gt (by linarith [hu.1])
      show u ^ 2 * (ε u / u) = u * ε u
      field_simp
  · set ts := max (t₀ + 1) (max t₁ (2 * β)) with hts
    have hts0 : t₀ + 1 ≤ ts := le_max_left _ _
    have hts1 : t₁ ≤ ts := le_trans (le_max_left _ _) (le_max_right _ _)
    have hts2 : 2 * β ≤ ts := le_trans (le_max_right _ _) (le_max_right _ _)
    refine Tikh31Aux.core g α β t₀ ε ε' u₀ v₀ x xd xdd S ht₀ hα hβ hGA hx hS ((α + 1) / 2)
      (β * ((α + 1) / 2 + 2 - α)) rfl rfl (((α + 1) / 2 + a * β) / 2)
      (by have : 0 ≤ a * β := by positivity
          linarith) ts (by linarith) hts2 ?_ ?_
    · intro s hs
      have hs0 : 0 < s := by linarith
      have hsI : s ∈ Ici t₀ := show t₀ ≤ s by linarith
      obtain ⟨-, -, hode⟩ := hx.1 s hsI
      have hεb' : s * ε s ≤ a := by
        have := mul_le_mul_of_nonneg_left (hεb s (le_trans hts1 hs)) hs0.le
        rwa [mul_div_cancel₀ _ hs0.ne'] at this
      exact Tikh31Aux.alg_vec_b (x s) (xd s) (gradient g (x s)) S (xdd s)
        (fderiv ℝ (gradient g) (x s) (xd s)) α β a s (ε s) (ε' s) (g (x s) - g S)
        ((α + 1) / 2) (β * ((α + 1) / 2 + 2 - α)) rfl rfl hα hβ ha hs0 (le_trans hts2 hs)
        (hGA.eps_nonneg s hsI) hεb'
        (Tikh31Aux.deriv_nonpos_of_antitone ε (ε' s) t₀ s (by linarith)
          (hGA.hasDerivWithinAt_eps s hsI) hGA.eps_antitoneOn)
        (he0 s) (hgrad s) hode
    · have hfc : ContinuousOn (fun τ => τ * ε τ) (Ici t₀) := continuousOn_id.mul hεc
      have hupper : Tendsto (fun T : ℝ => a * T⁻¹) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := a)).mul tendsto_inv_atTop_zero
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
      · filter_upwards [eventually_ge_atTop ts] with T hT
        refine mul_nonneg (inv_nonneg.2 (sq_nonneg _)) ?_
        refine intervalIntegral.integral_nonneg hT (fun u hu => ?_)
        exact mul_nonneg (by linarith [hu.1]) (hGA.eps_nonneg u (show t₀ ≤ u by linarith [hu.1]))
      · filter_upwards [eventually_ge_atTop ts] with T hT
        have hT0 : 0 < T := by linarith
        have hii : IntervalIntegrable (fun τ => τ * ε τ) MeasureTheory.volume ts T :=
          (hfc.mono (fun w hw => by
            rw [Set.uIcc_of_le hT] at hw; show t₀ ≤ w; linarith [hw.1])).intervalIntegrable
        have hle : ∫ τ in ts..T, τ * ε τ ≤ ∫ τ in ts..T, a :=
          intervalIntegral.integral_mono_on hT hii intervalIntegrable_const (fun u hu => by
            have hu0 : 0 < u := by linarith [hu.1]
            have := mul_le_mul_of_nonneg_left (hεb u (by linarith [hu.1])) hu0.le
            rwa [mul_div_cancel₀ _ hu0.ne'] at this)
        rw [intervalIntegral.integral_const, smul_eq_mul] at hle
        have h2 : (T ^ 2)⁻¹ * ∫ τ in ts..T, τ * ε τ ≤ (T ^ 2)⁻¹ * ((T - ts) * a) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 (sq_nonneg _))
        have h3 : (T ^ 2)⁻¹ * ((T - ts) * a) ≤ a * T⁻¹ := by
          have e : a * T⁻¹ = (T ^ 2)⁻¹ * (T * a) := by field_simp
          rw [e]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (sq_nonneg _))
          nlinarith
        linarith
