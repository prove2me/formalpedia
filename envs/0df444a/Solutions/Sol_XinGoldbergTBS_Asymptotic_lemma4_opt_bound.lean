-- Prove2me | solution 1 for XinGoldbergTBS.Asymptotic.lemma4_opt_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T15:18:39.585741+00:00
-- url     : https://prove2.me/submissions/5c0d6259-74e8-4b33-9a91-d96a345a5f21

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants
import Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
import Definitions.Def_XinGoldbergTBS_Asymptotic_Witness
import Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma2
import Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma4_bounds

set_option autoImplicit false

universe u

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XGL4

open XinGoldbergTBS.Asymptotic

instance pathLaw_isProb (μ : DemandLaw) : IsProbabilityMeasure (pathLaw μ) := by
  unfold pathLaw; infer_instance

lemma G_le (κ : Costs) (z : ℝ) : G κ z ≤ max κ.b κ.h * |z| := by
  unfold G
  have hb := le_max_left κ.b κ.h
  have hh := le_max_right κ.b κ.h
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz, max_eq_left hz, max_eq_right (by linarith : -z ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hz, max_eq_right hz, max_eq_left (by linarith : 0 ≤ -z)]
    nlinarith

lemma G_ge_neg (κ : Costs) (z : ℝ) : κ.b * (-z) ≤ G κ z := by
  unfold G
  have h1 : 0 ≤ κ.h * max z 0 := mul_nonneg κ.h_pos.le (le_max_right _ _)
  have h2 : κ.b * (-z) ≤ κ.b * max (-z) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) κ.b_pos.le
  linarith

lemma ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂μ.law, 0 ≤ d := by
  have h := μ.nonneg
  rw [measure_eq_zero_iff_ae_notMem] at h
  filter_upwards [h] with d hd
  simpa using hd

lemma mean_nonneg (μ : DemandLaw) : 0 ≤ μ.mean :=
  integral_nonneg_of_ae (ae_nonneg μ)

lemma mp_eval (μ : DemandLaw) (k : ℕ) :
    MeasurePreserving (fun x : Path => x k) (pathLaw μ) μ.law :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => μ.law) k

lemma path_ae_nonneg (μ : DemandLaw) : ∀ᵐ d ∂pathLaw μ, ∀ k, 0 ≤ d k := by
  rw [ae_all_iff]
  intro k
  have hmp := mp_eval μ k
  have h : ∀ᵐ y ∂(pathLaw μ).map (fun x : Path => x k), 0 ≤ y := by
    rw [hmp.map_eq]; exact ae_nonneg μ
  exact ae_of_ae_map hmp.measurable.aemeasurable h

lemma lintegral_coord (μ : DemandLaw) (k : ℕ) :
    ∫⁻ d, ENNReal.ofReal (d k) ∂pathLaw μ = ENNReal.ofReal μ.mean := by
  have h := (mp_eval μ k).lintegral_comp (f := fun y : ℝ => ENNReal.ofReal y)
    ENNReal.measurable_ofReal
  rw [show (∫⁻ d, ENNReal.ofReal (d k) ∂pathLaw μ) = ∫⁻ y, ENNReal.ofReal y ∂μ.law from h,
    DemandLaw.mean]
  refine (ofReal_integral_eq_lintegral_ofReal (f := fun y : ℝ => y) μ.integrable ?_).symm
  filter_upwards [ae_nonneg μ] with y hy
  exact hy

/-! ## The zero policy -/

/-- `∑_{j<n} (r - d_j)`. -/
def Wz (r : ℝ) (d : Path) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, (r - d j)

def zeroPol : SSPolicy := ⟨fun _ _ => 0, fun _ => measurable_const⟩

lemma zero_pos (r : ℝ) (d : Path) (n : ℕ) : ssPosition zeroPol r 0 d n = Wz r d n := by
  induction n with
  | zero => simp [ssPosition, Wz]
  | succ n ih =>
    rw [ssPosition, ih]
    simp only [ssOrder, zeroPol, Wz, Finset.sum_range_succ, NNReal.coe_zero]
    ring

lemma zero_cost (κ : Costs) (L₀ : ℕ) (r : ℝ) (d : Path) (i : ℕ) :
    ssCost κ L₀ zeroPol r 0 d i = ENNReal.ofReal (G κ (Wz r d (i + (L₀ + 1)))) := by
  unfold ssCost ssOrderUpTo
  rw [zero_pos]
  congr 2
  have h0 : ssOrder zeroPol d i = 0 := by simp [ssOrder, zeroPol]
  rw [h0, add_zero]
  unfold Wz
  have hsplit := Finset.sum_range_add (fun j => r - d j) i (L₀ + 1)
  beta_reduce at hsplit
  rw [hsplit, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma Wz_abs_le (r : ℝ) (hr : 0 ≤ r) (d : Path) (hd : ∀ k, 0 ≤ d k) (n : ℕ) :
    |Wz r d n| ≤ ∑ j ∈ Finset.range n, (r + d j) := by
  unfold Wz
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_le]
  constructor <;> linarith [hd j]

lemma zero_disc_le (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hr : 0 ≤ r) :
    ∫⁻ d, ssDiscCost κ L₀ α zeroPol r 0 d ∂pathLaw μ ≤
      ENNReal.ofReal (max κ.b κ.h * (r + μ.mean) *
        (α / (1 - α) ^ 2 + ((L₀ : ℝ) + 1) * (1 - α)⁻¹)) := by
  set M := max κ.b κ.h with hMdef
  have hM : 0 ≤ M := le_trans κ.b_pos.le (le_max_left _ _)
  have hE := mean_nonneg μ
  set g : ℕ → Path → ℝ≥0∞ := fun i d => ENNReal.ofReal (α ^ i) * (ENNReal.ofReal M *
      ∑ j ∈ Finset.range (i + (L₀ + 1)), (ENNReal.ofReal r + ENNReal.ofReal (d j))) with hg
  have hmj : ∀ j, Measurable (fun d : Path => ENNReal.ofReal r + ENNReal.ofReal (d j)) :=
    fun j => measurable_const.add (measurable_pi_apply j).ennreal_ofReal
  have hgm : ∀ i, Measurable (g i) := fun i =>
    ((Finset.measurable_sum _ fun j _ => hmj j).const_mul _).const_mul _
  have hpt : ∀ᵐ d ∂pathLaw μ, ssDiscCost κ L₀ α zeroPol r 0 d ≤ ∑' i : ℕ, g i d := by
    filter_upwards [path_ae_nonneg μ] with d hd
    unfold ssDiscCost
    refine ENNReal.tsum_le_tsum fun i => ?_
    simp only [hg]
    gcongr
    rw [zero_cost]
    calc ENNReal.ofReal (G κ (Wz r d (i + (L₀ + 1))))
        ≤ ENNReal.ofReal (M * ∑ j ∈ Finset.range (i + (L₀ + 1)), (r + d j)) := by
          apply ENNReal.ofReal_le_ofReal
          exact (G_le κ _).trans (mul_le_mul_of_nonneg_left (Wz_abs_le r hr d hd _) hM)
      _ = ENNReal.ofReal M *
            ∑ j ∈ Finset.range (i + (L₀ + 1)), (ENNReal.ofReal r + ENNReal.ofReal (d j)) := by
          rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_sum_of_nonneg (fun j _ => by linarith [hd j])]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          exact ENNReal.ofReal_add hr (hd j)
  set f : ℕ → ℝ := fun i => α ^ i * (M * (((i + (L₀ + 1) : ℕ) : ℝ) * (r + μ.mean))) with hf
  have hint : ∀ i : ℕ, ∫⁻ d, g i d ∂pathLaw μ = ENNReal.ofReal (f i) := by
    intro i
    simp only [hg, hf]
    rw [lintegral_const_mul _ ((Finset.measurable_sum _ fun j _ => hmj j).const_mul _),
      lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => hmj j),
      lintegral_finsetSum _ (fun j _ => hmj j)]
    have hj : ∀ j, ∫⁻ d, (ENNReal.ofReal r + ENNReal.ofReal (d j)) ∂pathLaw μ =
        ENNReal.ofReal r + ENNReal.ofReal μ.mean := by
      intro j
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_coord]
    simp only [hj, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (pow_nonneg hα0.le _), ENNReal.ofReal_mul hM,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_add hr hE, ENNReal.ofReal_natCast]
  have hnorm : ‖α‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hα0]; exact hα1
  have hsum : HasSum f (M * (r + μ.mean) * (α / (1 - α) ^ 2 + ((L₀ : ℝ) + 1) * (1 - α)⁻¹)) := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
    have h2 := (hasSum_geometric_of_lt_one hα0.le hα1).mul_left ((L₀ : ℝ) + 1)
    have h3 := (h1.add h2).mul_left (M * (r + μ.mean))
    have hfe : f = fun i : ℕ => M * (r + μ.mean) * ((i : ℝ) * α ^ i + ((L₀ : ℝ) + 1) * α ^ i) := by
      funext i
      simp only [hf]
      push_cast
      ring
    rw [hfe]
    exact h3
  have hfnn : ∀ i, 0 ≤ f i := fun i => by
    simp only [hf]
    have := pow_nonneg hα0.le i
    have : (0 : ℝ) ≤ ((i + (L₀ + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ r + μ.mean := by linarith
    positivity
  calc ∫⁻ d, ssDiscCost κ L₀ α zeroPol r 0 d ∂pathLaw μ
      ≤ ∫⁻ d, ∑' i, g i d ∂pathLaw μ := lintegral_mono_ae hpt
    _ = ∑' i, ∫⁻ d, g i d ∂pathLaw μ := lintegral_tsum (fun i => (hgm i).aemeasurable)
    _ = ∑' i, ENNReal.ofReal (f i) := by simp only [hint]
    _ = ENNReal.ofReal (∑' i, f i) := (ENNReal.ofReal_tsum_of_nonneg hfnn hsum.summable).symm
    _ = _ := by rw [hsum.tsum_eq]

/-! ## Shifting the initial position below the first order-up-to level -/

/-- The (constant) first order of `π`. -/
def u0 (π : SSPolicy) : ℝ := (π.order 0 (fun i => Fin.elim0 i) : ℝ)

lemma ssOrder_zero (π : SSPolicy) (d : Path) : ssOrder π d 0 = u0 π := by
  unfold ssOrder u0
  congr 2
  funext i
  exact Fin.elim0 i

def shiftPol (π : SSPolicy) (c : ℝ≥0) : SSPolicy where
  order k v := if k = 0 then c else π.order k v
  measurable_order k := by
    by_cases hk : k = 0
    · subst hk
      simpa using (measurable_const : Measurable fun _ : Fin 0 → ℝ => c)
    · simpa [hk] using π.measurable_order k

lemma shift_upTo (π : SSPolicy) (r x x' : ℝ) (h : x' ≤ x + u0 π) (d : Path) (i : ℕ) :
    ssOrderUpTo (shiftPol π (x + u0 π - x').toNNReal) r x' d i = ssOrderUpTo π r x d i := by
  induction i with
  | zero =>
    have e : ssOrder (shiftPol π (x + u0 π - x').toNNReal) d 0 =
        ((x + u0 π - x').toNNReal : ℝ) := by
      simp [ssOrder, shiftPol]
    show x' + ssOrder _ d 0 = x + ssOrder π d 0
    rw [e, ssOrder_zero, Real.coe_toNNReal _ (by linarith)]
    ring
  | succ i ih =>
    have e1 : ∀ (ρ : SSPolicy) (y : ℝ), ssOrderUpTo ρ r y d (i + 1) =
        ssOrderUpTo ρ r y d i - (d i - r) + ssOrder ρ d (i + 1) := by
      intro ρ y
      simp only [ssOrderUpTo, ssPosition]
    have e2 : ssOrder (shiftPol π (x + u0 π - x').toNNReal) d (i + 1) = ssOrder π d (i + 1) := by
      simp [ssOrder, shiftPol]
    rw [e1, e1, ih, e2]

lemma shift_cost (κ : Costs) (L₀ : ℕ) (π : SSPolicy) (r x x' : ℝ) (h : x' ≤ x + u0 π)
    (d : Path) (i : ℕ) :
    ssCost κ L₀ (shiftPol π (x + u0 π - x').toNNReal) r x' d i = ssCost κ L₀ π r x d i := by
  unfold ssCost
  rw [shift_upTo π r x x' h]

/-! ## The finite-horizon value from any initial position -/

lemma key (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) (n : ℕ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (Sb Emax : ℝ) (hSb : 0 ≤ Sb) (V : ℝ≥0∞)
    (hin : ∀ x' : ℝ, |x'| ≤ Sb → V ≤ Vn μ κ L₀ α n r x' + ENNReal.ofReal Emax)
    (hV : V ≤ ENNReal.ofReal (κ.b * (Sb - ((L₀ : ℝ) + 1) * r))) (x : ℝ) :
    V ≤ Vn μ κ L₀ α n r x + ENNReal.ofReal Emax := by
  unfold Vn
  rw [ENNReal.iInf_add]
  refine le_iInf fun π => ?_
  by_cases hy : x + u0 π < -Sb
  · refine hV.trans (le_trans ?_ le_self_add)
    calc ENNReal.ofReal (κ.b * (Sb - ((L₀ : ℝ) + 1) * r))
        = ∫⁻ _d, ENNReal.ofReal (κ.b * (Sb - ((L₀ : ℝ) + 1) * r)) ∂pathLaw μ := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i
            ∂pathLaw μ := by
          apply lintegral_mono_ae
          filter_upwards [path_ae_nonneg μ] with d hd
          have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.2 (by omega)
          refine le_trans ?_ (Finset.single_le_sum
            (f := fun i => ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i)
            (fun _ _ => bot_le) h0)
          simp only [pow_zero, ENNReal.ofReal_one, one_mul]
          unfold ssCost ssOrderUpTo
          apply ENNReal.ofReal_le_ofReal
          refine le_trans ?_ (G_ge_neg κ _)
          have hs : ∑ k ∈ Finset.range (L₀ + 1), (-r) ≤
              ∑ k ∈ Finset.range (L₀ + 1), (d (0 + k) - r) :=
            Finset.sum_le_sum fun k _ => by linarith [hd (0 + k)]
          have hs2 : ∑ k ∈ Finset.range (L₀ + 1), (-r) = -(((L₀ : ℝ) + 1) * r) := by
            simp [Finset.sum_const, nsmul_eq_mul]
          rw [hs2] at hs
          have hp : ssPosition π r x d 0 = x := rfl
          rw [hp, ssOrder_zero]
          apply mul_le_mul_of_nonneg_left _ κ.b_pos.le
          linarith
  · push Not at hy
    set x' := max (min x Sb) (-Sb) with hx'
    have hu : 0 ≤ u0 π := NNReal.coe_nonneg _
    have hx'1 : x' ≤ x + u0 π := max_le ((min_le_left _ _).trans (by linarith)) hy
    have hx'2 : |x'| ≤ Sb := by
      rw [abs_le]
      exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
    have hc : ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i
          ∂pathLaw μ =
        ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) *
          ssCost κ L₀ (shiftPol π (x + u0 π - x').toNNReal) r x' d i ∂pathLaw μ := by
      simp only [shift_cost κ L₀ π r x x' hx'1]
    rw [hc]
    refine (hin x' hx'2).trans ?_
    gcongr
    exact iInf_le (fun ρ : SSPolicy => ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) *
      ssCost κ L₀ ρ r x' d i ∂pathLaw μ) _

/-! ## Arithmetic -/

lemma arith1 (M m b E r α K : ℝ) (hm : 0 < m) (hmb : m ≤ b) (hbM : b ≤ M) (hE : 0 ≤ E)
    (hr0 : 0 ≤ r) (hrE : r ≤ E) (hα0 : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) :
    M * (r + E) * (α / (1 - α) ^ 2 + K * (1 - α)⁻¹) ≤
      b * (4 * K * (M / m) * (|r| + E) * ((1 - α) ^ 2)⁻¹ - K * r) := by
  rw [abs_of_nonneg hr0]
  set s := 1 - α with hs
  have hs0 : 0 < s := by linarith
  have hs1 : s ≤ 1 := by linarith
  set T := (s ^ 2)⁻¹ with hT
  have hss : s ^ 2 ≤ s := by nlinarith
  have hsT : s⁻¹ ≤ T := inv_anti₀ (by positivity) hss
  have hT1 : 1 ≤ T := by
    rw [hT]; exact one_le_inv₀ (by positivity) |>.2 (by nlinarith)
  have hb : 0 < b := lt_of_lt_of_le hm hmb
  have hM : 0 ≤ M := by linarith
  have hA : 0 ≤ r + E := by linarith
  have hbQ : M ≤ b * (M / m) := by
    rw [mul_div_assoc', le_div_iff₀ hm]
    nlinarith
  have hl : M * (r + E) * (α / s ^ 2 + K * s⁻¹) ≤ M * (r + E) * ((1 + K) * T) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM hA)
    rw [div_eq_mul_inv]
    have : K * s⁻¹ ≤ K * T := mul_le_mul_of_nonneg_left hsT (by linarith)
    nlinarith
  have hbr : b * (K * r) ≤ M * K * (r + E) * T := by
    have h1 : b * (K * r) ≤ M * (K * (r + E)) :=
      mul_le_mul hbM (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) (by positivity) hM
    have h2 : M * (K * (r + E)) ≤ M * (K * (r + E)) * T :=
      le_mul_of_one_le_right (by positivity) hT1
    nlinarith
  have hr2 : M * K * (r + E) * T * 4 ≤ 4 * K * (b * (M / m)) * (r + E) * T := by
    have : 0 ≤ K * (r + E) * T := by positivity
    nlinarith
  have hfin : M * (r + E) * ((1 + K) * T) ≤ 3 * (M * K * (r + E) * T) := by
    have : 0 ≤ M * (r + E) * T := by positivity
    nlinarith
  calc M * (r + E) * (α / s ^ 2 + K * s⁻¹) ≤ M * (r + E) * ((1 + K) * T) := hl
    _ ≤ 3 * (M * K * (r + E) * T) := hfin
    _ ≤ 4 * K * (b * (M / m)) * (r + E) * T - b * (K * r) := by linarith
    _ = b * (4 * K * (M / m) * (r + E) * T - K * r) := by ring

lemma arith2 (M m E r α K Lr : ℝ) (n : ℕ) (hm : 0 < m) (hmM : m ≤ M) (hE : 0 ≤ E)
    (hr0 : 0 ≤ r) (hrE : r ≤ E) (hα0 : 0 < α) (hα1 : α < 1) (hK : 1 ≤ K) (hL : 1 ≤ Lr) :
    (1 - α) * (M * (4 * K * (M / m) * (|r| + E) * ((1 - α) ^ 2)⁻¹ +
        4 * K * (M / m) * (|r| + E) * ((1 - α) ^ 2)⁻¹ + |r| + E) * (1 + Lr) *
        ((1 - α) ^ 2)⁻¹ * α ^ n) ≤
      64 * K * (M ^ 2 / m) * E * ((1 - α) ^ 3)⁻¹ * Lr * α ^ n := by
  rw [abs_of_nonneg hr0]
  set s := 1 - α with hs
  have hs0 : 0 < s := by linarith
  have hs1 : s ≤ 1 := by linarith
  set T := (s ^ 2)⁻¹ with hT
  have hsT : s ^ 2 * T = 1 := by rw [hT]; exact mul_inv_cancel₀ (by positivity)
  set Q := M / m with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ, le_div_iff₀ hm]; linarith
  have hM : 0 ≤ M := by linarith
  have hM2 : M ^ 2 / m = M * Q := by rw [hQ]; ring
  have h3 : (s ^ 3)⁻¹ = T * s⁻¹ := by rw [hT, pow_succ, mul_inv]
  set a := α ^ n with ha
  have ha0 : 0 ≤ a := pow_nonneg hα0.le n
  have hT0 : 0 ≤ T := by positivity
  have hKQ : 1 ≤ K * Q := one_le_mul_of_one_le_of_one_le hK hQ1
  have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
  have core : s * (8 * K * Q * (r + E) * T + (r + E)) * (1 + Lr) * s ≤ 64 * K * Q * E * Lr := by
    have e : s * (8 * K * Q * (r + E) * T + (r + E)) * (1 + Lr) * s =
        (8 * K * Q * (r + E) * (s ^ 2 * T) + s ^ 2 * (r + E)) * (1 + Lr) := by ring
    rw [e, hsT, mul_one]
    have h1 : 8 * K * Q * (r + E) + s ^ 2 * (r + E) ≤ 18 * (K * Q) * E := by
      have : s ^ 2 * (r + E) ≤ r + E := by nlinarith
      have : 8 * K * Q * (r + E) ≤ 16 * (K * Q) * E := by nlinarith
      nlinarith
    have h2 : 0 ≤ 8 * K * Q * (r + E) + s ^ 2 * (r + E) := by
      have : 0 ≤ K * Q := by linarith
      positivity
    calc (8 * K * Q * (r + E) + s ^ 2 * (r + E)) * (1 + Lr)
        ≤ 18 * (K * Q) * E * (2 * Lr) :=
          mul_le_mul h1 (by linarith) (by linarith) (by nlinarith)
      _ ≤ 64 * K * Q * E * Lr := by
          have : 0 ≤ K * Q * E * Lr := by
            have : 0 ≤ K * Q := by linarith
            have : 0 ≤ Lr := by linarith
            positivity
          nlinarith
  have core' : s * (8 * K * Q * (r + E) * T + (r + E)) * (1 + Lr) ≤ 64 * K * Q * E * Lr / s := by
    rw [le_div_iff₀ hs0]; exact core
  have hMaT : 0 ≤ M * a * T := by positivity
  calc s * (M * (4 * K * Q * (r + E) * T + 4 * K * Q * (r + E) * T + r + E) * (1 + Lr) * T * a)
      = (M * a * T) * (s * (8 * K * Q * (r + E) * T + (r + E)) * (1 + Lr)) := by ring
    _ ≤ (M * a * T) * (64 * K * Q * E * Lr / s) := mul_le_mul_of_nonneg_left core' hMaT
    _ = 64 * K * (M ^ 2 / m) * E * (s ^ 3)⁻¹ * Lr * a := by
        rw [hM2, h3]; ring

/-! ## Assembly from Lemma 2 and Lemma 4 (8) -/

theorem glue (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h2 : ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) * VnNegInf μ κ L₀ α (L - L₀) (rL P L₀ L χ)
      ≤ OPT μ κ L₀ L)
    (h41 : ∀ (r x : ℝ) (n : ℕ), 1 ≤ n →
      Vn μ κ L₀ α n r x ≤ Vinf μ κ L₀ α r x ∧
      Vinf μ κ L₀ α r x ≤ Vn μ κ L₀ α n r x +
        ENNReal.ofReal (max κ.b κ.h * (Sbar μ κ L₀ α r + |x| + |r| + μ.mean) *
          (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n))
    (h43 : ∀ r : ℝ,
      (∀ x : ℝ, Vinf μ κ L₀ α r x ≠ ⊤) ∧
      ConvexOn ℝ Set.univ (fun x => (Vinf μ κ L₀ α r x).toReal) ∧
      Monotone (fun x => Vinf μ κ L₀ α r x) ∧
      (VinfMinimizers μ κ L₀ α r).Nonempty ∧
      BddAbove (VinfMinimizers μ κ L₀ α r) ∧
      |Sinf μ κ L₀ α r| ≤ Sbar μ κ L₀ α r ∧
      ∀ x : ℝ, ∃ π : SSPolicy, IsStationaryMarkov π (baseStockRule (Sinf μ κ L₀ α r)) r x ∧
        ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ = Vinf μ κ L₀ α r x) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          Vinf μ κ L₀ α (rL P L₀ L χ) (Sinf μ κ L₀ α (rL P L₀ L χ))
      ≤ OPT μ κ L₀ L +
        ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) := by
  haveI := hw.isProb
  have hr0 : 0 ≤ rL P L₀ L χ := by
    have hpos : 0 < L - L₀ - 1 := by omega
    unfold rL
    apply integral_nonneg_of_ae
    filter_upwards [hw.nonneg] with ω hω
    show (0 : ℝ) ≤ chiN L₀ L χ ω 0
    rw [chiN, dif_pos hpos]
    exact hω.1 _
  have hrE : rL P L₀ L χ ≤ μ.mean := by
    have hq : 0 ≤ ∫ ω, qN L₀ L q ω 0 ∂P := by
      apply integral_nonneg_of_ae
      filter_upwards [hw.nonneg] with ω hω
      show (0 : ℝ) ≤ qN L₀ L q ω 0
      rw [qN, dif_pos (by omega)]
      exact hω.2 _
    have hm := hw.mean_eq
    have : rL P L₀ L χ = ∫ ω, chiN L₀ L χ ω 0 ∂P := rfl
    linarith
  set r := rL P L₀ L χ with hr_def
  set n := L - L₀ with hn_def
  have hn : 1 ≤ n := by omega
  have hE := mean_nonneg μ
  have hm : 0 < min κ.b κ.h := lt_min κ.b_pos κ.h_pos
  have hmM : min κ.b κ.h ≤ max κ.b κ.h := min_le_max
  have hM : 0 ≤ max κ.b κ.h := by linarith
  set Sb := Sbar μ κ L₀ α r with hSb_def
  have hSb : 0 ≤ Sb := by
    rw [hSb_def, Sbar]
    have : 0 ≤ max κ.b κ.h / min κ.b κ.h := div_nonneg hM hm.le
    have : 0 ≤ |r| + μ.mean := by positivity
    positivity
  obtain ⟨hfin, hconv, -, hne, hbdd, -, -⟩ := h43 r
  set S := Sinf μ κ L₀ α r with hS_def
  -- `S` is a minimizer of `V^∞_α(r, ·)`
  have hmin : ∀ x, Vinf μ κ L₀ α r S ≤ Vinf μ κ L₀ α r x := by
    have hcont : Continuous (fun x => (Vinf μ κ L₀ α r x).toReal) :=
      continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
    have hmm : (⨅ x', Vinf μ κ L₀ α r x') ≠ ⊤ :=
      ne_top_of_le_ne_top (hfin 0) (iInf_le _ 0)
    have hset : VinfMinimizers μ κ L₀ α r =
        (fun x => (Vinf μ κ L₀ α r x).toReal) ⁻¹' {(⨅ x', Vinf μ κ L₀ α r x').toReal} := by
      ext x
      simp only [VinfMinimizers, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact (ENNReal.toReal_eq_toReal_iff' (hfin x) hmm).symm
    have hcl : IsClosed (VinfMinimizers μ κ L₀ α r) := by
      rw [hset]; exact isClosed_singleton.preimage hcont
    have hSmem : S ∈ VinfMinimizers μ κ L₀ α r := hcl.csSup_mem hne hbdd
    intro x
    have hSeq : Vinf μ κ L₀ α r S = ⨅ x', Vinf μ κ L₀ α r x' := hSmem
    rw [hSeq]
    exact iInf_le _ x
  -- a crude bound on `V^∞_α(r, S)` from the zero policy
  have hV : Vinf μ κ L₀ α r S ≤ ENNReal.ofReal (κ.b * (Sb - ((L₀ : ℝ) + 1) * r)) := by
    calc Vinf μ κ L₀ α r S ≤ Vinf μ κ L₀ α r 0 := hmin 0
      _ ≤ ∫⁻ d, ssDiscCost κ L₀ α zeroPol r 0 d ∂pathLaw μ :=
          iInf_le (fun π => ∫⁻ d, ssDiscCost κ L₀ α π r 0 d ∂pathLaw μ) zeroPol
      _ ≤ ENNReal.ofReal (max κ.b κ.h * (r + μ.mean) *
            (α / (1 - α) ^ 2 + ((L₀ : ℝ) + 1) * (1 - α)⁻¹)) :=
          zero_disc_le μ κ L₀ α r hα0 hα1 hr0
      _ ≤ ENNReal.ofReal (κ.b * (Sb - ((L₀ : ℝ) + 1) * r)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hSb_def, Sbar]
          exact arith1 _ _ _ _ _ _ _ hm (min_le_left _ _) (le_max_left _ _) hE hr0 hrE hα0 hα1
            (by have : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _; linarith)
  set Emax := max κ.b κ.h * (Sb + Sb + |r| + μ.mean) * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n
    with hEmax
  have hin : ∀ x' : ℝ, |x'| ≤ Sb →
      Vinf μ κ L₀ α r S ≤ Vn μ κ L₀ α n r x' + ENNReal.ofReal Emax := by
    intro x' hx'
    refine (hmin x').trans ((h41 r x' n hn).2.trans ?_)
    gcongr
    have hk : 0 ≤ max κ.b κ.h * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n := by
      have : 0 ≤ α ^ n := pow_nonneg hα0.le n
      have : (0 : ℝ) ≤ 1 + L₀ + n := by positivity
      have : 0 ≤ ((1 - α) ^ 2)⁻¹ := by positivity
      positivity
    calc max κ.b κ.h * (Sbar μ κ L₀ α r + |x'| + |r| + μ.mean) * (1 + L₀ + n) *
          ((1 - α) ^ 2)⁻¹ * α ^ n
        = (Sb + |x'| + |r| + μ.mean) *
            (max κ.b κ.h * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n) := by rw [hSb_def]; ring
      _ ≤ (Sb + Sb + |r| + μ.mean) *
            (max κ.b κ.h * (1 + L₀ + n) * ((1 - α) ^ 2)⁻¹ * α ^ n) :=
          mul_le_mul_of_nonneg_right (by linarith) hk
      _ = Emax := by rw [hEmax]; ring
  have hneg : Vinf μ κ L₀ α r S ≤ VnNegInf μ κ L₀ α n r + ENNReal.ofReal Emax := by
    unfold VnNegInf
    rw [ENNReal.iInf_add]
    exact le_iInf fun x => key μ κ L₀ α r n hn hr0 Sb Emax hSb _ hin hV x
  have hα1' : 0 ≤ 1 - α := by linarith
  have harith : (1 - α) * Emax ≤ U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀) := by
    have hcast : (1 + (L₀ : ℝ) + (n : ℝ)) = 1 + (L : ℝ) := by
      rw [hn_def, Nat.cast_sub (by omega)]; ring
    rw [hEmax, hcast, hSb_def, Sbar, U0]
    exact arith2 _ _ _ _ _ _ _ n hm hmM hE hr0 hrE hα0 hα1
      (by have : (0 : ℝ) ≤ L₀ := Nat.cast_nonneg _; linarith)
      (by have : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
          linarith)
  calc ENNReal.ofReal (κ.c * (μ.mean - r)) + ENNReal.ofReal (1 - α) * Vinf μ κ L₀ α r S
      ≤ ENNReal.ofReal (κ.c * (μ.mean - r)) +
          ENNReal.ofReal (1 - α) * (VnNegInf μ κ L₀ α n r + ENNReal.ofReal Emax) := by
        gcongr
    _ = (ENNReal.ofReal (κ.c * (μ.mean - r)) + ENNReal.ofReal (1 - α) * VnNegInf μ κ L₀ α n r) +
          ENNReal.ofReal ((1 - α) * Emax) := by
        rw [mul_add, ENNReal.ofReal_mul hα1', add_assoc]
    _ ≤ OPT μ κ L₀ L + ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) := by
        exact add_le_add h2 (ENNReal.ofReal_le_ofReal harith)

end XGL4

open MeasureTheory ProbabilityTheory Filter ENNReal NNReal XinGoldbergTBS.Asymptotic in
theorem solution (μ : DemandLaw) (κ : Costs) (L₀ L : ℕ) (hL : L₀ + 1 < L)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : Ω → Fin (L - L₀ - 1) → ℝ) (q : Ω → Fin (L - L₀) → ℝ) (I : Ω → ℝ) (D : ℕ → Ω → ℝ)
    (hw : IsStationaryWitness P μ κ L₀ L χ q I D)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ENNReal.ofReal (κ.c * (μ.mean - rL P L₀ L χ)) +
        ENNReal.ofReal (1 - α) *
          Vinf μ κ L₀ α (rL P L₀ L χ) (Sinf μ κ L₀ α (rL P L₀ L χ))
      ≤ OPT μ κ L₀ L +
        ENNReal.ofReal (U0 μ κ L₀ * ((1 - α) ^ 3)⁻¹ * L * α ^ (L - L₀)) := by
  have h4 := XinGoldbergTBS.Asymptotic.lemma4_bounds μ κ L₀ α hα0 hα1
  exact XGL4.glue μ κ L₀ L hL P χ q I D hw α hα0 hα1
    (XinGoldbergTBS.Asymptotic.lemma2 μ κ L₀ L hL P χ q I D hw α hα0 hα1) h4.1 h4.2.2
