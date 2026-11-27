-- Prove2me | solution 1 for PositivityTheory.RgJS.dirichlet_series_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:39.941827+00:00
-- url     : https://prove2.me/submissions/9577d500-e0b1-4d40-8429-99e472e12f2f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded
import Theorems.Thm_P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__cc_nonneg_31edcbb41409
import Theorems.Thm_P2M_PositivityTheory_RgJS_DirichletSeriesUnbounded__sum_lterm_af7624365c87

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PositivityTheory PositivityTheory.RgJS
open DirichletSeriesUnbounded₂
namespace PositivityTheory.RgJS
theorem _root_.solution : LandauL → NewtonLow → EulerLog → Remov → Conv1 → Unb := by
  intro hL hN hE hR hC W q X d A hS ι _ _ x hMex
  obtain ⟨M, hM⟩ := hMex
  classical
  set c : W × ℕ → ℝ := cc A x with hc
  set l : W × ℕ → ℝ := ll q with hl
  have hq : ∀ w, (0 : ℝ) < q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 0 < q w)
  have hq1 : ∀ w, (1 : ℝ) ≤ q w := fun w => by
    have := hS.primes.two w
    exact_mod_cast (by omega : 1 ≤ q w)
  have hc0 : ∀ p, 0 ≤ c p := fun p => cc_nonneg A x p
  have hl0 : ∀ p, 0 ≤ l p := fun p => mul_nonneg (by positivity) (Real.log_nonneg (hq1 p.1))
  have hpt : ∀ (σ : ℝ) p, ∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p = ((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) :=
    fun σ p => sum_lterm q A x hq σ p
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun p => c p * Real.exp (-(l p * σ)) := by
    intro σ hσ
    have h1 : ∀ i j, Summable fun p => ‖lterm q (A (x i)) (A (x j)) σ p‖ := fun i j =>
      (hC W q X d A hS (x i) (x j)).1 σ hσ
    refine Summable.of_nonneg_of_le (fun p => mul_nonneg (hc0 p) (Real.exp_pos _).le) (fun p => ?_)
      (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ => h1 i j)
    calc c p * Real.exp (-(l p * σ)) = ‖((c p * Real.exp (-(l p * σ)) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hc0 p) (Real.exp_pos _).le)]
      _ = ‖∑ i, ∑ j, lterm q (A (x i)) (A (x j)) σ p‖ := by rw [hpt σ p]
      _ ≤ ∑ i, ∑ j, ‖lterm q (A (x i)) (A (x j)) σ p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
  have htsum : ∀ σ : ℝ, 1 < σ → ∑ i, ∑ j, ∑' p, lterm q (A (x i)) (A (x j)) σ p =
      ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) := by
    intro σ hσ
    have hs : ∀ i j, Summable fun p => lterm q (A (x i)) (A (x j)) σ p := fun i j =>
      ((hC W q X d A hS (x i) (x j)).1 σ hσ).of_norm
    rw [Complex.ofReal_tsum]
    simp_rw [← hpt σ]
    rw [Summable.tsum_finsetSum (fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  have hT : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∑' p, c p * Real.exp (-(l p * σ)) ≤ M := by
    intro σ h1 h2
    have := hM σ h1 h2
    rw [htsum σ h1, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  choose F σ0 hFa hFe using fun ij : ι × ι => hS.rs (x ij.1) (x ij.2)
  set G : ℂ → ℂ := fun s => ∏ ij : ι × ι, F ij s with hG
  have hGa : ∀ σ : ℝ, 0 < σ → AnalyticAt ℂ G σ := fun σ hσ => by
    have := Finset.analyticAt_prod (𝕜 := ℂ) (f := F) (c := (σ : ℂ)) Finset.univ (fun ij _ => hFa ij σ hσ)
    have e : G = ∏ ij ∈ Finset.univ, F ij := by
      funext s
      simp [hG, Finset.prod_apply]
    rw [e]
    exact this
  set B : ℝ := 2 + ∑ ij, |σ0 ij| with hBd
  have hB : ∀ ij, σ0 ij ≤ B := fun ij => by
    have := Finset.single_le_sum (f := fun ij => |σ0 ij|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)
    have := le_abs_self (σ0 ij)
    linarith
  have hB2 : (2 : ℝ) ≤ B := by
    have := Finset.sum_nonneg (s := Finset.univ) (f := fun ij : ι × ι => |σ0 ij|) (fun _ _ => abs_nonneg _)
    linarith
  set r : ℕ := (Finset.univ.filter fun ij : ι × ι => x ij.1 = x ij.2).card with hr
  set SC : ℂ → ℂ := fun s => ∑' p, (c p : ℂ) * Complex.exp (-((l p : ℂ) * s)) with hSCd
  have hSC : ∀ σ : ℝ, SC σ = ((∑' p, c p * Real.exp (-(l p * σ)) : ℝ) : ℂ) := by
    intro σ
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun p => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hSCa : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ SC σ := by
    intro σ hσ
    set σ' : ℝ := (1 + σ) / 2 with hσ'
    have hU : IsOpen {s : ℂ | σ' < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ SC {s : ℂ | σ' < s.re} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hsum σ' (by linarith)) (fun p => ?_) hU (fun p s hs => ?_)
      · exact (Differentiable.differentiableOn (by fun_prop))
      · rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (hc0 p)]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hc0 p)
        have hs' : σ' < s.re := hs
        simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith [hl0 p]
    exact hd.analyticAt (hU.mem_nhds (by simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith))
  have hEq : ∀ σ : ℝ, B < σ → G σ = ((σ : ℂ) - 1) ^ r * Complex.exp (SC σ) := by
    intro σ hσ
    have h2 : (2 : ℝ) < σ := by linarith
    have e0 : G σ = ∏ ij : ι × ι, ((if x ij.1 = x ij.2 then (σ : ℂ) - 1 else 1) *
        eul q (A (x ij.1)) (A (x ij.2)) σ) :=
      Finset.prod_congr rfl fun ij _ => hFe ij σ (lt_of_le_of_lt (hB ij) hσ)
    rw [e0, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    · rw [hSC σ, ← htsum σ (by linarith), ← Fintype.sum_prod_type', Complex.exp_sum]
      refine Finset.prod_congr rfl fun ij _ => ?_
      exact (hE W q (Fin (d (x ij.1))) (Fin (d (x ij.2))) (A (x ij.1)) (A (x ij.2)) σ hS.primes (hS.bd _) (hS.bd _)
        (by simpa using h2)).2.1
  have ha1 : AnalyticOnNhd ℝ (fun t : ℝ => G t) (Set.Ioi 1) := fun t ht => by
    have h1 : AnalyticAt ℝ G (t : ℂ) := (hGa t (by linarith [Set.mem_Ioi.1 ht])).restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have ha2 : AnalyticOnNhd ℝ (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1) := fun t ht => by
    have h : AnalyticAt ℂ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ) :=
      ((analyticAt_id.sub analyticAt_const).pow r).mul (hSCa t (Set.mem_Ioi.1 ht)).cexp
    have h1 : AnalyticAt ℝ (fun s => (s - 1) ^ r * Complex.exp (SC s)) (t : ℂ) := h.restrictScalars
    exact h1.comp (Complex.ofRealCLM.analyticAt t)
  have hid : Set.EqOn (fun t : ℝ => G t) (fun t : ℝ => ((t : ℂ) - 1) ^ r * Complex.exp (SC t)) (Set.Ioi 1) :=
    ha1.eqOn_of_preconnected_of_eventuallyEq ha2 isPreconnected_Ioi (z₀ := B + 1)
      (Set.mem_Ioi.2 (by linarith)) (by
        filter_upwards [Ioi_mem_nhds (show B < B + 1 by linarith)] with t ht
        exact hEq t ht)
  have hGb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖G σ‖ ≤ Real.exp M * (σ - 1) ^ r := by
    intro σ h1 h2
    have e := hid (Set.mem_Ioi.2 h1)
    simp only at e
    have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [e, norm_mul, norm_pow, hn, hSC, Complex.norm_exp_ofReal, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hT σ h1 h2)) (pow_nonneg (by linarith) _)
  obtain ⟨G', hG'a, hG'e⟩ := hR G r (Real.exp M) hGa hGb
  have hG'v : ∀ σ : ℝ, 1 < σ → G' σ = ((Real.exp (∑' p, c p * Real.exp (-(l p * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have e1 := hid (Set.mem_Ioi.2 hσ)
    simp only at e1
    have e2 := hG'e σ hσ
    have hne : ((σ : ℂ) - 1) ^ r ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (by exact_mod_cast hσ.ne'))
    rw [e1] at e2
    have e3 := mul_left_cancel₀ hne e2
    rw [← e3, hSC, Complex.ofReal_exp]
  have hLand := hL (W × ℕ) c l 0 1 G' hc0 hl0 (fun σ hσ => hG'a σ hσ) hsum (fun σ hσ => hG'v σ hσ)
  set N : ℕ := ∑ i, d (x i) with hNd
  have hN1 : 1 ≤ N := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact le_trans (hS.pos (x i)) (Finset.single_le_sum (f := fun i => d (x i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs0 := hLand (1 / N) (by positivity)
  obtain ⟨c0, hc0pos, hc0le⟩ := hN N hN1
  have hlow : ∀ w, c0 / N * (q w : ℝ)⁻¹ ≤ ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N))) := by
    intro w
    have hnew := hc0le (Σ i : ι, Fin (d (x i))) (fun ib => A (x ib.1) w ib.2)
      (by rw [Fintype.card_sigma]; simp [hNd]) (by
        rw [Fintype.prod_sigma, norm_prod]
        exact Finset.prod_eq_one fun i _ => hS.det (x i) w)
    have hPk : ∀ k, (∑ ib : Σ i : ι, Fin (d (x i)), A (x ib.1) w ib.2 ^ (k + 1)) = PP A x (w, k) := fun k => by
      rw [Fintype.sum_sigma]; rfl
    simp only [hPk] at hnew
    have hterm : ∀ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ ≤ c (w, k) * Real.exp (-(l (w, k) * (1 / N))) := by
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.1 hk
      have hlog : 0 ≤ Real.log (q w) := Real.log_nonneg (hq1 w)
      have he : (q w : ℝ)⁻¹ ≤ Real.exp (-(l (w, k) * (1 / N))) := by
        rw [← Real.exp_log (hq w), ← Real.exp_neg]
        refine Real.exp_le_exp.2 (neg_le_neg ?_)
        simp only [hl, ll]
        calc ((k : ℝ) + 1) * Real.log (q w) * (1 / N) = ((k + 1) / N) * Real.log (q w) := by ring
          _ ≤ 1 * Real.log (q w) := mul_le_mul_of_nonneg_right ((div_le_one hNpos).2 hk') hlog
          _ = Real.log (q w) := one_mul _
      have hc' : ‖PP A x (w, k)‖ ^ 2 / N ≤ c (w, k) := by
        simp only [hc, cc]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk'
      exact mul_le_mul hc' he (by positivity) (hc0 _)
    calc c0 / N * (q w : ℝ)⁻¹ ≤ (∑ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2) / N * (q w : ℝ)⁻¹ := by
          gcongr
      _ = ∑ k ∈ Finset.range N, ‖PP A x (w, k)‖ ^ 2 / N * (q w : ℝ)⁻¹ := by
          rw [Finset.sum_div, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum hterm
  have hsw : Summable fun w => ∑ k ∈ Finset.range N, c (w, k) * Real.exp (-(l (w, k) * (1 / N))) :=
    summable_sum (s := Finset.range N) fun k _ => hs0.comp_injective (fun a b h => (Prod.mk.inj h).1)
  have h2 : Summable fun w => c0 / N * (q w : ℝ)⁻¹ :=
    Summable.of_nonneg_of_le (fun w => by have := hq w; positivity) hlow hsw
  have h3 : Summable fun w => (q w : ℝ)⁻¹ := by
    have := h2.mul_left (N / c0)
    refine this.congr fun w => ?_
    field_simp
  exact hS.primes.div h3
end PositivityTheory.RgJS
