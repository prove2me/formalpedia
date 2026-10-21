-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P54.scalar_entropy_estimates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T13:37:07.323525+00:00
-- url     : https://prove2.me/submissions/90ada147-462e-4723-bd29-b0f5c2137bd5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
open scoped ENNReal

namespace G59P

noncomputable def g (v : ℝ) : ℝ := (v + 1) * Real.log (v + 1) - v * Real.log v

lemma g_zero : g 0 = 0 := by simp [g]

lemma g_cont : ContinuousOn g (Set.Ici 0) := by
  have h1 : ContinuousOn (fun v : ℝ => (v + 1) * Real.log (v + 1)) (Set.Ici 0) := by
    apply ContinuousOn.mul (continuousOn_id.add continuousOn_const)
    apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
    intro x hx; have : (0:ℝ) ≤ x := hx; exact ne_of_gt (by simp; linarith)
  exact h1.sub Real.continuous_mul_log.continuousOn

lemma g_hasDeriv {v : ℝ} (hv : 0 < v) :
    HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
  have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
  have h2 := h1.mul (h1.log (by linarith))
  have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
  have := h2.sub h3
  refine this.congr_deriv ?_
  simp only [id, one_mul]
  field_simp
  ring

lemma g_strictMono : StrictMonoOn g (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) g_cont
  intro x hx
  rw [interior_Ici] at hx
  rw [(g_hasDeriv hx).deriv]
  have := Real.log_lt_log hx (by linarith : x < x + 1)
  linarith

lemma g_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ g v := by
  rw [← g_zero]; exact g_strictMono.monotoneOn (Set.mem_Ici.2 le_rfl) hv hv

lemma g_ge_log {v : ℝ} (hv : 0 ≤ v) : Real.log (v + 1) ≤ g v := by
  unfold g
  have hl : Real.log v ≤ Real.log (v + 1) := by
    rcases hv.eq_or_lt with h | h
    · subst h; simp
    · exact Real.log_le_log h (by linarith)
  nlinarith

/-- `k v = v log(1 + 1/v)` is monotone. -/
lemma k_mono : MonotoneOn (fun v : ℝ => v * (Real.log (v + 1) - Real.log v)) (Set.Ioi 0) := by
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt (fun v : ℝ => v * (Real.log (v + 1) - Real.log v))
      (Real.log (v + 1) - Real.log v - 1 / (v + 1)) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
    have := (hasDerivAt_id v).mul ((h1.log (by linarith)).sub (Real.hasDerivAt_log hv.ne'))
    refine this.congr_deriv ?_
    simp only [id, Pi.sub_apply]
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx0 : (0:ℝ) < x := hx
    rw [(hd x hx0).deriv]
    have := Real.one_sub_inv_le_log_of_pos (by positivity : (0:ℝ) < (x + 1) / x)
    rw [Real.log_div (by linarith) hx0.ne', inv_div] at this
    have e : 1 - x / (x + 1) = 1 / (x + 1) := by field_simp; ring
    linarith

/-- D c = g'(c), E c = g'(q c + q - 1). -/
noncomputable def Dg (c : ℝ) : ℝ := Real.log (c + 1) - Real.log c
noncomputable def Eg (q c : ℝ) : ℝ := Real.log (q * c + q) - Real.log (q * c + q - 1)

lemma Dg_pos {c : ℝ} (hc : 0 < c) : 0 < Dg c := by
  unfold Dg; have := Real.log_lt_log hc (by linarith : c < c + 1); linarith

lemma Eg_pos {q c : ℝ} (hq : 1 < q) (hc : 0 < c) : 0 < Eg q c := by
  unfold Eg
  have h1 : 0 < q * c + q - 1 := by nlinarith
  have := Real.log_lt_log h1 (by linarith : q * c + q - 1 < q * c + q); linarith

lemma ratio_mono {q : ℝ} (hq : 1 < q) :
    MonotoneOn (fun c => Eg q c / Dg c) (Set.Ioi 0) := by
  have hdD : ∀ c : ℝ, 0 < c → HasDerivAt Dg (1 / (c + 1) - 1 / c) c := by
    intro c hc
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 c := (hasDerivAt_id c).add_const 1
    have := (h1.log (by linarith)).sub (Real.hasDerivAt_log hc.ne')
    refine this.congr_deriv ?_
    simp
  have hdE : ∀ c : ℝ, 0 < c → HasDerivAt (Eg q) (1 / (c + 1) - q / (q * c + q - 1)) c := by
    intro c hc
    have h1 : 0 < q * c + q - 1 := by nlinarith
    have a1 : HasDerivAt (fun v : ℝ => q * v + q) q c := by
      simpa using ((hasDerivAt_id c).const_mul q).add_const q
    have a2 : HasDerivAt (fun v : ℝ => q * v + q - 1) q c := a1.sub_const 1
    have := (a1.log (by nlinarith)).sub (a2.log h1.ne')
    refine this.congr_deriv ?_
    field_simp
  have hdR : ∀ c : ℝ, 0 < c → HasDerivAt (fun c => Eg q c / Dg c)
      (((1 / (c + 1) - q / (q * c + q - 1)) * Dg c - Eg q c * (1 / (c + 1) - 1 / c)) / Dg c ^ 2) c :=
    fun c hc => (hdE c hc).div (hdD c hc) (Dg_pos hc).ne'
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hdR x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx; exact (hdR x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]; intro c hc
    have hc0 : (0:ℝ) < c := hc
    rw [(hdR c hc0).deriv]
    apply div_nonneg _ (sq_nonneg _)
    have h1 : 0 < q * c + q - 1 := by nlinarith
    have hk := k_mono (Set.mem_Ioi.2 hc0) (Set.mem_Ioi.2 h1) (by nlinarith)
    simp only at hk
    have hkE : (q * c + q - 1) * (Real.log (q * c + q - 1 + 1) - Real.log (q * c + q - 1)) =
        (q * c + q - 1) * Eg q c := by
      unfold Eg; ring_nf
    rw [hkE] at hk
    have hD := Dg_pos hc0
    have hE := Eg_pos hq hc0
    -- numerator = (c D - (qc+q-1) E)·(-1)/(c (c+1) (qc+q-1)) ... show directly
    have n1 : q * c + q - 1 ≠ 0 := h1.ne'
    have n2 : c + 1 ≠ 0 := by linarith
    have n3 : c ≠ 0 := hc0.ne'
    have e1 : 1 / (c + 1) - q / (q * c + q - 1) = -1 / ((c + 1) * (q * c + q - 1)) := by
      rw [div_sub_div _ _ n2 n1]; congr 1; ring
    have e2 : 1 / (c + 1) - 1 / c = -1 / (c * (c + 1)) := by
      rw [div_sub_div _ _ n2 n3, mul_comm (c + 1) c]; congr 1; ring
    rw [e1, e2]
    have : (-1 / ((c + 1) * (q * c + q - 1))) * Dg c - Eg q c * (-1 / (c * (c + 1))) =
        ((q * c + q - 1) * Eg q c - c * Dg c) / (c * (c + 1) * (q * c + q - 1)) := by
      generalize q * c + q - 1 = w at n1 ⊢
      field_simp
      ring
    rw [this]
    apply div_nonneg _ (by positivity)
    have : c * Dg c = c * (Real.log (c + 1) - Real.log c) := rfl
    linarith


/-- pointwise Gibbs: `-x log x ≤ x (-log y) + (y - x)` for `x ≥ 0`, `y > 0`. -/
lemma gibbs_pt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    -x * Real.log x ≤ x * (-Real.log y) + (y - x) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp; linarith
  · have := Real.log_le_sub_one_of_pos (div_pos hy h)
    rw [Real.log_div hy.ne' h.ne'] at this
    have h2 : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left this h.le
    have h3 : x * (y / x - 1) = y - x := by field_simp
    nlinarith

lemma maxent (p : PMF ℕ) (hp : QAlgorithms.Papers.Independent.Information100.P54.countMean p ≠ ⊤) :
    QAlgorithms.Papers.Independent.Information100.P54.shannonEntropy p ≤
      ENNReal.ofReal (QAlgorithms.Papers.Independent.Information100.P54.thermalEntropy
        (QAlgorithms.Papers.Independent.Information100.P54.countMean p).toReal) := by
  set N := (QAlgorithms.Papers.Independent.Information100.P54.countMean p).toReal with hN
  set P : ℕ → ℝ := fun m => (p m).toReal with hP
  have hP0 : ∀ m, 0 ≤ P m := fun m => ENNReal.toReal_nonneg
  have hPs : Summable P := ENNReal.summable_toReal (PMF.tsum_coe_ne_top p)
  have hP1 : ∑' m, P m = 1 := by
    rw [hP, ← ENNReal.tsum_toReal_eq (PMF.apply_ne_top p), PMF.tsum_coe]; rfl
  have hfin : ∀ m : ℕ, (m : ℝ≥0∞) * p m ≠ ⊤ :=
    fun m => ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (PMF.apply_ne_top p m)
  have hMs : Summable (fun m : ℕ => (m : ℝ) * P m) := by
    have := ENNReal.summable_toReal hp
    simpa [ENNReal.toReal_mul] using this
  have hM : ∑' m : ℕ, (m : ℝ) * P m = N := by
    rw [hN]; unfold QAlgorithms.Papers.Independent.Information100.P54.countMean
    rw [ENNReal.tsum_toReal_eq hfin]
    simp [ENNReal.toReal_mul, hP]
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold QAlgorithms.Papers.Independent.Information100.P54.shannonEntropy
  rcases hN0.eq_or_lt with h0 | hpos
  · -- zero mean: point mass at 0, entropy 0
    have hz : ∀ m, m ≠ 0 → P m = 0 := by
      intro m hm
      have hsum0 : ∑' k : ℕ, (k : ℝ) * P k = 0 := by rw [hM, ← h0]
      have hnn : ∀ k : ℕ, 0 ≤ (k : ℝ) * P k := fun k => mul_nonneg (Nat.cast_nonneg k) (hP0 k)
      have hle := hMs.le_tsum m (fun j _ => hnn j)
      rw [hsum0] at hle
      have hk : (m : ℝ) * P m = 0 := le_antisymm hle (hnn m)
      rcases mul_eq_zero.1 hk with h | h
      · exact absurd (by exact_mod_cast h) hm
      · exact h
    have hp0 : P 0 = 1 := by
      rw [← hP1, tsum_eq_single 0 (fun m hm => hz m hm)]
    have : ∀ m, ENNReal.ofReal (-(p m).toReal * Real.log (p m).toReal / Real.log 2) = 0 := by
      intro m
      show ENNReal.ofReal (-P m * Real.log (P m) / Real.log 2) = 0
      by_cases hm : m = 0
      · subst hm; rw [hp0]; simp
      · rw [hz m hm]; simp
    simp only [this, tsum_zero]
    exact zero_le
  · set r := N / (N + 1) with hr
    have hr0 : 0 < r := div_pos hpos (by linarith)
    have hr1 : r < 1 := by rw [hr, div_lt_one (by linarith)]; linarith
    set Q : ℕ → ℝ := fun m => (1 / (N + 1)) * r ^ m with hQ
    have hQs : Summable Q := (summable_geometric_of_lt_one hr0.le hr1).mul_left _
    have hQ1 : ∑' m, Q m = 1 := by
      rw [hQ, tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1, hr]
      field_simp
      ring
    have hQpos : ∀ m, 0 < Q m := fun m => by positivity
    set c := Real.log (N + 1) - Real.log N with hc
    have hlogQ : ∀ m : ℕ, -Real.log (Q m) = Real.log (N + 1) + m * c := by
      intro m
      rw [hQ, Real.log_mul (by positivity) (by positivity), Real.log_pow, hr,
        Real.log_div hpos.ne' (by linarith), one_div, Real.log_inv]
      ring
    set B : ℕ → ℝ := fun m => (P m * (Real.log (N + 1) + m * c) + (Q m - P m)) / Real.log 2 with hB
    have hterm : ∀ m, -(p m).toReal * Real.log (p m).toReal / Real.log 2 ≤ B m := by
      intro m
      show -P m * Real.log (P m) / Real.log 2 ≤ B m
      rw [hB]
      apply div_le_div_of_nonneg_right _ hl2.le
      have := gibbs_pt (hP0 m) (hQpos m)
      rw [hlogQ m] at this
      exact this
    have hB0 : ∀ m, 0 ≤ B m := by
      intro m
      refine le_trans ?_ (hterm m)
      apply div_nonneg _ hl2.le
      show 0 ≤ -P m * Real.log (P m)
      have h1 : P m ≤ 1 := by
        have := PMF.coe_le_one p m
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      have := Real.log_nonpos (hP0 m) h1
      nlinarith [hP0 m]
    have hBs : Summable B := by
      have := (((hPs.mul_right (Real.log (N + 1))).add (hMs.mul_right c)).add (hQs.sub hPs)).div_const
        (Real.log 2)
      refine this.congr (fun m => ?_)
      simp only [hB]; ring
    have hBsum : ∑' m, B m = G59P.g N / Real.log 2 := by
      have e : ∀ m, B m = (P m * Real.log (N + 1) + (m * P m) * c + (Q m - P m)) / Real.log 2 := by
        intro m; simp only [hB]; ring
      simp only [e]
      rw [tsum_div_const, ((hPs.mul_right _).add (hMs.mul_right _)).tsum_add (hQs.sub hPs),
        (hPs.mul_right _).tsum_add (hMs.mul_right _), tsum_mul_right, tsum_mul_right,
        hQs.tsum_sub hPs, hP1, hM, hQ1]
      unfold G59P.g
      rw [hc]
      ring
    calc ∑' m, ENNReal.ofReal (-(p m).toReal * Real.log (p m).toReal / Real.log 2)
        ≤ ∑' m, ENNReal.ofReal (B m) :=
          ENNReal.tsum_le_tsum (fun m => ENNReal.ofReal_le_ofReal (hterm m))
      _ = ENNReal.ofReal (∑' m, B m) := (ENNReal.ofReal_tsum_of_nonneg hB0 hBs).symm
      _ = _ := by rw [hBsum]; rfl


lemma k_strict : StrictMonoOn (fun v : ℝ => v * (Real.log (v + 1) - Real.log v)) (Set.Ioi 0) := by
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt (fun v : ℝ => v * (Real.log (v + 1) - Real.log v))
      (Real.log (v + 1) - Real.log v - 1 / (v + 1)) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
    have := (hasDerivAt_id v).mul ((h1.log (by linarith)).sub (Real.hasDerivAt_log hv.ne'))
    refine this.congr_deriv ?_
    simp only [id, Pi.sub_apply]
    field_simp
    ring
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; intro x hx
    have hx0 : (0:ℝ) < x := hx
    rw [(hd x hx0).deriv]
    have hne : x / (x + 1) ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq (by linarith)] at h; linarith
    have := Real.log_lt_sub_one_of_pos (by positivity : (0:ℝ) < x / (x + 1)) hne
    rw [Real.log_div hx0.ne' (by linarith)] at this
    have e : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
    linarith

lemma g_ge_log' {v : ℝ} (hv : 0 ≤ v) : g v ≤ Real.log (v + 1) + 1 := by
  unfold g
  rcases hv.eq_or_lt with h | h
  · subst h; simp
  · have hl := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < (v + 1) / v)
    rw [Real.log_div (by linarith) h.ne'] at hl
    have : v * (Real.log (v + 1) - Real.log v) ≤ v * ((v + 1) / v - 1) := mul_le_mul_of_nonneg_left hl h.le
    have e : v * ((v + 1) / v - 1) = 1 := by field_simp; ring
    nlinarith

end G59P

open QAlgorithms.Papers.Independent.Information100.P54
open Filter

lemma g59_te : ∀ v, thermalEntropy v = G59P.g v / Real.log 2 := fun v => rfl

lemma g59_loss_deriv {eta x : ℝ} (heta1 : eta < 1) (hx : 0 < x) :
    HasDerivAt (lossRate eta) ((G59P.Dg x - (1 - eta) * G59P.Dg ((1 - eta) * x)) / Real.log 2) x := by
  have ht : 0 < 1 - eta := by linarith
  have a : HasDerivAt (fun y : ℝ => (1 - eta) * y) (1 - eta) x := by
    simpa using (hasDerivAt_id x).const_mul (1 - eta)
  have h2 := (G59P.g_hasDeriv (mul_pos ht hx)).comp x a
  have h1 := G59P.g_hasDeriv hx
  have := (h1.sub h2).div_const (Real.log 2)
  have hf : lossRate eta = fun y => (G59P.g y - G59P.g ((1 - eta) * y)) / Real.log 2 := by
    funext y; unfold lossRate; rw [g59_te, g59_te]; ring
  rw [hf]
  refine this.congr_deriv ?_
  unfold G59P.Dg; ring

theorem solution (eta : ℝ) (heta0 : 0 < eta) (heta1 : eta < 1) :
    (∀ p : PMF ℕ, countMean p ≠ ⊤ →
      shannonEntropy p ≤ ENNReal.ofReal (thermalEntropy (countMean p).toReal)) ∧
    StrictMonoOn (lossRate eta) (Set.Ici 0) ∧
    ConcaveOn ℝ (Set.Ici 0) (lossRate eta) ∧
    (∀ a : ℝ, 0 ≤ a →
      Tendsto (fun r : ℝ => thermalEntropy (r * a) / r) atTop (nhds 0)) := by
  have ht : 0 < 1 - eta := by linarith
  have ht1 : 1 - eta < 1 := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousOn (lossRate eta) (Set.Ici 0) := by
    have hf : lossRate eta = fun y => (G59P.g y - G59P.g ((1 - eta) * y)) / Real.log 2 := by
      funext y; unfold lossRate; rw [g59_te, g59_te]; ring
    rw [hf]
    apply ContinuousOn.div_const
    apply G59P.g_cont.sub
    apply G59P.g_cont.comp (by fun_prop)
    intro y hy; simp only [Set.mem_Ici] at hy ⊢; positivity
  refine ⟨fun p hp => G59P.maxent p hp, ?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0) hcont
    rw [interior_Ici]; intro x hx
    have hx0 : (0:ℝ) < x := hx
    rw [(g59_loss_deriv heta1 hx0).deriv]
    apply div_pos _ hl2
    have hk := G59P.k_strict (Set.mem_Ioi.2 (mul_pos ht hx0)) (Set.mem_Ioi.2 hx0)
      (by nlinarith)
    simp only at hk
    have e1 : (1 - eta) * x * (Real.log ((1 - eta) * x + 1) - Real.log ((1 - eta) * x)) =
        x * ((1 - eta) * G59P.Dg ((1 - eta) * x)) := by unfold G59P.Dg; ring
    have e2 : x * (Real.log (x + 1) - Real.log x) = x * G59P.Dg x := by unfold G59P.Dg; ring
    rw [e1, e2] at hk
    have := lt_of_mul_lt_mul_left hk hx0.le
    linarith
  · apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hcont
    · rw [interior_Ici]; intro x hx
      exact (g59_loss_deriv heta1 hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      set t := 1 - eta with htd
      have hD : ∀ c : ℝ, 0 < c → HasDerivAt G59P.Dg (1 / (c + 1) - 1 / c) c := by
        intro c hc
        have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 c := (hasDerivAt_id c).add_const 1
        have := (h1.log (by linarith)).sub (Real.hasDerivAt_log hc.ne')
        refine this.congr_deriv ?_
        simp
      have hφ : ∀ x : ℝ, 0 < x → HasDerivAt (fun y => (G59P.Dg y - t * G59P.Dg (t * y)) / Real.log 2)
          (((1 / (x + 1) - 1 / x) - t * ((1 / (t * x + 1) - 1 / (t * x)) * t)) / Real.log 2) x := by
        intro x hx
        have a : HasDerivAt (fun y : ℝ => t * y) t x := by
          simpa using (hasDerivAt_id x).const_mul t
        have := ((hD x hx).sub (((hD (t * x) (mul_pos ht hx)).comp x a).const_mul t)).div_const
          (Real.log 2)
        exact this
      have hanti : AntitoneOn (fun y => (G59P.Dg y - t * G59P.Dg (t * y)) / Real.log 2) (Set.Ioi 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
        · intro x hx; exact (hφ x hx).continuousAt.continuousWithinAt
        · rw [interior_Ioi]; intro x hx; exact (hφ x hx).differentiableAt.differentiableWithinAt
        · rw [interior_Ioi]; intro x hx
          have hx0 : (0:ℝ) < x := hx
          rw [(hφ x hx0).deriv]
          apply div_nonpos_of_nonpos_of_nonneg _ hl2.le
          have n1 : x + 1 ≠ 0 := by linarith
          have n2 : t * x + 1 ≠ 0 := by nlinarith
          have n3 : x ≠ 0 := hx0.ne'
          have n4 : t ≠ 0 := ht.ne'
          have e : (1 / (x + 1) - 1 / x) - t * ((1 / (t * x + 1) - 1 / (t * x)) * t) =
              (t - 1) / (x * (x + 1) * (t * x + 1)) := by
            field_simp; ring
          rw [e]
          apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      intro a ha b hb hab
      rw [(g59_loss_deriv heta1 ha).deriv, (g59_loss_deriv heta1 hb).deriv]
      exact hanti ha hb hab
  · intro a ha
    have hlim : Tendsto (fun r : ℝ => (Real.log r + (Real.log (a + 1) + 1)) / r / Real.log 2)
        atTop (nhds 0) := by
      have h1 : Tendsto (fun r : ℝ => Real.log r / r) atTop (nhds 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h2 : Tendsto (fun r : ℝ => (Real.log (a + 1) + 1) / r) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have := (h1.add h2).div_const (Real.log 2)
      simp only [zero_add, zero_div] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with r hr
      ring
    apply squeeze_zero' _ _ hlim
    · filter_upwards [eventually_gt_atTop 0] with r hr
      rw [g59_te]
      exact div_nonneg (div_nonneg (G59P.g_nonneg (by positivity)) hl2.le) hr.le
    · filter_upwards [eventually_ge_atTop 1] with r hr
      have hr0 : 0 < r := by linarith
      rw [g59_te]
      have hb := G59P.g_ge_log' (by positivity : 0 ≤ r * a)
      have hl : Real.log (r * a + 1) ≤ Real.log r + Real.log (a + 1) := by
        rw [← Real.log_mul hr0.ne' (by linarith)]
        exact Real.log_le_log (by positivity) (by nlinarith)
      rw [div_div, div_div, mul_comm (Real.log 2) r]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
