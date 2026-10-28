-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.proposition_5_4_existence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:47:06.091877+00:00
-- url     : https://prove2.me/submissions/cfe5c0c6-dbb5-4b36-856b-d214ad373205

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate


open MeasureTheory Set Filter Topology

namespace S46PE
open SmoothAmbEq.Gaussian

lemma zinv (M : Model) (t : ℝ) :
    (M.ζ t)⁻¹ = (M.σ ^ 2 + t * M.σ₀ ^ 2) / (M.σ ^ 2 * M.σ₀ ^ 2) := by
  simp [Model.ζ, inv_div]

lemma zinv_deriv (M : Model) (t : ℝ) :
    HasDerivAt (fun t => (M.ζ t)⁻¹) (1 / M.σ ^ 2) t := by
  have hσ := M.hσ.ne'; have hσ₀ := M.hσ₀.ne'
  simp_rw [zinv]
  have := ((hasDerivAt_id t).mul_const (M.σ₀ ^ 2)).const_add (M.σ ^ 2) |>.div_const
    (M.σ ^ 2 * M.σ₀ ^ 2)
  simp only [id] at this
  exact this.congr_deriv (by field_simp)

lemma zinv_pos (M : Model) {t : ℝ} (ht : 0 ≤ t) : 0 < (M.ζ t)⁻¹ := by
  rw [zinv]; have := M.hσ; have := M.hσ₀; positivity

lemma solA (M : Model) (hα : M.α ≠ 0) (p D p' D' : ℝ → ℝ)
    (hp : ∀ t ∈ Icc 0 M.T, HasDerivAt p (p' t) t) (hD : ∀ t ∈ Icc 0 M.T, HasDerivAt D (D' t) t)
    (hDpos : ∀ t ∈ Icc 0 M.T, 0 < D t)
    (hpe : ∀ t ∈ Icc 0 M.T, M.σ ^ 2 * p' t = (1 + p t) ^ 2 * (1 + M.α * p t) / D t)
    (hDe : ∀ t ∈ Icc 0 M.T, M.σ ^ 2 * D' t = 1 - M.α + M.α * (1 + p t) ^ 2)
    (hpT : p M.T = 0) (hDT : D M.T = (M.ζ M.T)⁻¹) :
    SolvesODE516 M (fun t => p t * (M.ζ t)⁻¹) (fun t => ((M.ζ t)⁻¹ - D t) / M.α) := by
  have hσ := M.hσ.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have : (M.ζ t)⁻¹ - M.α * (((M.ζ t)⁻¹ - D t) / M.α) = D t := by field_simp; ring
    rw [this]; exact hDpos t ht
  · intro t ht
    have hz : M.ζ t ≠ 0 := by
      have := zinv_pos M ht.1; intro h; rw [h] at this; simp at this
    have hDt := (hDpos t ht).ne'
    refine ((hp t ht).mul (zinv_deriv M t)).hasDerivWithinAt.congr_deriv ?_
    have e : p' t = (1 + p t) ^ 2 * (1 + M.α * p t) / D t / M.σ ^ 2 := by
      rw [← hpe t ht]; field_simp
    have hD' : (M.ζ t)⁻¹ - M.α * (((M.ζ t)⁻¹ - D t) / M.α) = D t := by field_simp; ring
    simp only [a₁]; rw [hD', e]
    field_simp
  · intro t ht
    have hz : M.ζ t ≠ 0 := by
      have := zinv_pos M ht.1; intro h; rw [h] at this; simp at this
    refine (((zinv_deriv M t).sub (hD t ht)).div_const M.α).hasDerivWithinAt.congr_deriv ?_
    have e : D' t = (1 - M.α + M.α * (1 + p t) ^ 2) / M.σ ^ 2 := by
      rw [← hDe t ht]; field_simp
    rw [e]; field_simp; ring
  · simp [hpT]
  · simp [hDT]

end S46PE


open MeasureTheory Set Filter Topology

namespace S46PE

lemma invB (f : ℝ → ℝ) (l r c Y₀ : ℝ) (hl : l < 0) (hY₀ : 0 ≤ Y₀) (hYr : Y₀ < r)
    (hf : ContinuousOn f (Ioo l r)) (hfpos : ∀ y ∈ Ioo l r, 0 < f y)
    (hG : c ≤ ∫ y in (0:ℝ)..Y₀, f y) :
    ∃ Yi : ℝ → ℝ, ∀ s ∈ Icc 0 c, Yi s ∈ Ioo l r ∧ 0 ≤ Yi s ∧ (s = 0 → Yi s = 0) ∧
      HasDerivAt Yi (f (Yi s))⁻¹ s := by
  set G : ℝ → ℝ := fun y => ∫ x in (0:ℝ)..y, f x with hGdef
  have h0 : (0:ℝ) ∈ Ioo l r := ⟨hl, hY₀.trans_lt hYr⟩
  have hGd : ∀ y ∈ Ioo l r, HasDerivAt G (f y) y := by
    intro y hy
    have hsub : uIcc 0 y ⊆ Ioo l r := (Set.ordConnected_Ioo).uIcc_subset h0 hy
    exact intervalIntegral.integral_hasDerivAt_right ((hf.mono hsub).intervalIntegrable)
      (hf.stronglyMeasurableAtFilter isOpen_Ioo y hy) (hf.continuousAt (Ioo_mem_nhds hy.1 hy.2))
  have hGc : ContinuousOn G (Ioo l r) := fun y hy => (hGd y hy).continuousAt.continuousWithinAt
  have hGm : StrictMonoOn G (Ioo l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo l r) hGc
    intro y hy
    rw [interior_Ioo] at hy
    rw [(hGd y hy).deriv]; exact hfpos y hy
  set l' := l / 2
  set r' := (Y₀ + r) / 2
  have hl' : l < l' ∧ l' < 0 := by constructor <;> simp [l'] <;> linarith
  have hr' : Y₀ < r' ∧ r' < r := by constructor <;> simp [r'] <;> linarith
  have hsub' : Ioo l' r' ⊆ Ioo l r := Ioo_subset_Ioo hl'.1.le hr'.2.le
  have hl'm : l' ∈ Ioo l r := ⟨hl'.1, by linarith⟩
  have hr'm : r' ∈ Ioo l r := ⟨by linarith, hr'.2⟩
  set U := Ioo (G l') (G r')
  have hsurj : ∀ s ∈ U, ∃ y ∈ Ioo l' r', G y = s := by
    intro s hs
    have := intermediate_value_Ioo (show l' ≤ r' by linarith)
      (hGc.mono (Icc_subset_Ioo hl'.1 hr'.2)) hs
    exact this
  set Yi := Function.invFunOn G (Ioo l' r')
  have hYi : ∀ s ∈ U, Yi s ∈ Ioo l' r' ∧ G (Yi s) = s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := hsurj s hs
    exact ⟨Function.invFunOn_mem ⟨y, hy, hys⟩, Function.invFunOn_eq ⟨y, hy, hys⟩⟩
  have hGinj : ∀ y ∈ Ioo l r, ∀ y' ∈ Ioo l r, G y = G y' → y = y' :=
    fun y hy y' hy' h => hGm.injOn hy hy' h
  have hYiG : ∀ y ∈ Ioo l' r', Yi (G y) = y := by
    intro y hy
    have hU : G y ∈ U := ⟨hGm hl'm (hsub' hy) hy.1, hGm (hsub' hy) hr'm hy.2⟩
    exact hGinj _ (hsub' (hYi _ hU).1) _ (hsub' hy) (hYi _ hU).2
  have hYim : StrictMonoOn Yi U := by
    intro s hs s' hs' hss'
    by_contra h
    push_neg at h
    have := hGm.monotoneOn (hsub' (hYi s' hs').1) (hsub' (hYi s hs).1) h
    rw [(hYi s hs).2, (hYi s' hs').2] at this
    linarith
  have hG0 : G 0 = 0 := by simp [G]
  have hUc : Icc 0 c ⊆ U := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have := hGm hl'm h0 hl'.2; rw [hG0] at this; linarith [hs.1]
    · have := hGm ⟨by linarith, by linarith⟩ hr'm hr'.1; linarith [hs.2]
  refine ⟨Yi, fun s hs => ?_⟩
  have hsU := hUc hs
  obtain ⟨hmem, heq⟩ := hYi s hsU
  have hnn : 0 ≤ Yi s := by
    by_contra h; push_neg at h
    have := hGm (hsub' hmem) h0 h
    rw [heq, hG0] at this; linarith [hs.1]
  refine ⟨hsub' hmem, hnn, fun h => ?_, ?_⟩
  · subst h; exact hGinj _ (hsub' hmem) _ h0 (by rw [heq, hG0])
  · have hUn : U ∈ 𝓝 s := Ioo_mem_nhds hsU.1 hsU.2
    have hcont : ContinuousAt Yi s := by
      apply hYim.continuousAt_of_image_mem_nhds hUn
      apply mem_of_superset (Ioo_mem_nhds hmem.1 hmem.2)
      intro y hy
      exact ⟨G y, ⟨hGm hl'm (hsub' hy) hy.1, hGm (hsub' hy) hr'm hy.2⟩, hYiG y hy⟩
    exact HasDerivAt.of_local_left_inverse hcont (hGd _ (hsub' hmem))
      (hfpos _ (hsub' hmem)).ne' (Filter.mem_of_superset hUn fun y hy => (hYi y hy).2)

end S46PE


open MeasureTheory Set Filter Topology

namespace S46PE
open SmoothAmbEq.Gaussian

/-- the Y-density `g(y) = e^{-y} (1+βy)^{1/β} / (1+βy)` -/
noncomputable def gfun (β y : ℝ) : ℝ := Real.exp (-y) * (1 + β * y) ^ (1 / β) / (1 + β * y)

lemma solC (M : Model) (hα : M.α ≠ 0) (hα1 : M.α ≠ 1) (Y : ℝ → ℝ)
    (hY : ∀ t ∈ Icc 0 M.T, HasDerivAt Y (-(M.ζ M.T) / M.σ ^ 2 * (gfun (1 - M.α) (Y t))⁻¹) t)
    (hY1 : ∀ t ∈ Icc 0 M.T, 0 < 1 + Y t) (hYb : ∀ t ∈ Icc 0 M.T, 0 < 1 + (1 - M.α) * Y t)
    (hYT : Y M.T = 0) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  set β := 1 - M.α with hβ
  have hβ0 : β ≠ 0 := by intro h; apply hα1; linarith
  have hαβ : M.α = 1 - β := by linarith
  set K := M.ζ M.T
  have hK : 0 < K := by have := zinv_pos M M.hT.le; exact inv_pos.mp this
  have hσ := M.hσ.ne'
  set Y' : ℝ → ℝ := fun t => -K / M.σ ^ 2 * (gfun β (Y t))⁻¹ with hY'
  have hP : ∀ t ∈ Icc 0 M.T, HasDerivAt (fun t => (1 + β * Y t) ^ (1 / β))
      (Y' t * ((1 + β * Y t) ^ (1 / β) / (1 + β * Y t))) t := by
    intro t ht
    have h1 := (((hY t ht).const_mul β).const_add 1).rpow_const (p := 1 / β)
      (Or.inl (hYb t ht).ne')
    refine h1.congr_deriv ?_
    rw [Real.rpow_sub_one (hYb t ht).ne']
    simp only [hY']
    field_simp
  have hE : ∀ t ∈ Icc 0 M.T, HasDerivAt (fun t => Real.exp (-Y t))
      (Real.exp (-Y t) * -Y' t) t := fun t ht => (hY t ht).neg.exp
  refine ⟨_, _, solA M hα (fun t => -Y t / (1 + Y t))
    (fun t => K⁻¹ * (Real.exp (-Y t) * (1 + β * Y t) ^ (1 / β)) / (1 + Y t))
    (fun t => -Y' t / (1 + Y t) ^ 2)
    (fun t => K⁻¹ * (Real.exp (-Y t) * (1 + β * Y t) ^ (1 / β)) * Y' t *
      ((-1 + 1 / (1 + β * Y t)) * (1 + Y t) - 1) / (1 + Y t) ^ 2)
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) ?_ ?_⟩
  · have h1 := hY1 t ht
    refine ((hY t ht).neg.div ((hY t ht).const_add 1) h1.ne').congr_deriv ?_
    simp only [Pi.neg_apply]
    simp only [hY']
    generalize (gfun β (Y t))⁻¹ = gi at *
    field_simp; ring
  · have h1 := hY1 t ht; have h2 := hYb t ht
    refine ((((hE t ht).mul (hP t ht)).const_mul K⁻¹).div ((hY t ht).const_add 1)
      h1.ne').congr_deriv ?_
    simp only [Pi.mul_apply]
    have hP0 : 0 < (1 + β * Y t) ^ (1 / β) := Real.rpow_pos_of_pos h2 _
    generalize Real.exp (-Y t) = E at *
    generalize (1 + β * Y t) ^ (1 / β) = P at *
    simp only [hY']
    generalize (gfun β (Y t))⁻¹ = gi at *
    field_simp; ring
  · have := hY1 t ht; have := hYb t ht; positivity
  · have h1 := hY1 t ht; have h2 := hYb t ht
    have hP0 : 0 < (1 + β * Y t) ^ (1 / β) := Real.rpow_pos_of_pos h2 _
    simp only [hY', gfun]; rw [hαβ]
    have hE0 := Real.exp_pos (-Y t)
    generalize Real.exp (-Y t) = E at *
    generalize (1 + β * Y t) ^ (1 / β) = P at *
    field_simp; ring
  · have h1 := hY1 t ht; have h2 := hYb t ht
    have hP0 : 0 < (1 + β * Y t) ^ (1 / β) := Real.rpow_pos_of_pos h2 _
    simp only [hY', gfun]; rw [hαβ]
    have hE0 := Real.exp_pos (-Y t)
    generalize Real.exp (-Y t) = E at *
    generalize (1 + β * Y t) ^ (1 / β) = P at *
    field_simp; ring
  · simp [hYT]
  · simp [hYT, K]

end S46PE


open MeasureTheory Set Filter Topology

namespace S46PE
open SmoothAmbEq.Gaussian

lemma gfun_contAt (β y : ℝ) (h : 0 < 1 + β * y) : ContinuousAt (gfun β) y := by
  unfold gfun
  have hc : ContinuousAt (fun y => 1 + β * y) y := by fun_prop
  exact ((Real.continuous_exp.continuousAt.comp (continuous_neg.continuousAt)).mul
    (hc.rpow_const (Or.inl h.ne'))).div hc h.ne'

lemma gfun_pos (β y : ℝ) (h : 0 < 1 + β * y) : 0 < gfun β y := by
  unfold gfun; have := Real.rpow_pos_of_pos h (1 / β); positivity

lemma solD (M : Model) (hα : M.α ≠ 0) (hα1 : M.α ≠ 1) (l r Y₀ : ℝ) (hl : l < 0) (hY₀ : 0 ≤ Y₀)
    (hYr : Y₀ < r) (hdom : ∀ y ∈ Ioo l r, 0 < 1 + y ∧ 0 < 1 + (1 - M.α) * y)
    (hG : M.ζ M.T * M.T / M.σ ^ 2 ≤ ∫ y in (0:ℝ)..Y₀, gfun (1 - M.α) y) :
    ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  obtain ⟨Yi, hYi⟩ := invB (gfun (1 - M.α)) l r _ Y₀ hl hY₀ hYr
    (fun y hy => (gfun_contAt _ _ (hdom y hy).2).continuousWithinAt)
    (fun y hy => gfun_pos _ _ (hdom y hy).2) hG
  set K := M.ζ M.T
  have hK : 0 < K := by have := zinv_pos M M.hT.le; exact inv_pos.mp this
  have hσ := M.hσ
  set τ : ℝ → ℝ := fun t => K * (M.T - t) / M.σ ^ 2
  have hτ : ∀ t ∈ Icc 0 M.T, τ t ∈ Icc 0 (K * M.T / M.σ ^ 2) := by
    intro t ht
    constructor
    · have := ht.2; simp only [τ]; apply div_nonneg _ (by positivity)
      apply mul_nonneg hK.le; linarith
    · simp only [τ]; gcongr; linarith [ht.1]
  apply solC M hα hα1 (fun t => Yi (τ t))
  · intro t ht
    have h1 := (hYi _ (hτ t ht)).2.2.2
    have h2 : HasDerivAt τ (-K / M.σ ^ 2) t := by
      have := ((hasDerivAt_id t).const_sub M.T).const_mul K |>.div_const (M.σ ^ 2)
      simp only [id] at this
      exact this.congr_deriv (by ring)
    exact (h1.comp t h2).congr_deriv (by ring)
  · intro t ht; exact (hdom _ (hYi _ (hτ t ht)).1).1
  · intro t ht; exact (hdom _ (hYi _ (hτ t ht)).1).2
  · have : τ M.T = 0 := by simp [τ]
    have hm : τ M.T ∈ Icc 0 (K * M.T / M.σ ^ 2) := hτ _ ⟨M.hT.le, le_rfl⟩
    exact (hYi _ hm).2.2.1 this

/-- case α > 1 -/
lemma sol_gt1 (M : Model) (hα : 1 < M.α) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  set γ := M.α - 1 with hγ
  have hγ0 : 0 < γ := by linarith
  have hβ : 1 - M.α = -γ := by ring
  set K := M.ζ M.T
  have hK : 0 < K := by have := zinv_pos M M.hT.le; exact inv_pos.mp this
  set c := K * M.T / M.σ ^ 2
  have hc : 0 ≤ c := by have := M.hT; have := M.hσ; positivity
  set r := 1 / γ
  set Kk := c * γ * Real.exp r
  set Y₀ := (1 - Real.exp (-Kk)) / γ
  have hKk : 0 ≤ Kk := by positivity
  have hY₀ : 0 ≤ Y₀ := by
    apply div_nonneg _ hγ0.le
    have : Real.exp (-Kk) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hYr : Y₀ < r := by
    simp only [Y₀, r]; apply div_lt_div_of_pos_right _ hγ0
    have := Real.exp_pos (-Kk); linarith
  have hb : ∀ y ∈ Icc (0:ℝ) Y₀, 0 < 1 - γ * y := by
    intro y hy
    have : γ * y < 1 := by
      have := mul_lt_mul_of_pos_left (hy.2.trans_lt hYr) hγ0
      simp only [r] at this; rw [mul_one_div_cancel hγ0.ne'] at this; exact this
    linarith
  have hY0b : 0 < 1 - γ * Y₀ := hb Y₀ ⟨hY₀, le_rfl⟩
  apply solD M (by linarith) (by linarith) (-1/2) r Y₀ (by norm_num) hY₀ hYr
  · intro y hy
    rw [hβ]
    refine ⟨by linarith [hy.1], ?_⟩
    rcases le_or_gt y 0 with h | h
    · nlinarith
    · have := mul_lt_mul_of_pos_left hy.2 hγ0
      simp only [r] at this; rw [mul_one_div_cancel hγ0.ne'] at this; linarith
  · rw [hβ]
    have hlow : ∀ y ∈ Icc (0:ℝ) Y₀, Real.exp (-r) * (1 - γ * y)⁻¹ ≤ gfun (-γ) y := by
      intro y hy
      have hby := hb y hy
      have hb' : 1 + -γ * y = 1 - γ * y := by ring
      unfold gfun; rw [hb']
      have h1 : 1 ≤ (1 - γ * y) ^ (1 / -γ) := by
        apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hby
        · nlinarith [hy.1]
        · rw [div_neg, one_div]; simp [hγ0.le]
      have h2 : Real.exp (-r) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith [hy.2])
      rw [div_eq_mul_inv]
      have := inv_pos.mpr hby
      calc Real.exp (-r) * (1 - γ * y)⁻¹ ≤ Real.exp (-y) * 1 * (1 - γ * y)⁻¹ := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right h2 this.le
        _ ≤ _ := by gcongr
    have hF : ∀ y ∈ uIcc (0:ℝ) Y₀, HasDerivAt (fun y => Real.exp (-r) * (-Real.log (1 - γ * y) / γ))
        (Real.exp (-r) * (1 - γ * y)⁻¹) y := by
      intro y hy
      rw [uIcc_of_le hY₀] at hy
      have := (((hasDerivAt_id y).const_mul γ).const_sub 1).log (hb y hy).ne'
      have := (this.neg.div_const γ).const_mul (Real.exp (-r))
      refine this.congr_deriv ?_
      simp only [id]; field_simp
    have hcont : ContinuousOn (fun y => Real.exp (-r) * (1 - γ * y)⁻¹) (uIcc 0 Y₀) := by
      rw [uIcc_of_le hY₀]
      intro y hy
      exact (continuousAt_const.mul ((continuousAt_const.sub (continuousAt_const.mul
        continuousAt_id)).inv₀ (hb y hy).ne')).continuousWithinAt
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable
    have hval : ∫ y in (0:ℝ)..Y₀, Real.exp (-r) * (1 - γ * y)⁻¹ = c := by
      rw [hint]
      have : 1 - γ * Y₀ = Real.exp (-Kk) := by simp only [Y₀]; field_simp; ring
      simp only [this, Real.log_exp, mul_zero, sub_zero, Real.log_one, neg_zero, zero_div]
      simp only [Kk]; field_simp
      rw [mul_comm, ← mul_assoc, ← Real.exp_add]; simp
    show c ≤ _
    rw [← hval]
    apply intervalIntegral.integral_mono_on hY₀ (hcont.intervalIntegrable.mono_set (by simp))
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hY₀]
      intro y hy
      apply (gfun_contAt _ _ _).continuousWithinAt
      have := hb y hy; linarith
    · exact hlow

end S46PE


open MeasureTheory Set Filter Topology

namespace S46PE
open SmoothAmbEq.Gaussian

lemma cmp_pt (a β y : ℝ) (ha : a < 0) (hβ : 0 < β) (hβs : β < 1 - a) (hy : 0 < y) :
    Real.exp (-y) * (1 + (1 - a) * y) ^ (a / (1 - a)) < gfun β y := by
  set s := 1 - a with hs
  have hs0 : 0 < s := by linarith
  have h1 : 1 < 1 + s * y := by nlinarith
  have h2 : 1 < 1 + β * y := by nlinarith
  set Ls := Real.log (1 + s * y)
  set Lb := Real.log (1 + β * y)
  have hconc := strictConcaveOn_log_Ioi.2 (show (1:ℝ) ∈ Ioi 0 by simp)
    (show 1 + s * y ∈ Ioi 0 by simp only [mem_Ioi]; linarith) (by linarith : (1:ℝ) ≠ 1 + s * y)
    (show 0 < 1 - β / s by rw [sub_pos, div_lt_one hs0]; exact hβs)
    (show 0 < β / s by positivity) (by ring : 1 - β / s + β / s = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
  have harg : (1 - β / s) * 1 + β / s * (1 + s * y) = 1 + β * y := by field_simp; ring
  rw [harg] at hconc
  have hq : Ls / s < Lb / β := by
    rw [div_lt_div_iff₀ hs0 hβ]; rw [div_mul_eq_mul_div, div_lt_iff₀ hs0] at hconc; linarith
  have hmono : Lb ≤ Ls := Real.log_le_log (by linarith) (by nlinarith)
  unfold gfun
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith)]
  have he : 1 + β * y = Real.exp Lb := (Real.exp_log (by linarith)).symm
  conv_rhs => rw [show (1 + β * y) = Real.exp Lb from he]
  rw [Real.log_exp, mul_div_assoc, ← Real.exp_sub]
  apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
  apply Real.exp_lt_exp.mpr
  have : a / s = 1 / s - 1 := by
    rw [eq_sub_iff_add_eq, div_add_one hs0.ne', hs]; congr 1; ring
  rw [this]
  have e1 : Ls * (1 / s - 1) = Ls / s - Ls := by ring
  have e2 : Lb * (1 / β) = Lb / β := by ring
  rw [e1, e2]; linarith

lemma ga_contAt (a y : ℝ) (h : 0 < 1 + (1 - a) * y) :
    ContinuousAt (fun y => Real.exp (-y) * (1 + (1 - a) * y) ^ (a / (1 - a))) y := by
  have hc : ContinuousAt (fun y => 1 + (1 - a) * y) y := by fun_prop
  exact (Real.continuous_exp.continuousAt.comp (continuous_neg.continuousAt)).mul
    (hc.rpow_const (Or.inl h.ne'))

/-- case α < 1, α ≠ 0 -/
lemma sol_lt1 (M : Model) (a : ℝ) (ha : IsAlphaStar M a) (hα : a < M.α) (h1 : M.α < 1)
    (h0 : M.α ≠ 0) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  obtain ⟨ha0, hI⟩ := ha
  set β := 1 - M.α with hβdef
  have hβ : 0 < β := by linarith
  have hβs : β < 1 - a := by linarith
  set ga : ℝ → ℝ := fun y => Real.exp (-y) * (1 + (1 - a) * y) ^ (a / (1 - a)) with hga
  set c := M.ζ M.T * M.T / M.σ ^ 2
  have hσ := M.hσ; have hσ₀ := M.hσ₀; have hT := M.hT
  have hcI : c * (1 + M.σ ^ 2 / (M.σ₀ ^ 2 * M.T)) = 1 := by
    simp only [c, Model.ζ]; field_simp; ring
  set I := ∫ x in Ioi (0:ℝ), ga x
  have hIc : I = c := by
    have hne : (1 + M.σ ^ 2 / (M.σ₀ ^ 2 * M.T)) ≠ 0 := by positivity
    have : (1 + M.σ ^ 2 / (M.σ₀ ^ 2 * M.T)) * I = (1 + M.σ ^ 2 / (M.σ₀ ^ 2 * M.T)) * c := by
      rw [hI, mul_comm, hcI]
    exact mul_left_cancel₀ hne this
  have hIne : I ≠ 0 := by intro h; rw [h] at hI; simp at hI
  have hint : IntegrableOn ga (Ioi 0) := Integrable.of_integral_ne_zero hIne
  have hlim : Tendsto (fun Y => ∫ x in (0:ℝ)..Y, ga x) atTop (𝓝 c) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
    rw [← hIc]; exact this
  have hpos1 : ∀ y, 0 ≤ y → 0 < 1 + (1 - a) * y := fun y hy => by nlinarith
  have hposb : ∀ y, 0 ≤ y → 0 < 1 + β * y := fun y hy => by nlinarith
  have hii : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → IntervalIntegrable ga volume u v ∧
      IntervalIntegrable (gfun β) volume u v := by
    intro u v hu hv
    have hsub : uIcc u v ⊆ Ici 0 := by
      intro x hx; rw [mem_uIcc] at hx; simp only [mem_Ici]
      rcases hx with h | h <;> linarith [h.1]
    constructor
    · exact ContinuousOn.intervalIntegrable fun x hx =>
        (ga_contAt a x (hpos1 x (hsub hx))).continuousWithinAt
    · exact ContinuousOn.intervalIntegrable fun x hx =>
        (gfun_contAt β x (hposb x (hsub hx))).continuousWithinAt
  set δ := ∫ y in (0:ℝ)..1, (gfun β y - ga y)
  have hδ : 0 < δ := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
    · exact ((hii 0 1 le_rfl zero_le_one).2).sub ((hii 0 1 le_rfl zero_le_one).1)
    · intro y hy; have := cmp_pt a β y ha0 hβ hβs hy.1; simp only [hga] at this ⊢; linarith
    · norm_num
  obtain ⟨Y₀, hY₀a, hY₀b⟩ := ((hlim.eventually (lt_mem_nhds (show c - δ < c by linarith))).and
    (eventually_ge_atTop 1)).exists
  have hY0 : (0:ℝ) ≤ Y₀ := by linarith
  have hG : c ≤ ∫ y in (0:ℝ)..Y₀, gfun β y := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals (hii 0 1 le_rfl zero_le_one).2
      (hii 1 Y₀ zero_le_one hY0).2
    have e2 := intervalIntegral.integral_add_adjacent_intervals (hii 0 1 le_rfl zero_le_one).1
      (hii 1 Y₀ zero_le_one hY0).1
    have e3 : δ = (∫ y in (0:ℝ)..1, gfun β y) - ∫ y in (0:ℝ)..1, ga y :=
      intervalIntegral.integral_sub (hii 0 1 le_rfl zero_le_one).2 (hii 0 1 le_rfl zero_le_one).1
    have e4 : ∫ y in (1:ℝ)..Y₀, ga y ≤ ∫ y in (1:ℝ)..Y₀, gfun β y :=
      intervalIntegral.integral_mono_on hY₀b (hii 1 Y₀ zero_le_one hY0).1
        (hii 1 Y₀ zero_le_one hY0).2 fun y hy =>
          (cmp_pt a β y ha0 hβ hβs (by linarith [hy.1])).le
    linarith
  set l := -1 / (2 * (1 + β))
  apply solD M h0 (by linarith) l (Y₀ + 1) Y₀ (by simp only [l]; apply div_neg_of_neg_of_pos <;> linarith)
    hY0 (by linarith) _ hG
  intro y hy
  have hl : -1 < 2 * (1 + β) * y := by
    have := hy.1; simp only [l] at this; rw [div_lt_iff₀ (by linarith)] at this; linarith
  rcases le_or_gt 0 y with h | h
  · exact ⟨by linarith, hposb y h⟩
  · constructor <;> nlinarith

end S46PE


open MeasureTheory Set Filter Topology

namespace S46PE
open SmoothAmbEq.Gaussian

lemma sol_eq1 (M : Model) (h1 : M.α = 1) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  set K := M.ζ M.T
  have hK : 0 < K := by have := zinv_pos M M.hT.le; exact inv_pos.mp this
  have hσ := M.hσ
  set τ : ℝ → ℝ := fun t => K * (M.T - t) / M.σ ^ 2
  have hτd : ∀ t, HasDerivAt τ (-K / M.σ ^ 2) t := by
    intro t
    have := ((hasDerivAt_id t).const_sub M.T).const_mul K |>.div_const (M.σ ^ 2)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hτ : ∀ t ∈ Icc 0 M.T, 0 < 1 + τ t := by
    intro t ht
    have : 0 ≤ τ t := by
      simp only [τ]; apply div_nonneg _ (by positivity); apply mul_nonneg hK.le; linarith [ht.2]
    linarith
  refine ⟨_, _, solA M (by rw [h1]; norm_num) (fun t => 1 / (1 + τ t) - 1)
    (fun t => K⁻¹ / (1 + τ t)) (fun t => K / M.σ ^ 2 / (1 + τ t) ^ 2)
    (fun t => 1 / M.σ ^ 2 / (1 + τ t) ^ 2)
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) ?_ ?_⟩
  · have h := hτ t ht
    refine ((((hτd t).const_add 1).inv h.ne').const_mul 1 |>.sub_const 1).congr_deriv ?_
    field_simp
  · have h := hτ t ht
    refine ((((hτd t).const_add 1).inv h.ne').const_mul K⁻¹).congr_deriv ?_
    field_simp
  · have := hτ t ht; positivity
  · have h := hτ t ht
    rw [h1]; field_simp; ring
  · have h := hτ t ht
    rw [h1]; field_simp; ring
  · simp [τ]
  · simp [τ, K]

end S46PE


open MeasureTheory Set Filter Topology

namespace S46PE
open SmoothAmbEq.Gaussian

lemma sol_eq0 (M : Model) (h0 : M.α = 0) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  have hσ := M.hσ; have hσ₀ := M.hσ₀; have hT := M.hT
  set Z : ℝ → ℝ := fun t => (M.ζ t)⁻¹ with hZ
  set ZT := Z M.T
  have hZp : ∀ t ∈ Icc 0 M.T, 0 < Z t := fun t ht => zinv_pos M ht.1
  have hZT : 0 < ZT := hZp _ ⟨hT.le, le_rfl⟩
  set Y : ℝ → ℝ := fun t => Real.log (ZT / Z t)
  have hYd : ∀ t ∈ Icc 0 M.T, HasDerivAt Y (-1 / (M.σ ^ 2 * Z t)) t := by
    intro t ht
    have hz := hZp t ht
    have h2 := (hasDerivAt_const t ZT).div (zinv_deriv M t) hz.ne'
    have := h2.log (by simp only [Pi.div_apply]; exact (div_pos hZT hz).ne')
    simp only [Pi.div_apply] at this
    refine this.congr_deriv ?_
    simp only [Z] at hz ⊢
    generalize (M.ζ t)⁻¹ = z at *
    field_simp; ring
  have hY0 : ∀ t ∈ Icc 0 M.T, 0 ≤ Y t := by
    intro t ht
    apply Real.log_nonneg
    rw [one_le_div (hZp t ht)]
    simp only [ZT, Z, zinv]
    gcongr; exact ht.2
  set p : ℝ → ℝ := fun t => -Y t / (1 + Y t)
  have hpd : ∀ t ∈ Icc 0 M.T, HasDerivAt p (1 / (M.σ ^ 2 * Z t) / (1 + Y t) ^ 2) t := by
    intro t ht
    have h1 : 0 < 1 + Y t := by linarith [hY0 t ht]
    refine ((hYd t ht).neg.div ((hYd t ht).const_add 1) h1.ne').congr_deriv ?_
    have hz := hZp t ht
    simp only [Pi.neg_apply]
    generalize Y t = y at *; generalize Z t = z at *
    field_simp; ring
  set F : ℝ → ℝ := fun s => (-2 * p s - p s ^ 2) / M.σ ^ 2
  have hFc : ContinuousOn F (Icc 0 M.T) := by
    intro t ht
    have := (hpd t ht).continuousAt
    exact (((continuousAt_const.mul this).sub (this.pow 2)).div_const _).continuousWithinAt
  set Fc : ℝ → ℝ := fun s => F (max 0 (min s M.T))
  have hFcc : Continuous Fc :=
    hFc.comp_continuous (by fun_prop) fun s => ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hFcF : ∀ t ∈ Icc 0 M.T, Fc t = F t := by
    intro t ht; simp only [Fc]; rw [min_eq_left ht.2, max_eq_right ht.1]
  have hζZ : ∀ t ∈ Icc 0 M.T, M.ζ t = (Z t)⁻¹ := fun t ht => by simp [Z]
  refine ⟨fun t => p t * Z t, fun t => ∫ s in M.T..t, Fc s, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; rw [h0, zero_mul, sub_zero]; exact hZp t ht
  · intro t ht
    have hz := hZp t ht
    have h1 : 0 < 1 + Y t := by linarith [hY0 t ht]
    refine ((hpd t ht).mul (zinv_deriv M t)).hasDerivWithinAt.congr_deriv ?_
    simp only [a₁, h0, zero_mul, add_zero, sub_zero]
    rw [hζZ t ht]
    simp only [p]
    generalize Y t = y at *; generalize Z t = z at *
    field_simp; ring
  · intro t ht
    refine (intervalIntegral.integral_hasDerivAt_right (hFcc.intervalIntegrable _ _)
      (hFcc.stronglyMeasurableAtFilter _ _) hFcc.continuousAt).hasDerivWithinAt.congr_deriv ?_
    rw [hFcF t ht]
    have hz := hZp t ht
    simp only [F, hζZ t ht]
    field_simp
  · simp [p, Y, ZT, div_self hZT.ne']
  · simp

end S46PE


open SmoothAmbEq.Gaussian in
theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : a < M.α) : ∃ m₂ m₃ : ℝ → ℝ, SolvesODE516 M m₂ m₃ := by
  rcases lt_trichotomy M.α 1 with h | h | h
  · by_cases h0 : M.α = 0
    · exact S46PE.sol_eq0 M h0
    · exact S46PE.sol_lt1 M a ha hα h h0
  · exact S46PE.sol_eq1 M h
  · exact S46PE.sol_gt1 M h
