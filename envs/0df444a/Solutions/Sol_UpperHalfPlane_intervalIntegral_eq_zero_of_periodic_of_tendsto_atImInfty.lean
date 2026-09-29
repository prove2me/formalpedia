-- Prove2me | solution 1 for UpperHalfPlane.intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3affc6b7-43c6-5acb-a1c6-432b36a320e9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty

open UpperHalfPlane Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace ConstantTermVanishing

def reg (f : ℂ → ℂ) (z : ℂ) : ℂ := limUnder (𝓝[≠] z) f

theorem reg_spec {f g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (h : ∀ᶠ w in 𝓝[≠] z, f w = g w) :
    (∀ᶠ w in 𝓝 z, reg f w = g w) ∧ ∀ᶠ w in 𝓝[≠] z, f w = reg f w := by
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h
  obtain ⟨U, hU, hUo, hzU⟩ := h
  set A : Set ℂ := {w | AnalyticAt ℂ g w}
  have hAo : IsOpen A := isOpen_analyticAt ℂ g
  have hzA : z ∈ A := hg

  have key : ∀ w ∈ U ∩ A, reg f w = g w := by
    rintro w ⟨hwU, hwA⟩
    apply Tendsto.limUnder_eq
    have hgc : Tendsto g (𝓝[≠] w) (𝓝 (g w)) :=
      (hwA : AnalyticAt ℂ g w).continuousAt.continuousWithinAt.tendsto
    refine hgc.congr' ?_
    have h1 : ∀ᶠ w' in 𝓝[≠] w, w' ∈ U := mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hwU)
    have h2 : ∀ᶠ w' in 𝓝[≠] w, w' ≠ z := by
      by_cases hwz : w = z
      · subst hwz; exact self_mem_nhdsWithin
      · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hwz)
    filter_upwards [h1, h2] with w' h1 h2
    exact (hU w' h1 h2).symm
  have hUA : U ∩ A ∈ 𝓝 z := (hUo.inter hAo).mem_nhds ⟨hzU, hzA⟩
  refine ⟨?_, ?_⟩
  · filter_upwards [hUA] with w hw
    exact key w hw
  · have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ U ∩ A := mem_nhdsWithin_of_mem_nhds hUA
    filter_upwards [h1, self_mem_nhdsWithin] with w hw hwz
    rw [key w hw, hU w hw.1 hwz]

theorem ofComplex_add_one {w : ℂ} (hw : 0 < w.im) :
    ofComplex (w + 1) = (1 : ℝ) +ᵥ ofComplex w := by
  have h1 : 0 < (w + 1).im := by simpa using hw
  apply UpperHalfPlane.ext
  rw [coe_vadd, ofComplex_apply_of_im_pos h1, ofComplex_apply_of_im_pos hw, coe_mk, coe_mk]
  push_cast
  ring

theorem finite_inter_of_locally_subsingleton {D K : Set ℝ} (hK : IsCompact K)
    (hD : ∀ x : ℝ, ∀ᶠ x' in 𝓝[≠] x, x' ∉ D) : (D ∩ K).Finite := by
  have hU : ∀ x : ℝ, ∃ U ∈ 𝓝 x, U ∩ D ⊆ {x} := by
    intro x
    have := hD x
    rw [eventually_nhdsWithin_iff] at this
    exact ⟨_, this, fun x' ⟨h1, h2⟩ => by
      by_contra h3
      exact h1 h3 h2⟩
  choose U hUn hUD using hU
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover U fun x _ => hUn x
  refine (t.finite_toSet).subset ?_
  rintro x ⟨hxD, hxK⟩
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hKt hxK)
  have : x ∈ ({i} : Set ℝ) := hUD i ⟨hxi, hxD⟩
  rw [mem_singleton_iff] at this
  subst this
  exact hi

theorem main
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (y : ℝ) (hy : Y < y) :
    ∫ x in (0 : ℝ)..1, ω (ofComplex (x + y * Complex.I)) = 0 := by
  set F : ℂ → ℂ := fun z => ω (ofComplex z) with hF
  set G : ℂ → ℂ := reg F with hG
  have hholC : ∀ z : ℂ, Y < z.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝[≠] z, F w = g w := fun z hz => hhol ⟨z, hY.trans_lt hz⟩ hz

  have hGan : ∀ z : ℂ, Y < z.im → AnalyticAt ℂ G z := by
    intro z hz
    obtain ⟨g, hg, hev⟩ := hholC z hz
    exact hg.congr ((reg_spec hg hev).1.mono fun w hw => hw.symm)
  have hGeq : ∀ z : ℂ, Y < z.im → ∀ᶠ w in 𝓝[≠] z, F w = G w := by
    intro z hz
    obtain ⟨g, hg, hev⟩ := hholC z hz
    exact (reg_spec hg hev).2

  have hGt : ∀ z : ℂ, Y < z.im → Tendsto F (𝓝[≠] z) (𝓝 (G z)) := by
    intro z hz
    have hc : Tendsto G (𝓝[≠] z) (𝓝 (G z)) :=
      (hGan z hz).continuousAt.continuousWithinAt.tendsto
    exact hc.congr' ((hGeq z hz).mono fun w hw => hw.symm)

  have hGper : ∀ z : ℂ, Y < z.im → G (z + 1) = G z := by
    intro z hz
    apply Tendsto.limUnder_eq
    have hsh : Tendsto (fun w : ℂ => w - 1) (𝓝[≠] (z + 1)) (𝓝[≠] z) := by
      have := ((continuous_sub_right (1 : ℂ)).continuousWithinAt (s := {z + 1}ᶜ)
        (x := z + 1)).tendsto_nhdsWithin (t := {z}ᶜ) (fun w hw => by
          simp only [mem_compl_iff, mem_singleton_iff] at hw ⊢
          intro h; exact hw (by rw [← h]; ring))
      simpa using this
    have h1 : Tendsto (fun w => F (w - 1)) (𝓝[≠] (z + 1)) (𝓝 (G z)) := (hGt z hz).comp hsh
    refine h1.congr' ?_
    have hpos : ∀ᶠ w in 𝓝[≠] (z + 1), 0 < (w - 1).im := by
      apply mem_nhdsWithin_of_mem_nhds
      have : 0 < ((z + 1) - 1).im := by simpa using hY.trans_lt hz
      exact (Complex.continuous_im.comp (continuous_sub_right (1 : ℂ))).isOpen_preimage _ isOpen_Ioi
        |>.mem_nhds this
    filter_upwards [hpos] with w hw
    show ω (ofComplex (w - 1)) = ω (ofComplex w)
    rw [← hper (ofComplex (w - 1)), ← ofComplex_add_one hw, sub_add_cancel]

  have hGsmall : ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℂ, A ≤ z.im → Y < z.im → ‖G z‖ ≤ ε := by
    intro ε hε
    have h1 := (Metric.tendsto_nhds.1 hcusp) ε hε
    rw [Filter.Eventually, atImInfty_mem] at h1
    obtain ⟨A₀, hA₀⟩ := h1
    refine ⟨A₀ + 1, fun z hzA hzY => ?_⟩
    have hz0 : 0 < z.im := hY.trans_lt hzY
    have hopen : Complex.im ⁻¹' Ioi (max A₀ 0) ∈ 𝓝 z :=
      (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds (by
        show max A₀ 0 < z.im
        exact max_lt (by linarith) hz0)
    have hev : ∀ᶠ w in 𝓝[≠] z, ‖F w‖ ≤ ε := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with w hw
      have hw' : max A₀ 0 < w.im := hw
      have hw0 : 0 < w.im := (le_max_right _ _).trans_lt hw'
      have hwA : A₀ ≤ (ofComplex w).im := by
        rw [ofComplex_apply_of_im_pos hw0]
        exact (le_max_left _ _).trans hw'.le
      have := hA₀ _ hwA
      simp only [mem_setOf_eq, dist_zero_right] at this
      exact this.le
    exact le_of_tendsto (hGt z hzY).norm hev

  set V : ℝ → ℂ := fun t => ∫ x in (0 : ℝ)..1, G (x + t * Complex.I) with hV
  have hVeq : ∀ y₁ y₂ : ℝ, Y < y₁ → Y < y₂ → V y₁ = V y₂ := by
    intro y₁ y₂ h1 h2
    have hdiff : DifferentiableOn ℂ G (uIcc (0 : ℝ) 1 ×ℂ uIcc y₁ y₂) := by
      intro s hs
      rw [mem_reProdIm] at hs
      have hsY : Y < s.im := by
        rcases mem_uIcc.1 hs.2 with h | h <;> linarith [h.1]
      exact (hGan s hsY).differentiableAt.differentiableWithinAt
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G ⟨0, y₁⟩ ⟨1, y₂⟩
      hdiff
    dsimp only at key
    have hside : (∫ t in y₁..y₂, G (((1 : ℝ) : ℂ) + t * Complex.I))
        = ∫ t in y₁..y₂, G (((0 : ℝ) : ℂ) + t * Complex.I) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      have hYt : Y < t := by
        rcases mem_uIcc.1 ht with h | h <;> linarith [h.1]
      show G (((1 : ℝ) : ℂ) + t * Complex.I) = G (((0 : ℝ) : ℂ) + t * Complex.I)
      rw [← hGper (((0 : ℝ) : ℂ) + t * Complex.I) (by simpa using hYt)]
      congr 1
      push_cast
      ring
    rw [hside, add_sub_cancel_right, sub_eq_zero] at key
    exact key

  have hVsmall : ∀ ε : ℝ, 0 < ε → ‖V y‖ ≤ ε := by
    intro ε hε
    obtain ⟨A, hA⟩ := hGsmall ε hε
    set y₂ : ℝ := max A (Y + 1) with hy₂def
    have hy₂ : Y < y₂ := lt_max_iff.2 (Or.inr (by linarith))
    rw [hVeq y y₂ hy hy₂]
    have : ‖V y₂‖ ≤ ε * |(1 : ℝ) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x _
      have him : ((x : ℂ) + y₂ * Complex.I).im = y₂ := by simp
      apply hA
      · rw [him]; exact le_max_left _ _
      · rw [him]; exact hy₂
    simpa using this
  have hV0 : V y = 0 := by
    have : ‖V y‖ ≤ 0 :=
      le_of_forall_pos_le_add fun ε hε => by rw [zero_add]; exact hVsmall ε hε
    exact norm_le_zero_iff.1 this

  have hD : ∀ x : ℝ, ∀ᶠ x' in 𝓝[≠] x,
      x' ∉ {x : ℝ | F (x + y * Complex.I) ≠ G (x + y * Complex.I)} := by
    intro x
    have hℓ : Tendsto (fun x' : ℝ => (x' : ℂ) + y * Complex.I) (𝓝[≠] x)
        (𝓝[≠] ((x : ℂ) + y * Complex.I)) := by
      refine ((continuous_ofReal.add continuous_const).continuousWithinAt).tendsto_nhdsWithin
        ?_
      intro x' hx'
      simp only [mem_compl_iff, mem_singleton_iff] at hx' ⊢
      intro h
      apply hx'
      have := congrArg Complex.re h
      simpa using this
    have hev := hGeq ((x : ℂ) + y * Complex.I) (by simpa using hy)
    filter_upwards [hℓ.eventually hev] with x' hx'
    intro hne
    exact hne hx'
  have hfin := finite_inter_of_locally_subsingleton (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hD
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ uIoc (0 : ℝ) 1 →
      F (x + y * Complex.I) = G (x + y * Complex.I) := by
    filter_upwards [hfin.countable.ae_notMem volume] with x hx hxI
    by_contra hne
    exact hx ⟨hne, Ioc_subset_Icc_self (by rwa [uIoc_of_le zero_le_one] at hxI)⟩
  calc ∫ x in (0 : ℝ)..1, F (x + y * Complex.I) = V y := intervalIntegral.integral_congr_ae hae
    _ = 0 := hV0

end ConstantTermVanishing

end

open UpperHalfPlane Filter in
open scoped Topology in
theorem solution
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (y : ℝ) (hy : Y < y) :
    ∫ x in (0 : ℝ)..1, ω (ofComplex (x + y * Complex.I)) = 0 :=
  ConstantTermVanishing.main ω Y hY hper hcusp hhol y hy

end S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty
end P2MW
export P2MW.S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty (solution)
