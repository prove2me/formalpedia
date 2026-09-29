-- Prove2me | solution 1 for PorteusSS.leibniz_exp_kernel
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:40:55.089205+00:00
-- url     : https://prove2.me/submissions/b11800d8-8638-45e3-9a4d-0df099454429

import Mathlib

open MeasureTheory Filter Topology Set

namespace PorteusSS

lemma aux_lek_mp (x : ℝ) : MeasurePreserving (fun t : ℝ => x - t) volume volume :=
  Measure.measurePreserving_sub_left volume x

lemma aux_lek_me (x : ℝ) : MeasurableEmbedding (fun t : ℝ => x - t) :=
  (Homeomorph.subLeft x).measurableEmbedding

lemma aux_lek_pre (x : ℝ) : (fun t : ℝ => x - t) ⁻¹' Iic x = Ici 0 := by
  ext t; simp

lemma aux_lek_cov (φ : ℝ → ℝ) (x : ℝ) :
    ∫ t in Ici (0:ℝ), φ (x - t) = ∫ s in Iic x, φ s := by
  have := (aux_lek_mp x).setIntegral_preimage_emb (aux_lek_me x) φ (Iic x)
  rw [aux_lek_pre] at this
  exact this

lemma aux_lek_cov_int (φ : ℝ → ℝ) (x : ℝ) :
    IntegrableOn (fun t => φ (x - t)) (Ici (0:ℝ)) ↔ IntegrableOn φ (Iic x) := by
  have := (aux_lek_mp x).integrableOn_comp_preimage (aux_lek_me x) (f := φ) (s := Iic x)
  rw [aux_lek_pre] at this
  exact this

end PorteusSS

open PorteusSS

theorem solution (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hg : Continuous g)
    (hint : ∀ x : ℝ,
      IntegrableOn (fun t => g (x - t) * (lam * Real.exp (-lam * t))) (Ici 0)) :
    ContDiff ℝ 1 (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t))) ∧
      ∀ x : ℝ, HasDerivAt (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
        (lam * (g x - ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))) x := by
  set h : ℝ → ℝ := fun s => g s * Real.exp (lam * s) with hh
  have hcont : Continuous h := hg.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  -- rewriting the integrand
  have hform : ∀ x t : ℝ, g (x - t) * (lam * Real.exp (-lam * t))
      = (lam * Real.exp (-lam * x)) * h (x - t) := by
    intro x t
    simp only [hh]
    have : Real.exp (-lam * t) = Real.exp (-lam * x) * Real.exp (lam * (x - t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hintH : ∀ x : ℝ, IntegrableOn h (Iic x) := by
    intro x
    rw [← aux_lek_cov_int]
    have hne : lam * Real.exp (-lam * x) ≠ 0 := by positivity
    have hi : IntegrableOn (fun t => (lam * Real.exp (-lam * x))⁻¹ *
        (g (x - t) * (lam * Real.exp (-lam * t)))) (Ici 0) :=
      (hint x).const_mul (lam * Real.exp (-lam * x))⁻¹
    refine IntegrableOn.congr_fun hi (fun t _ => ?_) measurableSet_Ici
    simp only [hform x t]
    field_simp
  set G : ℝ → ℝ := fun x => ∫ s in Iic x, h s with hG
  have hF : (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
      = fun x => (lam * Real.exp (-lam * x)) * G x := by
    funext x
    simp only [hform x, integral_const_mul, hG]
    rw [aux_lek_cov h x]
  have hG' : G = fun x => G 0 + ∫ s in (0:ℝ)..x, h s := by
    funext x
    rw [← intervalIntegral.integral_Iic_sub_Iic (hintH 0) (hintH x)]
    simp [hG]
  have hGd : ∀ x, HasDerivAt G (h x) x := by
    intro x
    rw [hG']
    exact ((hcont.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
        (lam * (g x - ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))) x := by
    intro x
    rw [hF]
    have he : HasDerivAt (fun x => lam * Real.exp (-lam * x)) (lam * (Real.exp (-lam * x) * (-lam))) x := by
      have := ((hasDerivAt_id x).const_mul (-lam)).exp
      simpa using this.const_mul lam
    have hm : HasDerivAt (fun y => lam * Real.exp (-lam * y) * G y)
        (lam * (Real.exp (-lam * x) * (-lam)) * G x + lam * Real.exp (-lam * x) * h x) x :=
      HasDerivAt.mul he (hGd x)
    refine hm.congr_deriv ?_
    rw [show (∫ t in Ici (0:ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
      = lam * Real.exp (-lam * x) * G x from congrFun hF x]
    simp only [hh]
    have : Real.exp (-lam * x) * Real.exp (lam * x) = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination (lam * g x) * this
  refine ⟨?_, hderiv⟩
  rw [contDiff_one_iff_deriv]
  have hdiff : Differentiable ℝ (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t))) :=
    fun x => (hderiv x).differentiableAt
  refine ⟨hdiff, ?_⟩
  have : deriv (fun x => ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t)))
      = fun x => lam * (g x - ∫ t in Ici (0 : ℝ), g (x - t) * (lam * Real.exp (-lam * t))) := by
    funext x; exact (hderiv x).deriv
  rw [this]
  exact continuous_const.mul (hg.sub hdiff.continuous)
