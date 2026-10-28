-- Prove2me | solution 2 for RegevLWE.PeriodicGauss.claim_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:43.035699+00:00
-- url     : https://prove2.me/submissions/db4bdfe7-8ced-45ae-9bdc-cafbd3457c1c

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian
import Theorems.Thm_RegevLWE_PeriodicGauss_normal_bound

-- carved verbatim out of submission 15d24515-800e-484d-9b84-da15f24e9f7c, lines 334-349

section
set_option autoImplicit false
open MeasureTheory RegevLWE.PeriodicGauss
open MeasureTheory Set

lemma RLP_shift (g : ℝ → ENNReal) (k : ℤ) :
    ∫⁻ r in Ico (0:ℝ) 1, g (r + k) = ∫⁻ x in Ico (k:ℝ) (k+1), g x := by
  have := (measurePreserving_add_right volume (k:ℝ)).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (k:ℝ)) g (Ico (k:ℝ) (k+1))
  have hpre : (fun x : ℝ => x + k) ⁻¹' Ico (k:ℝ) (k+1) = Ico 0 1 := by
    ext x
    simp only [mem_preimage, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at this
  exact this

lemma RLP_periodize (g : ℝ → ENNReal) (hg : AEMeasurable g volume) :
    ∫⁻ r in Ico (0:ℝ) 1, ∑' k : ℤ, g (r - k) = ∫⁻ x, g x := by
  have hmeas : ∀ k : ℤ, AEMeasurable (fun r : ℝ => g (r - k))
      (volume.restrict (Ico (0:ℝ) 1)) := fun k =>
    (hg.comp_quasiMeasurePreserving ((measurePreserving_sub_right volume (k:ℝ)).quasiMeasurePreserving)).restrict
  rw [lintegral_tsum hmeas]
  have h1 : ∀ k : ℤ, ∫⁻ r in Ico (0:ℝ) 1, g (r - k) =
      ∫⁻ x in Ico ((-k : ℤ):ℝ) (((-k : ℤ):ℝ)+1), g x := by
    intro k
    rw [← RLP_shift g (-k)]
    refine lintegral_congr fun r => ?_
    simp [sub_eq_add_neg]
  simp_rw [h1]
  rw [show (∑' k : ℤ, ∫⁻ x in Ico ((-k : ℤ):ℝ) (((-k : ℤ):ℝ)+1), g x) =
      ∑' k : ℤ, ∫⁻ x in Ico (k:ℝ) (k+1), g x from
    (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ∫⁻ x in Ico (k:ℝ) (k+1), g x)]
  have hU : (⋃ k : ℤ, Ico (k:ℝ) (k+1)) = univ := by
    ext x
    simp only [mem_iUnion, mem_Ico, mem_univ, iff_true]
    exact ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩
  have hd : Pairwise (Function.onFun Disjoint fun k : ℤ => Ico (k:ℝ) (k+1)) := by
    intro a b hab
    refine disjoint_left.2 fun x hx hx' => hab ?_
    have h1 : ⌊x⌋ = a := Int.floor_eq_iff.2 ⟨hx.1, hx.2⟩
    have h2 : ⌊x⌋ = b := Int.floor_eq_iff.2 ⟨hx'.1, hx'.2⟩
    omega
  have := lintegral_iUnion (μ := volume) (fun k : ℤ => measurableSet_Ico) hd g
  rw [hU, Measure.restrict_univ] at this
  exact this.symm

lemma RLP_summable {φ : ℝ → ℝ} (h : Integrable φ) :
    ∀ᵐ r ∂(volume.restrict (Ico (0:ℝ) 1)), Summable (fun k : ℤ => φ (r - k)) := by
  set g : ℝ → ENNReal := fun x => ENNReal.ofReal ‖φ x‖ with hgdef
  have hg : AEMeasurable g volume := h.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
  have hfin : ∫⁻ x, g x ≠ ⊤ := by
    have e : g = fun x => ‖φ x‖ₑ := funext fun x => ofReal_norm _
    rw [e]
    exact h.hasFiniteIntegral.ne
  have hT : AEMeasurable (fun r => ∑' k : ℤ, g (r - k)) (volume.restrict (Ico (0:ℝ) 1)) :=
    AEMeasurable.ennreal_tsum fun k =>
      (hg.comp_quasiMeasurePreserving ((measurePreserving_sub_right volume (k:ℝ)).quasiMeasurePreserving)).restrict
  have hI : ∫⁻ r in Ico (0:ℝ) 1, ∑' k : ℤ, g (r - k) ≠ ⊤ := by
    rw [RLP_periodize g hg]; exact hfin
  have hae := ae_lt_top' hT hI
  filter_upwards [hae] with r hr
  have hne : ∑' k : ℤ, g (r - k) ≠ ⊤ := hr.ne
  have hs := ENNReal.summable_toReal hne
  have : Summable (fun k : ℤ => ‖φ (r - k)‖) := by
    refine hs.congr fun k => ?_
    simp [g, ENNReal.toReal_ofReal (norm_nonneg _)]
  exact this.of_norm

theorem RLP_periodization_le (φ₁ φ₂ : ℝ → ℝ) (h₁ : Integrable φ₁) (h₂ : Integrable φ₂) :
    statDistT (fun r => ∑' k : ℤ, φ₁ (r - k)) (fun r => ∑' k : ℤ, φ₂ (r - k)) ≤
      statDist φ₁ φ₂ := by
  unfold statDistT statDist
  have hd : Integrable (fun x => φ₁ x - φ₂ x) := h₁.sub h₂
  set g : ℝ → ENNReal := fun x => ENNReal.ofReal |φ₁ x - φ₂ x| with hg
  have hgm : AEMeasurable g volume := by
    have := hd.aestronglyMeasurable.aemeasurable.norm.ennreal_ofReal
    simpa [g, Real.norm_eq_abs] using this
  calc ∫⁻ r in Ico (0:ℝ) 1, ENNReal.ofReal |∑' k : ℤ, φ₁ (r - k) - ∑' k : ℤ, φ₂ (r - k)|
      ≤ ∫⁻ r in Ico (0:ℝ) 1, ∑' k : ℤ, g (r - k) := by
        refine lintegral_mono_ae ?_
        filter_upwards [RLP_summable h₁, RLP_summable h₂] with r hr1 hr2
        have hs := hr1.sub hr2
        have e : ∑' k : ℤ, φ₁ (r - k) - ∑' k : ℤ, φ₂ (r - k) =
            ∑' k : ℤ, (φ₁ (r - k) - φ₂ (r - k)) := (hr1.tsum_sub hr2).symm
        have habs : Summable (fun k : ℤ => |φ₁ (r - k) - φ₂ (r - k)|) := hs.abs
        rw [e]
        calc ENNReal.ofReal |∑' k : ℤ, (φ₁ (r - k) - φ₂ (r - k))|
            ≤ ENNReal.ofReal (∑' k : ℤ, |φ₁ (r - k) - φ₂ (r - k)|) := by
              apply ENNReal.ofReal_le_ofReal
              simpa [Real.norm_eq_abs] using
                norm_tsum_le_tsum_norm (f := fun k : ℤ => φ₁ (r - k) - φ₂ (r - k))
                  (by simpa [Real.norm_eq_abs] using habs)
          _ = ∑' k : ℤ, g (r - k) := ENNReal.ofReal_tsum_of_nonneg (fun k => abs_nonneg _) habs
    _ = ∫⁻ x, g x := RLP_periodize g hgm

theorem solution (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ : β ≤ 2 * α) :
    statDistT (Psi α) (Psi β) ≤ ENNReal.ofReal (9 * (β / α - 1)) := by
  have hint : ∀ γ : ℝ, 0 < γ → Integrable (nu γ) := by
    intro γ hγ
    have hb : 0 < Real.pi / γ ^ 2 := by positivity
    have e : nu γ = fun x => (1 / γ) * Real.exp (-(Real.pi / γ ^ 2) * x ^ 2) := by
      funext x
      unfold nu
      congr 2
      rw [div_pow]
      ring
    rw [e]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  have h := RLP_periodization_le (nu α) (nu β) (hint α hα) (hint β (hα.trans hαβ))
  exact h.trans (RegevLWE.PeriodicGauss.normal_bound α β hα hαβ hβ)

end
