-- Prove2me | solution 1 for RetirePartialInfo.Duality.Supplement.theorem_3_2_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:15:37.009944+00:00
-- url     : https://prove2.me/submissions/af4eb5b5-a33f-42fe-ad41-15a78e6e4575

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Supplement_Analysis

open Set
set_option autoImplicit false

open RetirePartialInfo
open RetirePartialInfo.Duality
open RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), p.20, Theorem 3.2, (37)–(39); p.17, (32).
**Formalization Note.** Counterexample on the source-allowed ξ=0 subfamily, T1>0.
Then g(t,y)=ℓ(1-exp(-β(T1-t)))/β>0 for t<T1, independent of y and p.
Thus (37) contradicts global L^q on the unbounded y-domain. Every clause of the printed
existence package, including +2 and unconditional p monotonicity, is inside the negation.
No sign condition is imposed on the risk premium; no replacement with a local space. -/
theorem solution (a : Data) (ha : a.Admissible)
    (hxi : a.par.ξ = 0) (hh : 0 < a.par.T1) (q : ℝ) (hq : 1 ≤ q) :
    ¬ ∃ f : Value,
      GlobalW a.par.T1 q f ∧ C1 a.par.T1 f ∧ VI32 a f ∧
      (∀ z ∈ domain a.par.T1,
        max (obstacle a (z 0) (z 1)) 0 ≤ flatten f z ∧
        flatten f z ≤ a.par.ℓ / a.par.β *
          (1 - Real.exp (-a.par.β * (a.par.T1 - z 0))) + 2 ∧
        -(a.par.ξ / a.par.r) * (1 - Real.exp (-a.par.r * (a.par.T1 - z 0))) ≤
          dy f (z 0) (z 1) (z 2) ∧
        dy f (z 0) (z 1) (z 2) ≤ 0 ∧ 0 ≤ dp f (z 0) (z 1) (z 2)) := by
          rintro ⟨f, hW, -, -, hbd⟩
          obtain ⟨-, hW'⟩ := hW
          obtain ⟨g, hg, hgLp⟩ := hW' ![0,0,0] (by simp [orders])
          set T1 := a.par.T1 with hT1
          let S : Set Space := {z | z 0 ∈ Ioo 0 (T1/2) ∧ z 1 ∈ Ioi 1 ∧ z 2 ∈ Ioo 0 1}
          have hS_sub : S ⊆ domain T1 := by
            rintro z ⟨⟨h0, h0'⟩, h1, h2⟩
            refine ⟨⟨h0.le, by linarith⟩, ?_, h2⟩
            have : (1:ℝ) < z 1 := h1
            linarith
          have hSopen : IsOpen S := by
            have c0 : Continuous fun z : Space => z 0 := by fun_prop
            have c1 : Continuous fun z : Space => z 1 := by fun_prop
            have c2 : Continuous fun z : Space => z 2 := by fun_prop
            exact (isOpen_Ioo.preimage c0).inter ((isOpen_Ioi.preimage c1).inter (isOpen_Ioo.preimage c2))
          have hmd : ∀ φ : Space → ℝ, HunterPDE.Shared.multiDeriv φ ![0,0,0] = φ := by
            intro φ
            rfl
          have key : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure Space), z ∈ S → g z - flatten f z = 0 := by
            refine hSopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
              ((hg.2.1.sub hg.1).mono_set hS_sub) ?_
            intro φ hφ hφc hφS
            have hK : IsCompact (tsupport φ) := hφc
            have hKd : tsupport φ ⊆ domain T1 := hφS.trans hS_sub
            have hint := hg.2.2 φ ⟨hφ, hφc, hKd⟩
            rw [hmd] at hint
            have hs : (-1:ℝ)^(∑ i, (![0,0,0] : Fin 3 → ℕ) i) = 1 := by simp [Fin.sum_univ_three]
            rw [hs, one_mul] at hint
            have hz : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
            have Ig : MeasureTheory.Integrable (fun x => g x * φ x) := by
              rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset (s := tsupport φ)]
              · exact (hg.2.1.integrableOn_compact_subset hKd hK).mul_continuousOn
                  hφ.continuous.continuousOn hK
              · intro x hx; by_contra h; exact hx (by simp [hz x h])
            have If : MeasureTheory.Integrable (fun x => flatten f x * φ x) := by
              rw [← MeasureTheory.integrableOn_iff_integrable_of_support_subset (s := tsupport φ)]
              · exact (hg.1.integrableOn_compact_subset hKd hK).mul_continuousOn
                  hφ.continuous.continuousOn hK
              · intro x hx; by_contra h; exact hx (by simp [hz x h])
            have e1 : ∫ x in domain T1, g x * φ x = ∫ x, g x * φ x :=
              MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
                (fun x hx => by rw [hz x (fun h => hx (hKd h)), mul_zero])
            have e2 : ∫ x in domain T1, flatten f x * φ x = ∫ x, flatten f x * φ x :=
              MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
                (fun x hx => by rw [hz x (fun h => hx (hKd h)), mul_zero])
            have e3 : (fun x => φ x • (g x - flatten f x)) = fun x => g x * φ x - flatten f x * φ x := by
              funext x; simp only [smul_eq_mul]; ring
            rw [e3, MeasureTheory.integral_sub Ig If, ← e1, ← e2, hint, sub_self]
          have hβ := a.par.β_pos
          have hℓ := a.par.ℓ_pos
          set c : ℝ := (1 - Real.exp (-(a.par.β * (T1/2)))) * a.par.ℓ / a.par.β with hcdef
          have hc0 : 0 < c := by
            have : Real.exp (-(a.par.β * (T1/2))) < 1 := by
              have h := Real.exp_lt_exp.mpr (show -(a.par.β * (T1/2)) < 0 by nlinarith)
              rwa [Real.exp_zero] at h
            rw [hcdef]; apply div_pos _ hβ; apply mul_pos _ hℓ; linarith
          have hc : ∀ z ∈ S, c ≤ flatten f z := by
            intro z hz
            have h1 := (le_max_left _ _).trans (hbd z (hS_sub hz)).1
            have hb : b a.par (z 0) = 0 := by unfold b; simp [hxi]
            have hob : obstacle a (z 0) (z 1) = (1 - Real.exp (a.par.β * (z 0 - T1))) * a.par.ℓ / a.par.β := by
              unfold obstacle laborCost; rw [hb]; ring
            rw [hob] at h1
            refine le_trans ?_ h1
            rw [hcdef]
            apply div_le_div_of_nonneg_right _ hβ.le
            apply mul_le_mul_of_nonneg_right _ hℓ.le
            have hz0 : z 0 < T1 / 2 := hz.1.2
            have : Real.exp (a.par.β * (z 0 - T1)) ≤ Real.exp (-(a.par.β * (T1/2))) := by
              rw [Real.exp_le_exp]; nlinarith
            linarith
          have hSmeas : MeasurableSet S := hSopen.measurableSet
          let cn : NNReal := ⟨c, hc0.le⟩
          have hcn : cn ≠ 0 := by
            intro h; exact hc0.ne' (congrArg NNReal.toReal h)
          have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
          have hfin := (hgLp.mono_measure (MeasureTheory.Measure.restrict_mono hS_sub le_rfl)).meas_ge_lt_top
            hq0 ENNReal.ofReal_ne_top hcn
          have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict S), x ∈ {x | cn ≤ ‖g x‖₊} := by
            rw [MeasureTheory.ae_restrict_iff' hSmeas]
            refine key.mono fun x hx hxS => ?_
            have hgx : g x = flatten f x := by linarith [hx hxS]
            show cn ≤ ‖g x‖₊
            rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, hgx]
            exact le_abs.mpr (Or.inl (hc x hxS))
          have hle : (MeasureTheory.volume.restrict S) univ ≤ (MeasureTheory.volume.restrict S) {x | cn ≤ ‖g x‖₊} :=
            MeasureTheory.measure_mono_ae (hae.mono fun x hx _ => hx)
          rw [MeasureTheory.Measure.restrict_apply_univ] at hle
          have hinf : MeasureTheory.volume S = ⊤ := by
            let I : Fin 3 → Set ℝ := ![Ioo 0 (T1/2), Ioi 1, Ioo 0 1]
            have hSeq : S = (fun z : Space => z.ofLp) ⁻¹' (Set.pi univ I) := by
              ext z
              simp [S, I, Fin.forall_fin_succ]
            rw [hSeq, (PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage
              (MeasurableSet.univ_pi (fun i => by fin_cases i <;> simp [I])).nullMeasurableSet,
              MeasureTheory.volume_pi_pi, Fin.prod_univ_three]
            simp [I, Real.volume_Ioo, Real.volume_Ioi]
            exact ENNReal.mul_top (by simp; linarith)
          rw [hinf] at hle
          exact absurd (lt_of_le_of_lt hle hfin) (lt_irrefl _)
