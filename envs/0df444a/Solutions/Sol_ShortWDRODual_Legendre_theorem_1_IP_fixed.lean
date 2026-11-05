-- Prove2me | solution 1 for ShortWDRODual.Legendre.theorem_1_IP_fixed
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:50:32.54855+00:00
-- url     : https://prove2.me/submissions/122522bc-f9ed-423d-99a9-9d2c9bbfc924

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting
import Theorems.Thm_ShortWDRODual_Legendre_theorem_1_soft

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre

namespace WDRO1Red

variable {X : Type*} [MeasurableSpace X]

lemma lamMul_measurable (lam : ℝ) : Measurable (lamMul lam) := by
  unfold lamMul
  refine Measurable.ite (measurableSet_singleton ⊤) measurable_const ?_
  exact (measurable_coe_ennreal_ereal).const_mul _

lemma phiLam_measurable (c : X → X → ENNReal) (f : X → ℝ) (hf : Measurable f)
    (hc : Measurable (fun p : X × X => c p.1 p.2)) (lam : ℝ) :
    Measurable (phiLam c f lam) := by
  unfold phiLam
  have h1 : Measurable (fun p : X × X => (f p.2 : EReal)) :=
    (hf.comp measurable_snd).coe_real_ereal
  have h2 : Measurable (fun p : X × X => lamMul lam (c p.1 p.2)) :=
    (lamMul_measurable lam).comp hc
  simp_rw [sub_eq_add_neg]
  exact h1.add h2.neg

lemma lamMul_eq (lam : ℝ) {t : ENNReal} (ht : t ≠ ⊤) :
    lamMul lam t = ((lam * t.toReal : ℝ) : EReal) := by
  unfold lamMul
  rw [if_neg ht, EReal.coe_mul, EReal.coe_ennreal_toReal ht]

lemma phiLam_ne_top (c : X → X → ENNReal) (f : X → ℝ) (lam : ℝ) (p : X × X) :
    phiLam c f lam p ≠ ⊤ := by
  unfold phiLam
  by_cases ht : c p.1 p.2 = ⊤
  · unfold lamMul; rw [if_pos ht, EReal.sub_top]; exact bot_ne_top
  · rw [lamMul_eq lam ht, ← EReal.coe_sub]; exact EReal.coe_ne_top _

end WDRO1Red

open WDRO1Red

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    IP Phat (phiLam c f lam) ↔
      (NullMeasurable (supFn (phiLam c f lam)) Phat ∧
        legendre (fun ρ => - robustLoss c f Phat ρ) (-lam) = dualG c f Phat lam) := by
  rw [theorem_1_soft Phat f c hf hfint hc hc0 lam hlam]
  constructor
  · rintro ⟨_, _, hm, heq⟩
    exact ⟨hm, heq.symm⟩
  · rintro ⟨hm, heq⟩
    exact ⟨phiLam_measurable c f hf hc lam, phiLam_ne_top c f lam, hm, heq.symm⟩
