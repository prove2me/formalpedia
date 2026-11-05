-- Prove2me | solution 1 for ShortWDRODual.Legendre.theorem_1_D
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:50:31.563225+00:00
-- url     : https://prove2.me/submissions/67749ec1-4aed-4c9d-98dd-f954f9a8a268

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting
import Theorems.Thm_ShortWDRODual_Legendre_theorem_1_hard
import Theorems.Thm_ShortWDRODual_Legendre_theorem_1_IP_fixed
import Theorems.Thm_ShortWDRODual_Legendre_theorem_1_soft
import Theorems.Thm_ShortWDRODual_Legendre_lemma_2_G
import Theorems.Thm_ShortWDRODual_Legendre_antitone_convex_le_biconj
import Theorems.Thm_ShortWDRODual_IP_extIntegral_le_supFn

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

lemma lamMul_mono (t : ENNReal) {a b : ℝ} (hab : a ≤ b) : lamMul a t ≤ lamMul b t := by
  by_cases ht : t = ⊤
  · unfold lamMul; rw [if_pos ht, if_pos ht]
  · rw [lamMul_eq a ht, lamMul_eq b ht]
    exact_mod_cast mul_le_mul_of_nonneg_right hab ENNReal.toReal_nonneg

lemma extIntegral_mono (μ : Measure X) {φ ψ : X → EReal} (h : ∀ x, φ x ≤ ψ x) :
    extIntegral μ φ ≤ extIntegral μ ψ := by
  unfold extIntegral
  apply EReal.sub_le_sub
  · exact_mod_cast lintegral_mono fun x => EReal.toENNReal_le_toENNReal (h x)
  · exact_mod_cast lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (h x))

lemma S_anti (Phat : Measure X) (c : X → X → ENNReal) (f : X → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f b)) ≤
      ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f a) := by
  refine iSup₂_mono fun γ _ => extIntegral_mono γ fun p => ?_
  unfold phiLam
  exact EReal.sub_le_sub le_rfl (lamMul_mono _ hab)

lemma ereal_le_of_forall_pos {a b : EReal} (h : ∀ δ : ℝ, 0 < δ → a ≤ (δ : EReal) + b) : a ≤ b := by
  induction b using EReal.rec with
  | bot =>
    have := h 1 one_pos
    simpa using this
  | top => exact le_top
  | coe b =>
    induction a using EReal.rec with
    | bot => exact bot_le
    | top =>
      have := h 1 one_pos
      rw [← EReal.coe_add] at this
      exact absurd this (not_le.mpr (EReal.coe_lt_top _))
    | coe a =>
      have : ∀ δ : ℝ, 0 < δ → a ≤ δ + b := fun δ hδ => by
        have := h δ hδ
        rw [← EReal.coe_add] at this
        exact_mod_cast this
      exact_mod_cast le_of_forall_pos_le_add fun δ hδ => by linarith [this δ hδ]

end WDRO1Red

open WDRO1Red

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0) :
    (∀ lam : ℝ, 0 < lam → IP Phat (phiLam c f lam)) ↔
      ((∀ lam : ℝ, 0 < lam → NullMeasurable (supFn (phiLam c f lam)) Phat) ∧
        ∀ ρ : ℝ, 0 < ρ →
          IsLeast {y : EReal | ∃ lam : ℝ, 0 ≤ lam ∧ y = ((lam * ρ : ℝ) : EReal) + dualG c f Phat lam}
            (robustLoss c f Phat ρ)) := by
  constructor
  · intro hIP
    have hmeas : ∀ lam : ℝ, 0 < lam → NullMeasurable (supFn (phiLam c f lam)) Phat :=
      fun lam h => (hIP lam h).2.2.1
    have hSG : ∀ lam : ℝ, 0 < lam →
        (⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam)) = dualG c f Phat lam :=
      fun lam h => (hIP lam h).2.2.2.symm
    obtain ⟨_, hGanti, _, hGlsc⟩ := lemma_2_G Phat f c hf hfint hc hc0 hmeas
    refine ⟨hmeas, fun ρ hρ => ?_⟩
    obtain ⟨⟨lam0, hlam0, heq⟩, hlow⟩ := theorem_1_hard Phat f c hf hfint hc hc0 ρ hρ
    have hpos : ∀ lam : ℝ, 0 < lam →
        robustLoss c f Phat ρ ≤ ((lam * ρ : ℝ) : EReal) + dualG c f Phat lam := by
      intro lam hlam
      rw [← hSG lam hlam]
      exact hlow ⟨lam, hlam.le, rfl⟩
    have hzero : robustLoss c f Phat ρ ≤ dualG c f Phat 0 := by
      apply ereal_le_of_forall_pos
      intro δ hδ
      have hl : 0 < δ / ρ := div_pos hδ hρ
      have h1 := hpos (δ / ρ) hl
      have h2 : dualG c f Phat (δ / ρ) ≤ dualG c f Phat 0 :=
        hGanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hl.le) hl.le
      rw [div_mul_cancel₀ δ hρ.ne'] at h1
      exact h1.trans (add_le_add le_rfl h2)
    refine ⟨?_, ?_⟩
    · rcases hlam0.lt_or_eq with hlt | heq0
      · exact ⟨lam0, hlam0, heq.trans (by rw [hSG lam0 hlt])⟩
      · subst heq0
        refine ⟨0, le_rfl, ?_⟩
        simp only [zero_mul, EReal.coe_zero, zero_add] at heq ⊢
        apply le_antisymm hzero
        -- G(0) ≤ S(0) = 𝓛(ρ), by lower semicontinuity of G at 0
        rw [heq]
        refine le_of_forall_lt fun y hy => ?_
        have hev := hGlsc 0 (Set.mem_Ici.mpr le_rfl) y hy
        have hev' : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), y < dualG c f Phat x :=
          hev.filter_mono (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
        obtain ⟨x, hx1, hx2⟩ := (hev'.and self_mem_nhdsWithin).exists
        calc y < dualG c f Phat x := hx1
          _ = ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f x) := (hSG x hx2).symm
          _ ≤ ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f 0) :=
            S_anti Phat c f (le_of_lt hx2)
    · rintro y ⟨lam, hlam, rfl⟩
      rcases hlam.lt_or_eq with hlt | heq0
      · exact hpos lam hlt
      · subst heq0
        simpa using hzero
  · rintro ⟨hmeas, hD⟩ lam hlam
    rw [theorem_1_IP_fixed Phat f c hf hfint hc hc0 lam hlam]
    refine ⟨hmeas lam hlam, le_antisymm ?_ ?_⟩
    · rw [theorem_1_soft Phat f c hf hfint hc hc0 lam hlam]
      refine iSup₂_le fun γ hγ => ?_
      exact ShortWDRODual.IP.extIntegral_le_supFn Phat (phiLam c f lam)
        (phiLam_measurable c f hf hc lam) (phiLam_ne_top c f lam) (hmeas lam hlam) γ hγ
    · obtain ⟨hGlb, hGanti, hGconv, hGlsc⟩ := lemma_2_G Phat f c hf hfint hc hc0 hmeas
      have hbot : ∀ μ : ℝ, 0 ≤ μ → dualG c f Phat μ ≠ ⊥ :=
        fun μ hμ => ne_bot_of_gt (hfint.trans_le (hGlb μ hμ))
      refine (antitone_convex_le_biconj (dualG c f Phat) hbot hGanti hGconv hGlsc lam hlam).trans ?_
      refine iSup₂_le fun ρ hρ => ?_
      obtain ⟨⟨μ, hμ, hy⟩, _⟩ := hD ρ hρ
      have h1 : (⨅ (μ : ℝ) (_ : 0 ≤ μ), ((μ * ρ : ℝ) : EReal) + dualG c f Phat μ) ≤
          robustLoss c f Phat ρ := by
        rw [hy]; exact iInf₂_le μ hμ
      unfold legendre
      refine le_iSup_of_le ρ ?_
      have halg : ((-lam * ρ : ℝ) : EReal) - -robustLoss c f Phat ρ =
          robustLoss c f Phat ρ - ((lam * ρ : ℝ) : EReal) := by
        rw [neg_mul, EReal.coe_neg, sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
      rw [halg]
      exact EReal.sub_le_sub h1 le_rfl
