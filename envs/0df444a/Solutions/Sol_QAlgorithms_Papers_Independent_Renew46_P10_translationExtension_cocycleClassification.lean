-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P10.translationExtension_cocycleClassification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:28:31.497393+00:00
-- url     : https://prove2.me/submissions/6b04b149-fa02-47a1-9fc6-85c11deaaed0

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P10

namespace QAlgorithms.Papers.Independent.Renew46.P10

universe u v

lemma S170B_conj {G : Type u} [Group G] (H : Subgroup G) [H.Normal] (h : H) (g : G) :
    g⁻¹ * (h : G) * g ∈ H := by
  have := ‹H.Normal›.conj_mem (h : G) h.2 g⁻¹
  simpa using this

/-- Lemma B from the twisted identity. -/
lemma S170B_lemB_tw {G : Type u} [Group G] (H : Subgroup G) {L : Type v}
    (star : L → G → L) (c : L → G → H) (hc : TwistedCocycleData H star c) (l : L) (h : H) (g : G) :
    (c l ((h : G) * g) : G) = (c l g : G) * g⁻¹ * (h : G) * g := by
  rw [hc.2.2 l h g, hc.1.2 l h, hc.2.1 l h]

lemma S170B_lemB_nest {G : Type u} [Group G] (H : Subgroup G) [H.Normal] {L : Type v}
    (star : L → G → L) (c : L → G → H) (hc : NestedCocycleData H star c) (l : L) (h : H) (g : G) :
    (c l ((h : G) * g) : G) = (c l g : G) * g⁻¹ * (h : G) * g := by
  have e : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
  rw [e, hc.2.2 l g]
  have hm : (c l g : G) * (g⁻¹ * (h : G) * g) ∈ H :=
    H.mul_mem (c l g).2 (S170B_conj H h g)
  have := hc.2.1 (star l g) ⟨_, hm⟩
  simp only at this
  rw [this]; simp [mul_assoc]

lemma S170B_tw_iff {G : Type u} [Group G] (H : Subgroup G) [H.Normal] {L : Type v}
    (star : L → G → L) (c : L → G → H) :
    TwistedCocycleData H star c ↔ NestedCocycleData H star c := by
  constructor
  · intro hc
    refine ⟨hc.1, hc.2.1, fun l g g2 => ?_⟩
    apply Subtype.ext
    rw [hc.2.2 l g g2]
    have := S170B_lemB_tw H star c hc (star l g) (c l g) g2
    rw [this]
  · intro hc
    refine ⟨hc.1, hc.2.1, fun l g g2 => ?_⟩
    rw [hc.2.2 l g g2]
    have := S170B_lemB_nest H star c hc (star l g) (c l g) g2
    rw [this]

/-- Lemma A: structure of a translation extension. -/
lemma S170B_lemA {G : Type u} [Group G] (H : Subgroup G) [H.Normal] {L : Type v}
    (act : (H × L) → G → (H × L)) (ha : TranslationExtension H act) (l : L) (h : H) (g : G) :
    act (1, l) ((h : G) * g) =
      (extensionCocycle act l g * ⟨g⁻¹ * (h : G) * g, S170B_conj H h g⟩, extensionBase act l g) := by
  have e : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
  rw [e, ← ha.1.2]
  have := ha.2 (act (1, l) g).1 ⟨g⁻¹ * (h : G) * g, S170B_conj H h g⟩ (act (1, l) g).2
  simp only [Prod.mk.eta] at this
  rw [this]; rfl

lemma S170B_lemA' {G : Type u} [Group G] (H : Subgroup G) {L : Type v}
    (act : (H × L) → G → (H × L)) (ha : TranslationExtension H act) (l : L) (h : H) (g : G) :
    act (h, l) g = act (1, l) ((h : G) * g) := by
  have := ha.2 1 h l
  rw [one_mul] at this
  rw [← this, ha.1.2]

end QAlgorithms.Papers.Independent.Renew46.P10

open QAlgorithms.Papers.Independent.Renew46.P10

universe u v

theorem solution
    {G : Type u} [Group G] (H : Subgroup G) [H.Normal] (L : Type v) :
    (∀ (act : (H × L) → G → (H × L)), TranslationExtension H act →
      TwistedCocycleData H (extensionBase act) (extensionCocycle act) ∧
      cocycleAction (extensionBase act) (extensionCocycle act) = act) ∧
    (∀ (star : L → G → L) (c : L → G → H), TwistedCocycleData H star c →
      TranslationExtension H (cocycleAction star c) ∧
      extensionBase (cocycleAction star c) = star ∧
      extensionCocycle (cocycleAction star c) = c ∧
      (∀ (l : L) (h : H) (g : G),
        (c l ((h : G) * g) : G) = (c l g : G) * g⁻¹ * (h : G) * g) ∧
      (∀ (l : L) (g g2 : G),
        (c (star l g) g2 : G) * g2⁻¹ * (c l g : G) * g2 =
          (c (star l g) ((c l g : G) * g2) : G))) ∧
    (∀ (star : L → G → L) (c : L → G → H),
      TwistedCocycleData H star c ↔ NestedCocycleData H star c) := by
  refine ⟨fun act ha => ?_, fun star c hc => ?_, S170B_tw_iff H⟩
  · -- part 1
    have hA := S170B_lemA H act ha
    have h1 : ∀ l (h : H), act (1, l) (h : G) = (h, l) := fun l h => by
      have := ha.2 1 h l; rwa [one_mul] at this
    -- base invariance and cocycle formula
    have hstar : ∀ l (h : H) g, extensionBase act l ((h : G) * g) = extensionBase act l g := by
      intro l h g; show (act (1, l) ((h : G) * g)).2 = _; rw [hA]
    have hcoc : ∀ l (h : H) g, (extensionCocycle act l ((h : G) * g) : G) =
        (extensionCocycle act l g : G) * g⁻¹ * (h : G) * g := by
      intro l h g; show ((act (1, l) ((h : G) * g)).1 : G) = _; rw [hA]
      simp [mul_assoc]
    refine ⟨⟨⟨⟨fun l => ?_, fun l g g2 => ?_⟩, fun l h => ?_⟩, fun l h => ?_, fun l g g2 => ?_⟩, ?_⟩
    · show (act (1, l) 1).2 = l; rw [ha.1.1]
    · show (act (1, (act (1, l) g).2) g2).2 = (act (1, l) (g * g2)).2
      rw [← ha.1.2]
      conv_rhs => rw [← Prod.mk.eta (p := act (1, l) g), S170B_lemA' H act ha]
      exact (hstar _ _ _).symm
    · show (act (1, l) (h : G)).2 = l; rw [h1]
    · show (act (1, l) (h : G)).1 = h; rw [h1]
    · show ((act (1, l) (g * g2)).1 : G) = _
      rw [← ha.1.2]
      conv_lhs => rw [← Prod.mk.eta (p := act (1, l) g), S170B_lemA' H act ha]
      exact hcoc _ _ _
    · funext p g
      obtain ⟨h, l⟩ := p
      rw [S170B_lemA' H act ha]
      simp only [cocycleAction]
      rw [hA]
      ext
      · simp only
        rw [hcoc]; simp [mul_assoc]
      · rfl
  · have hB := S170B_lemB_tw H star c hc
    have hn := (S170B_tw_iff H star c).1 hc
    refine ⟨⟨⟨fun p => ?_, fun p g g2 => ?_⟩, fun h r l => ?_⟩, rfl, ?_, hB, fun l g g2 => (hB _ _ _).symm⟩
    · obtain ⟨h, l⟩ := p
      simp only [cocycleAction, mul_one]
      rw [hc.2.1, hc.1.1.1]
    · obtain ⟨h, l⟩ := p
      simp only [cocycleAction]
      have hs : star l ((h : G) * g) = star l g := by
        rw [← hc.1.1.2, hc.1.2]
      rw [hc.1.1.2, ← hs, ← hn.2.2, mul_assoc]
    · simp only [cocycleAction]
      have := hc.2.1 l (h * r)
      rw [Subgroup.coe_mul] at this
      rw [this, hc.1.2]
    · funext l g
      simp [extensionCocycle, cocycleAction]
