-- Prove2me | solution 1 for TaoAnDCA.TRS.subdiff_conj_eq_argmin
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:39:17.135997+00:00
-- url     : https://prove2.me/submissions/7f02b13f-b4e9-4572-a697-ad4ef61267ad

import Mathlib
import Definitions.Def_TaoAnDCA_GlobalOpt_Setting

open TaoAnDCA.GlobalOpt
open InnerProductSpace

namespace PaperLemmas4

variable {n : ℕ}
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma conj_ne_bot (f : E n → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (y : E n) :
    CondatPD.FinDim.conj f y ≠ ⊥ := by
  obtain ⟨z, hz⟩ := hf.2.1
  lift f z to ℝ using ⟨hz, hf.1 z⟩ with a ha
  have hb := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - f z) z
  rw [← ha, ← EReal.coe_sub] at hb
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb

lemma epi_closed (f : E n → EReal) (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E n × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  have heq : {p : E n × ℝ | f p.1 ≤ (p.2 : EReal)} =
      (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E n × EReal | f p.1 ≤ p.2} := rfl
  rw [heq]
  exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)

lemma minorant (f : E n → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) :
    ∃ (l : StrongDual ℝ (E n)) (b : ℝ), ∀ y (c : ℝ), f y = c → l y + b ≤ c := by
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hnot : (y0, c0 - 1) ∉ {p : E n × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, ← hc0, EReal.coe_le_coe_iff, not_le]; linarith
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hf.2.2.2
    (epi_closed f hf.2.2.1) hnot
  let φ : StrongDual ℝ (E n) := ℓ.comp (ContinuousLinearMap.inl ℝ (E n) ℝ)
  let β : ℝ := ℓ (0, 1)
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E n × ℝ) + r • ((0, 1) : E n × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]; rfl
  have h0 := hl2 (y0, c0) (by simp [← hc0])
  rw [hℓ] at hl1 h0
  have hβ : 0 < β := by nlinarith
  refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_⟩
  have ht := hl2 (y, c) (by simp [hc])
  rw [hℓ] at ht
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  have hi : 0 < β⁻¹ := inv_pos.2 hβ
  have ht' := mul_lt_mul_of_pos_left ht hi
  have he : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
  linarith

lemma conj_finite_point (f : E n → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) :
    ∃ y, CondatPD.FinDim.conj f y ≠ ⊤ := by
  obtain ⟨l, b, hl⟩ := minorant f hf
  let y := (toDual ℝ (E n)).symm l
  refine ⟨y, ne_top_of_le_ne_top (EReal.coe_ne_top (-b)) ?_⟩
  apply iSup_le
  intro z
  rw [toDual_symm_apply]
  by_cases hz : f z = ⊤
  · simp [hz]
  lift f z to ℝ using ⟨hz, hf.1 z⟩ with c hc
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  have := hl z c hc.symm
  linarith

lemma fenchel (f : E n → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (x y : E n) :
    ((inner ℝ x y : ℝ) : EReal) ≤ f x + CondatPD.FinDim.conj f y := by
  by_cases hx : f x = ⊤
  · rw [hx, EReal.top_add_of_ne_bot (conj_ne_bot f hf y)]; exact le_top
  lift f x to ℝ using ⟨hx, hf.1 x⟩ with a ha
  have ht := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - f z) x
  rw [← ha, real_inner_comm, ← EReal.coe_sub] at ht
  calc ((inner ℝ x y : ℝ) : EReal) = (a : EReal) + ((inner ℝ x y - a : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
    _ ≤ _ := add_le_add le_rfl ht

lemma separation (f : E n → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (x : E n) (z : ℝ) (hz : (z : EReal) < f x) :
    ∃ (l : StrongDual ℝ (E n)) (b : ℝ),
      (∀ y (c : ℝ), f y = c → l y + b ≤ c) ∧ z < l x + b := by
  obtain ⟨l0, b0, hl0⟩ := minorant f hf
  have hnot : (x, z) ∉ {p : E n × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact not_le.mpr hz
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hf.2.2.2
    (epi_closed f hf.2.2.1) hnot
  let φ : StrongDual ℝ (E n) := ℓ.comp (ContinuousLinearMap.inl ℝ (E n) ℝ)
  let β : ℝ := ℓ (0, 1)
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E n × ℝ) + r • ((0, 1) : E n × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]; rfl
  rw [hℓ] at hl1
  have hC : ∀ y (c : ℝ), f y = c → ∀ r, c ≤ r → u < φ y + r * β := by
    intro y c hc r hr
    have ht := hl2 (y, r) (by simp [hc, hr])
    rwa [hℓ] at ht
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    let r := max c0 ((u - φ y0) / β)
    have h1 := hC y0 c0 hc0.symm r (le_max_left _ _)
    have h2 : (u - φ y0) / β ≤ r := le_max_right _ _
    rw [div_le_iff_of_neg hneg] at h2
    linarith
  rcases eq_or_lt_of_le hβ0 with hβzero | hβpos
  · have hβ : β = 0 := hβzero.symm
    rw [hβ, mul_zero, add_zero] at hl1
    have hdom : ∀ y (c : ℝ), f y = c → u < φ y := by
      intro y c hc
      have ht := hC y c hc c le_rfl
      rwa [hβ, mul_zero, add_zero] at ht
    have hpos : 0 < u - φ x := by linarith
    let lam := max 0 ((z - l0 x - b0) / (u - φ x)) + 1
    have hlam0 : 0 < lam := by dsimp [lam]; positivity
    refine ⟨l0 - lam • φ, b0 + lam * u, fun y c hc => ?_, ?_⟩
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := hl0 y c hc
      have := hdom y c hc
      nlinarith
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 := le_max_right 0 ((z - l0 x - b0) / (u - φ x))
      rw [div_le_iff₀ hpos] at h1
      have h2 : lam * (u - φ x) =
          max 0 ((z - l0 x - b0) / (u - φ x)) * (u - φ x) + (u - φ x) := by
        dsimp [lam]; ring
      nlinarith
  · refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_, ?_⟩
    · have ht := hC y c hc c le_rfl
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have ht' := mul_lt_mul_of_pos_left ht hi
      have he : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
      linarith
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have ht' := mul_lt_mul_of_pos_left hl1 hi
      have he : β⁻¹ * (φ x + z * β) = β⁻¹ * φ x + z := by field_simp
      linarith

lemma biconj (f : E n → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) (x : E n) :
    CondatPD.FinDim.conj (CondatPD.FinDim.conj f) x = f x := by
  apply le_antisymm
  · apply iSup_le
    intro y
    by_cases hx : f x = ⊤
    · rw [hx]; exact le_top
    lift f x to ℝ using ⟨hx, hf.1 x⟩ with a ha
    have ht := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - f z) x
    rw [← ha, real_inner_comm, ← EReal.coe_sub] at ht
    calc ((inner ℝ x y : ℝ) : EReal) - CondatPD.FinDim.conj f y ≤
        ((inner ℝ x y : ℝ) : EReal) - ((inner ℝ x y - a : ℝ) : EReal) :=
          EReal.sub_le_sub le_rfl ht
      _ = (a : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
  · by_contra hn
    have hlt := lt_of_not_ge hn
    obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    obtain ⟨l, b, hl, hlz⟩ := separation f hf x z hz2
    let y := (toDual ℝ (E n)).symm l
    have hc : CondatPD.FinDim.conj f y ≤ ((-b : ℝ) : EReal) := by
      apply iSup_le
      intro w
      rw [toDual_symm_apply]
      by_cases hw : f w = ⊤
      · simp [hw]
      lift f w to ℝ using ⟨hw, hf.1 w⟩ with c hc
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := hl w c hc.symm
      linarith
    have ht := le_iSup (fun y => ((inner ℝ x y : ℝ) : EReal) - CondatPD.FinDim.conj f y) y
    have he : inner ℝ x y = l x := by rw [real_inner_comm, toDual_symm_apply]
    rw [he] at ht
    have hb : ((l x + b : ℝ) : EReal) ≤ CondatPD.FinDim.conj (CondatPD.FinDim.conj f) x := by
      calc ((l x + b : ℝ) : EReal) = ((l x : ℝ) : EReal) - ((-b : ℝ) : EReal) := by
            rw [← EReal.coe_sub]; congr 1; ring
        _ ≤ ((l x : ℝ) : EReal) - CondatPD.FinDim.conj f y := EReal.sub_le_sub le_rfl hc
        _ ≤ _ := ht
    have hbad := hb.trans_lt hz1
    rw [EReal.coe_lt_coe_iff] at hbad
    linarith


end PaperLemmas4

open TaoAnDCA.GlobalOpt InnerProductSpace PaperLemmas4

theorem solution {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g) (y : EuclideanSpace ℝ (Fin n)) :
    TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) y =
      {x | g x ≠ ⊤ ∧ ∀ z, g x - ((inner ℝ x y : ℝ) : EReal) ≤ g z - ((inner ℝ z y : ℝ) : EReal)} := by
  ext x
  change InertialFB.IFB.IsSubgradient (CondatPD.FinDim.conj g) y x ↔ _
  constructor
  · rintro ⟨hy, hs⟩
    lift CondatPD.FinDim.conj g y to ℝ using ⟨hy, conj_ne_bot g hg y⟩ with b hb
    have hbound : g x ≤ ((inner ℝ x y - b : ℝ) : EReal) := by
      rw [← biconj g hg x]
      apply iSup_le
      intro v
      have h := hs v
      rw [← EReal.coe_add] at h
      calc
        ((inner ℝ x v : ℝ) : EReal) - CondatPD.FinDim.conj g v ≤
            ((inner ℝ x v : ℝ) : EReal) - ((b + inner ℝ x (v - y) : ℝ) : EReal) :=
          EReal.sub_le_sub le_rfl h
        _ = ((inner ℝ x y - b : ℝ) : EReal) := by
          rw [← EReal.coe_sub, inner_sub_right]; congr 1; ring
    have hx : g x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound
    refine ⟨hx, ?_⟩
    lift g x to ℝ using ⟨hx, hg.1 x⟩ with a ha
    have hf := fenchel g hg x y
    rw [← ha, ← hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hf
    rw [EReal.coe_le_coe_iff] at hbound
    have he : a + b = inner ℝ x y := by linarith
    intro z
    by_cases hz : g z = ⊤
    · simp [hz]
    lift g z to ℝ using ⟨hz, hg.1 z⟩ with c hc
    have hfz := fenchel g hg z y
    rw [← hc, ← hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hfz
    simp only [← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · rintro ⟨hx, hmin⟩
    lift g x to ℝ using ⟨hx, hg.1 x⟩ with a ha
    have he : CondatPD.FinDim.conj g y = ((inner ℝ x y - a : ℝ) : EReal) := by
      apply le_antisymm
      · apply iSup_le
        intro z
        by_cases hz : g z = ⊤
        · simp [hz]
        lift g z to ℝ using ⟨hz, hg.1 z⟩ with c hc
        have hm := hmin z
        rw [← hc, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hm
        simp only [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have hij : inner ℝ y z = inner ℝ z y := real_inner_comm _ _
        rw [hij]
        linarith
      · have h := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - g z) x
        have hij : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
        simpa only [← ha, hij, ← EReal.coe_sub, CondatPD.FinDim.conj] using h
    refine ⟨by rw [he]; exact EReal.coe_ne_top _, ?_⟩
    intro v
    have h := le_iSup (fun z => ((inner ℝ v z : ℝ) : EReal) - g z) x
    rw [he, ← EReal.coe_add]
    have hij : inner ℝ v x = inner ℝ x v := real_inner_comm _ _
    rw [← ha, hij, ← EReal.coe_sub] at h
    convert h using 1
    · congr 1
      rw [inner_sub_right]
      ring
    · rfl

#print axioms solution
