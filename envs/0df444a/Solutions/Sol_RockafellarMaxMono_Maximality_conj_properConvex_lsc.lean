-- Prove2me | solution 1 for RockafellarMaxMono.Maximality.conj_properConvex_lsc
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:17:31.500486+00:00
-- url     : https://prove2.me/submissions/0bb49361-6df0-42af-828f-2b9d00c2709e

import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj



namespace RockafellarMaxMono.Cyclic

section Biconj
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cf_minorant (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), ∀ y (c : ℝ), f y = c → l y + b ≤ c := by
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := by
    have : C = (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := by
      ext p; simp [hC]
    rw [this]
    exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hCv : Convex ℝ C := by
    rintro ⟨y1, r1⟩ h1 ⟨y2, r2⟩ h2 s t hs ht hst
    simp only [hC, Set.mem_setOf_eq] at h1 h2 ⊢
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      simpa using h1
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · subst hs0
      have : t = 1 := by linarith
      subst this
      simpa using h2
    have hts : s = 1 - t := by linarith
    subst hts
    have hne1 : f y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hne2 : f y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
    lift f y1 to ℝ using ⟨hne1, hf.1 y1⟩ with c1
    lift f y2 to ℝ using ⟨hne2, hf.1 y2⟩ with c2
    rw [EReal.coe_le_coe_iff] at h1 h2
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine hcv.trans ?_
    rw [EReal.coe_le_coe_iff]
    nlinarith
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hnot : (y0, c0 - 1) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, ← hc0, EReal.coe_le_coe_iff, not_le]; linarith
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have h0 := hl2 (y0, c0) (by simp [hC, ← hc0])
  rw [hℓ] at hl1 h0
  have hβ : 0 < β := by nlinarith
  refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_⟩
  have := hl2 (y, c) (by simp [hC, hc])
  rw [hℓ] at this
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  have e : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have hi : 0 < β⁻¹ := inv_pos.2 hβ
  have := mul_lt_mul_of_pos_left this hi
  have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
  linarith


lemma bc_sep (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x : E) (z : ℝ) (hz : (z : EReal) < f x) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), (∀ y (c : ℝ), f y = c → l y + b ≤ c) ∧ z < l x + b := by
  obtain ⟨l0, b0, hl0⟩ := cf_minorant f hf hlsc
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := by
    have : C = (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := by
      ext p; simp [hC]
    rw [this]
    exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hCv : Convex ℝ C := by
    rintro ⟨y1, r1⟩ h1 ⟨y2, r2⟩ h2 s t hs ht hst
    simp only [hC, Set.mem_setOf_eq] at h1 h2 ⊢
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      simpa using h1
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · subst hs0
      have : t = 1 := by linarith
      subst this
      simpa using h2
    have hts : s = 1 - t := by linarith
    subst hts
    have hne1 : f y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hne2 : f y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
    lift f y1 to ℝ using ⟨hne1, hf.1 y1⟩ with c1
    lift f y2 to ℝ using ⟨hne2, hf.1 y2⟩ with c2
    rw [EReal.coe_le_coe_iff] at h1 h2
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine hcv.trans ?_
    rw [EReal.coe_le_coe_iff]
    nlinarith
  have hnot : (x, z) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, not_le]; exact hz
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  rw [hℓ] at hl1
  have hC' : ∀ y (c : ℝ), f y = c → ∀ r, c ≤ r → u < φ y + r * β := by
    intro y c hc r hr
    have := hl2 (y, r) (by simp [hC, hc, hr])
    rwa [hℓ] at this
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    set r := max c0 ((u - φ y0) / β)
    have h1 := hC' y0 c0 hc0.symm r (le_max_left _ _)
    have h2 : (u - φ y0) / β ≤ r := le_max_right _ _
    rw [div_le_iff_of_neg hneg] at h2
    linarith
  rcases eq_or_lt_of_le hβ0 with hβ0 | hβpos
  · -- vertical hyperplane
    have hβ' : β = 0 := hβ0.symm
    rw [hβ', mul_zero, add_zero] at hl1
    have hdom : ∀ y (c : ℝ), f y = c → u < φ y := by
      intro y c hc
      have := hC' y c hc c le_rfl
      rwa [hβ', mul_zero, add_zero] at this
    have hpos : 0 < u - φ x := by linarith
    set lam := max 0 ((z - l0 x - b0) / (u - φ x)) + 1 with hlam
    have hlam0 : 0 < lam := by positivity
    refine ⟨l0 - lam • φ, b0 + lam * u, fun y c hc => ?_, ?_⟩
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := hl0 y c hc
      have := hdom y c hc
      nlinarith
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 : (z - l0 x - b0) / (u - φ x) ≤ max 0 ((z - l0 x - b0) / (u - φ x)) := le_max_right _ _
      rw [div_le_iff₀ hpos] at h1
      have h2 : lam * (u - φ x) = max 0 ((z - l0 x - b0) / (u - φ x)) * (u - φ x) + (u - φ x) := by
        rw [hlam]; ring
      nlinarith
  · refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_, ?_⟩
    · have := hC' y c hc c le_rfl
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have := mul_lt_mul_of_pos_left this hi
      have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
      linarith
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have := mul_lt_mul_of_pos_left hl1 hi
      have e2 : β⁻¹ * (φ x + z * β) = β⁻¹ * φ x + z := by field_simp
      linarith

theorem biconj_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.conj (Shared.conj f) (NormedSpace.inclusionInDoubleDual ℝ E x) = f x := by
  intro x
  unfold Shared.conj
  simp only [NormedSpace.dual_def]
  apply le_antisymm
  · apply iSup_le
    intro x'
    rcases eq_or_ne (f x) ⊤ with hx | hx
    · rw [hx]; exact le_top
    lift f x to ℝ using ⟨hx, hf.1 x⟩ with a ha
    have h1 : ((x' x - a : ℝ) : EReal) ≤ ⨆ y, ((x' y : ℝ) : EReal) - f y := by
      have := le_iSup (fun y => ((x' y : ℝ) : EReal) - f y) x
      rwa [← ha, ← EReal.coe_sub] at this
    calc ((x' x : ℝ) : EReal) - ⨆ y, ((x' y : ℝ) : EReal) - f y
        ≤ ((x' x : ℝ) : EReal) - ((x' x - a : ℝ) : EReal) := EReal.sub_le_sub le_rfl h1
      _ = (a : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
  · by_contra hlt
    push_neg at hlt
    obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨l, b, hl, hlz⟩ := bc_sep f hf hlsc x z hz2
    have hconj : (⨆ y, ((l y : ℝ) : EReal) - f y) ≤ ((-b : ℝ) : EReal) := by
      apply iSup_le
      intro y
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy, EReal.sub_top]; exact bot_le
      lift f y to ℝ using ⟨hy, hf.1 y⟩ with c hc
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := hl y c hc.symm
      linarith
    have h2 : ((l x + b : ℝ) : EReal) ≤ ((l x : ℝ) : EReal) - ⨆ y, ((l y : ℝ) : EReal) - f y := by
      calc ((l x + b : ℝ) : EReal) = ((l x : ℝ) : EReal) - ((-b : ℝ) : EReal) := by
            rw [← EReal.coe_sub]; congr 1; ring
        _ ≤ _ := EReal.sub_le_sub le_rfl hconj
    have h3 := le_iSup (fun x' : StrongDual ℝ E =>
      ((x' x : ℝ) : EReal) - ⨆ y, ((x' y : ℝ) : EReal) - f y) l
    have h4 := lt_of_le_of_lt (h2.trans h3) hz1
    rw [EReal.coe_lt_coe_iff] at h4
    linarith

end Biconj
end RockafellarMaxMono.Cyclic


namespace RockProof
open RockafellarMaxMono
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem conj_ne_bot (f : E → EReal) (hf : Shared.ProperConvex f) (y : StrongDual ℝ E) :
    Shared.conj f y ≠ ⊥ := by
  obtain ⟨x,hx⟩ := hf.2.1
  have h : ((y x : ℝ) : EReal)-f x ≤ Shared.conj f y :=
    le_iSup (fun u => ((y u : ℝ) : EReal)-f u) x
  rw [← EReal.coe_toReal hx (hf.1 x),← EReal.coe_sub] at h
  intro hy
  rw [hy,le_bot_iff] at h
  exact EReal.coe_ne_bot _ h

theorem conj_proper (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    Shared.ProperConvex (Shared.conj f) := by
  refine ⟨conj_ne_bot f hf,?_,?_⟩
  · obtain ⟨l,b,hl⟩ := RockafellarMaxMono.Cyclic.cf_minorant f hf hlsc
    have hbound : Shared.conj f l ≤ ((-b : ℝ) : EReal) := by
      apply iSup_le
      intro x
      by_cases hx : f x = ⊤
      · simp [hx]
      · have he := (EReal.coe_toReal hx (hf.1 x)).symm
        have h := hl x (f x).toReal he
        rw [he,← EReal.coe_sub,EReal.coe_le_coe_iff]
        linarith
    exact ⟨l,ne_top_of_le_ne_top (EReal.coe_ne_top _) hbound⟩
  · intro x y t ht ht1
    apply iSup_le
    intro u
    by_cases hu : f u = ⊤
    · simp [hu]
    · have he := (EReal.coe_toReal hu (hf.1 u)).symm
      have h1 : ((x u : ℝ) : EReal)-f u ≤ Shared.conj f x :=
        le_iSup (fun v => ((x v : ℝ) : EReal)-f v) u
      have h2 : ((y u : ℝ) : EReal)-f u ≤ Shared.conj f y :=
        le_iSup (fun v => ((y v : ℝ) : EReal)-f v) u
      have ha : (0 : EReal) ≤ ((1-t : ℝ) : EReal) := EReal.coe_nonneg.mpr (by linarith)
      have hb : (0 : EReal) ≤ ((t : ℝ) : EReal) := EReal.coe_nonneg.mpr ht.le
      have hh := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
      rw [he,← EReal.coe_sub,← EReal.coe_sub,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add] at hh
      rw [he,← EReal.coe_sub]
      convert hh using 1
      congr 1
      simp only [add_apply,smul_apply,smul_eq_mul]
      ring

theorem conj_weak_lsc (f : E → EReal) (hf : Shared.ProperConvex f) :
    LowerSemicontinuous (fun w : WeakDual ℝ E => Shared.conj f (StrongDual.toWeakDual.symm w)) := by
  apply lowerSemicontinuous_iSup
  intro x
  by_cases hx : f x = ⊤
  · simp only [hx,EReal.sub_top]
    exact continuous_const.lowerSemicontinuous
  · have he := (EReal.coe_toReal hx (hf.1 x)).symm
    have he' : (fun w : WeakDual ℝ E => (((StrongDual.toWeakDual.symm w) x : ℝ) : EReal)-f x) =
        fun w => ((w x-(f x).toReal : ℝ) : EReal) := by
      funext w
      rw [he,← EReal.coe_sub]
      simp
    rw [he']
    exact (continuous_coe_real_ereal.comp ((WeakDual.eval_continuous x).sub continuous_const)).lowerSemicontinuous

end RockProof

open RockafellarMaxMono
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (fun w : WeakDual ℝ E => Shared.conj f (StrongDual.toWeakDual.symm w)) ∧
      LowerSemicontinuous (Shared.conj f) ∧ Shared.ProperConvex (Shared.conj f) := by
  have h := RockProof.conj_weak_lsc f hf
  refine ⟨h,?_,RockProof.conj_proper f hf hlsc⟩
  simpa only [Function.comp_def,LinearEquiv.symm_apply_apply] using
    h.comp NormedSpace.Dual.toWeakDual_continuous
