-- Prove2me | solution 1 for TaoAnDCA.GlobalOpt.eq7_iff_eq8
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:15:56.629261+00:00
-- url     : https://prove2.me/submissions/31085810-9a61-4a7e-892b-3b998119a455

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

end PaperLemmas4
open TaoAnDCA.GlobalOpt PaperLemmas4

theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    (x ∈ effDom g ∧ ∀ y ∈ effDom (CondatPD.FinDim.conj h),
        g x + CondatPD.FinDim.conj g y ≤ h x + CondatPD.FinDim.conj h y) ↔
      ∀ ε : ℝ, 0 < ε → ∀ y : EuclideanSpace ℝ (Fin n),
        ((inner ℝ x y + ε : ℝ) : EReal) ≥ h x + CondatPD.FinDim.conj h y →
          ((inner ℝ x y + ε : ℝ) : EReal) ≥ g x + CondatPD.FinDim.conj g y := by
  constructor
  · rintro ⟨hxg, hineq⟩ ε hε y hy
    have hyfin : CondatPD.FinDim.conj h y ≠ ⊤ := by
      intro ht
      have hsum : h x + CondatPD.FinDim.conj h y = ⊤ := by
        rw [ht, EReal.add_top_of_ne_bot (hgh.h_mem.1 x)]
      rw [hsum] at hy
      exact EReal.coe_ne_top _ (top_le_iff.mp hy)
    exact (hineq y hyfin).trans hy
  · intro h8
    have hxf : h x ≠ ⊤ := hx
    obtain ⟨y0, hy0⟩ := conj_finite_point h hgh.h_mem
    have hchoose (y : EuclideanSpace ℝ (Fin n)) (hy : CondatPD.FinDim.conj h y ≠ ⊤) :
        g x + CondatPD.FinDim.conj g y ≤ h x + CondatPD.FinDim.conj h y := by
      lift h x to ℝ using ⟨hxf, hgh.h_mem.1 x⟩ with a ha
      lift CondatPD.FinDim.conj h y to ℝ using ⟨hy, conj_ne_bot h hgh.h_mem y⟩ with b hb
      have hfen := fenchel h hgh.h_mem x y
      rw [← ha, ← hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hfen
      by_contra hn
      have hlt : ((a + b : ℝ) : EReal) < g x + CondatPD.FinDim.conj g y := by
        simpa only [← ha, ← hb, ← EReal.coe_add, not_le] using hn
      obtain ⟨r, hr, hr'⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      have hrreal : a + b < r := EReal.coe_lt_coe_iff.mp hr
      have hp : 0 < r - inner ℝ x y := by linarith
      have hbound := h8 (r - inner ℝ x y) hp y (by
        change (a : EReal) + CondatPD.FinDim.conj h y ≤
          ((inner ℝ x y + (r - inner ℝ x y) : ℝ) : EReal)
        rw [← hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
        linarith)
      have he : inner ℝ x y + (r - inner ℝ x y) = r := by ring
      rw [he] at hbound
      exact (not_le_of_gt hr') hbound
    have hbound := hchoose y0 hy0
    have hxg : g x ≠ ⊤ := by
      intro ht
      rw [ht, EReal.top_add_of_ne_bot (conj_ne_bot g hgh.g_mem y0)] at hbound
      have hn : h x + CondatPD.FinDim.conj h y0 ≠ ⊤ := EReal.add_ne_top hxf hy0
      exact hn (top_le_iff.mp hbound)
    exact ⟨hxg, fun y hy => hchoose y hy⟩

#print axioms solution
