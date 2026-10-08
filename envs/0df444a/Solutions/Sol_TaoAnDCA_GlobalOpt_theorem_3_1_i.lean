-- Prove2me | solution 1 for TaoAnDCA.GlobalOpt.theorem_3_1_i
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:21:38.67429+00:00
-- url     : https://prove2.me/submissions/4eec307f-3f9b-47c8-b690-bce68a2a4f4f

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

lemma lower_bound_iff (g h : E n → EReal) (hgh : DCStanding g h) (r : ℝ) :
    (∀ x, (r : EReal) ≤ dcSub g h x) ↔
      ∀ y, (r : EReal) ≤ dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y := by
  constructor
  · intro hp y
    by_cases hy : CondatPD.FinDim.conj h y = ⊤
    · simp only [dcSub, hy, ite_true]; exact le_top
    have hgy := hgh.dom_conj_h_sub hy
    lift CondatPD.FinDim.conj h y to ℝ using ⟨hy, conj_ne_bot h hgh.h_mem y⟩ with b hb
    lift CondatPD.FinDim.conj g y to ℝ using ⟨hgy, conj_ne_bot g hgh.g_mem y⟩ with a ha
    have hbound : CondatPD.FinDim.conj g y ≤ ((b - r : ℝ) : EReal) := by
      apply iSup_le
      intro x
      by_cases hx : g x = ⊤
      · simp [hx]
      have hhx := hgh.dom_g_sub hx
      have hp' := hp x
      simp only [dcSub, if_neg hx] at hp'
      have hf := fenchel h hgh.h_mem x y
      lift g x to ℝ using ⟨hx, hgh.g_mem.1 x⟩ with c hc
      lift h x to ℝ using ⟨hhx, hgh.h_mem.1 x⟩ with d hd
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hp'
      rw [← hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at hf
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have he : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
      linarith
    rw [← ha, EReal.coe_le_coe_iff] at hbound
    simp only [dcSub, if_neg hy, ← ha, ← hb, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · intro hd x
    by_cases hx : g x = ⊤
    · simp only [dcSub, hx, ite_true]; exact le_top
    have hhx := hgh.dom_g_sub hx
    lift g x to ℝ using ⟨hx, hgh.g_mem.1 x⟩ with c hc
    lift h x to ℝ using ⟨hhx, hgh.h_mem.1 x⟩ with d hd'
    have hbound : CondatPD.FinDim.conj (CondatPD.FinDim.conj h) x ≤ ((c - r : ℝ) : EReal) := by
      apply iSup_le
      intro y
      by_cases hy : CondatPD.FinDim.conj h y = ⊤
      · simp [hy]
      have hgy := hgh.dom_conj_h_sub hy
      have hd'' := hd y
      simp only [dcSub, if_neg hy] at hd''
      have hf := fenchel g hgh.g_mem x y
      lift CondatPD.FinDim.conj h y to ℝ using ⟨hy, conj_ne_bot h hgh.h_mem y⟩ with b hb
      lift CondatPD.FinDim.conj g y to ℝ using ⟨hgy, conj_ne_bot g hgh.g_mem y⟩ with a ha
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hd''
      rw [← hc, ← EReal.coe_add, EReal.coe_le_coe_iff] at hf
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
    rw [biconj h hgh.h_mem x, ← hd', EReal.coe_le_coe_iff] at hbound
    simp only [dcSub, if_neg hx, ← hc, ← hd', ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

lemma duality (g h : E n → EReal) (hgh : DCStanding g h) :
    primalValue g h = ⨅ y, dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨r, hr, hr'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have hp : ∀ x, (r : EReal) ≤ dcSub g h x := by
      intro x
      exact hr'.le.trans (iInf_le (fun x => dcSub g h x) x)
    have hd := (lower_bound_iff g h hgh r).mp hp
    exact (not_le_of_gt hr) (le_iInf hd)
  · by_contra hn
    obtain ⟨r, hr, hr'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hn)
    have hd : ∀ y, (r : EReal) ≤ dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y := by
      intro y
      exact hr'.le.trans (iInf_le _ y)
    have hp := (lower_bound_iff g h hgh r).mpr hd
    exact (not_le_of_gt hr) (le_iInf hp)

end PaperLemmas4

open TaoAnDCA.GlobalOpt PaperLemmas4

private theorem paper_mem {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) :
    (x ∈ primalSol g h ↔ x ∈ effDom g ∧
      ∀ y ∈ effDom (CondatPD.FinDim.conj h),
        dcSub g h x ≤ dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) ∧
    (x ∈ primalSol g h ↔ x ∈ effDom g ∧
      ∀ y ∈ effDom (CondatPD.FinDim.conj h),
        g x + CondatPD.FinDim.conj g y ≤ h x + CondatPD.FinDim.conj h y) := by
  have hdom : x ∈ primalSol g h → x ∈ effDom g := by
    intro hp
    obtain ⟨z, hz⟩ := hgh.g_mem.2.1
    have hhz := hgh.dom_g_sub hz
    have hmin := hp z
    by_contra hx
    have hx : g x = ⊤ := Classical.not_not.mp hx
    simp only [dcSub, hx, ite_true, if_neg hz] at hmin
    have hfinite : g z - h z ≠ ⊤ := by
      lift g z to ℝ using ⟨hz, hgh.g_mem.1 z⟩ with a ha
      lift h z to ℝ using ⟨hhz, hgh.h_mem.1 z⟩ with b hb
      rw [← EReal.coe_sub]
      exact EReal.coe_ne_top _
    exact hfinite (top_le_iff.mp hmin)
  have hfirst :
      x ∈ primalSol g h ↔ x ∈ effDom g ∧
        ∀ y ∈ effDom (CondatPD.FinDim.conj h),
          dcSub g h x ≤ dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y := by
    constructor
    · intro hp
      refine ⟨hdom hp, ?_⟩
      have hv : dcSub g h x ≤ primalValue g h := le_iInf hp
      rw [duality g h hgh] at hv
      intro y hy
      exact hv.trans (iInf_le _ y)
    · rintro ⟨hx, hd⟩
      have hall : ∀ y, dcSub g h x ≤
          dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y := by
        intro y
        by_cases hy : CondatPD.FinDim.conj h y = ⊤
        · simp only [dcSub, hy, ite_true]; exact le_top
        exact hd y hy
      have hv := le_iInf hall
      rw [← duality g h hgh] at hv
      intro z
      exact hv.trans (iInf_le _ z)
  refine ⟨hfirst, hfirst.trans ?_⟩
  apply and_congr_right
  intro hx
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  have hhx := hgh.dom_g_sub hx
  have hgy := hgh.dom_conj_h_sub hy
  change g x ≠ ⊤ at hx
  change h x ≠ ⊤ at hhx
  change CondatPD.FinDim.conj h y ≠ ⊤ at hy
  change CondatPD.FinDim.conj g y ≠ ⊤ at hgy
  simp only [dcSub, if_neg hx, if_neg hy]
  lift g x to ℝ using ⟨hx, hgh.g_mem.1 x⟩ with a ha
  lift h x to ℝ using ⟨hhx, hgh.h_mem.1 x⟩ with b hb
  lift CondatPD.FinDim.conj h y to ℝ using ⟨hy, conj_ne_bot h hgh.h_mem y⟩ with c hc
  lift CondatPD.FinDim.conj g y to ℝ using ⟨hgy, conj_ne_bot g hgh.g_mem y⟩ with d hd
  simp only [← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff]
  constructor <;> intro h <;> linarith


private theorem paper_eq7 {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
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





open TaoAnDCA.GlobalOpt

private lemma conj_ne_bot {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (y : EuclideanSpace ℝ (Fin n)) : CondatPD.FinDim.conj f y ≠ ⊥ := by
  obtain ⟨z, hz⟩ := hf.2.1
  lift f z to ℝ using ⟨hz, hf.1 z⟩ with a ha
  have hb := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - f z) z
  rw [← ha, ← EReal.coe_sub] at hb
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb

private lemma rearrange (a b : ℝ) (v : EReal) :
    (a : EReal) + v ≤ (b : EReal) ↔ v ≤ ((b - a : ℝ) : EReal) := by
  cases v with
  | bot => simp only [EReal.add_bot, bot_le, true_iff]
  | top => simp only [EReal.coe_add_top, top_le_iff, EReal.coe_ne_top, false_iff,
      ← EReal.coe_sub, EReal.coe_ne_top, not_false_eq_true]
  | coe r =>
    simp only [← EReal.coe_add, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

private lemma eps_iff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (x y : EuclideanSpace ℝ (Fin n)) (ε : ℝ) :
    y ∈ epsSubdiff f ε x ↔
      f x + CondatPD.FinDim.conj f y ≤ ((inner ℝ x y + ε : ℝ) : EReal) := by
  by_cases hx : f x = ⊤
  · simp only [epsSubdiff, Set.mem_setOf_eq, hx, ne_eq, not_true_eq_false, false_and,
      EReal.top_add_of_ne_bot (PaperLemmas4.conj_ne_bot f hf y), top_le_iff, EReal.coe_ne_top]
  lift f x to ℝ using ⟨hx, hf.1 x⟩ with a ha
  simp only [epsSubdiff, Set.mem_setOf_eq, ← ha, ne_eq, EReal.coe_ne_top, not_false_eq_true,
    true_and]
  rw [rearrange a (inner ℝ x y + ε), CondatPD.FinDim.conj, iSup_le_iff]
  apply forall_congr'
  intro z
  cases hz : f z with
  | bot => exact (hf.1 z hz).elim
  | top => simp [EReal.sub_top]
  | coe b =>
    simp only [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [inner_sub_left, real_inner_comm y z]
    constructor <;> intro h <;> linarith

private theorem paper_eps {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    (∀ ε : ℝ, 0 < ε → epsSubdiff h ε x ⊆ epsSubdiff g ε x) ↔
      ∀ ε : ℝ, 0 < ε → ∀ y : EuclideanSpace ℝ (Fin n),
        ((inner ℝ x y + ε : ℝ) : EReal) ≥ h x + CondatPD.FinDim.conj h y →
          ((inner ℝ x y + ε : ℝ) : EReal) ≥ g x + CondatPD.FinDim.conj g y := by
  simp only [Set.subset_def, eps_iff g hgh.g_mem, eps_iff h hgh.h_mem]


theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : DCStanding g h) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ effDom h) :
    x ∈ primalSol g h ↔ ∀ ε : ℝ, 0 < ε → epsSubdiff h ε x ⊆ epsSubdiff g ε x := by
  exact ((paper_mem g h hgh x).2.trans (paper_eq7 g h hgh x hx)).trans
    (paper_eps g h hgh x hx).symm

#print axioms solution
