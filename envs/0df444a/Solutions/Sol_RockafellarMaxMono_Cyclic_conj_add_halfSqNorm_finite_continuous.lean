-- Prove2me | solution 1 for RockafellarMaxMono.Cyclic.conj_add_halfSqNorm_finite_continuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:03:19.617153+00:00
-- url     : https://prove2.me/submissions/12ee9c00-0098-4704-9573-5395b3034c97

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_HalfSqNorm



namespace RockafellarMaxMono.Cyclic

section ConjFin
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

/-- the real set whose sup is the conjugate -/
def cfS (f : E → EReal) (x' : StrongDual ℝ E) : Set ℝ :=
  {t | ∃ y : E, ∃ c : ℝ, f y = c ∧ t = x' y - c - ‖y‖ ^ 2 / 2}

lemma cf_le_norm (x' : StrongDual ℝ E) (y : E) : x' y ≤ ‖x'‖ * ‖y‖ :=
  (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using x'.le_opNorm y)

lemma cfS_bdd {f : E → EReal} (l : StrongDual ℝ E) (b : ℝ) (hl : ∀ y (c : ℝ), f y = c → l y + b ≤ c)
    (x' : StrongDual ℝ E) {t : ℝ} (ht : t ∈ cfS f x') :
    ∃ y : E, t ≤ (‖x'‖ + ‖l‖) * ‖y‖ - b - ‖y‖ ^ 2 / 2 := by
  obtain ⟨y, c, hc, rfl⟩ := ht
  refine ⟨y, ?_⟩
  have h1 := cf_le_norm x' y
  have h2 := cf_le_norm (-l) y
  rw [norm_neg, ContinuousLinearMap.neg_apply] at h2
  have := hl y c hc
  nlinarith

lemma cfS_bddAbove {f : E → EReal} (l : StrongDual ℝ E) (b : ℝ) (hl : ∀ y (c : ℝ), f y = c → l y + b ≤ c)
    (x' : StrongDual ℝ E) : BddAbove (cfS f x') := by
  refine ⟨(‖x'‖ + ‖l‖) ^ 2 / 2 - b, fun t ht => ?_⟩
  obtain ⟨y, hy⟩ := cfS_bdd l b hl x' ht
  nlinarith [sq_nonneg (‖x'‖ + ‖l‖ - ‖y‖)]

theorem conjfin_core {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by
  obtain ⟨l, b, hl⟩ := cf_minorant f hf hlsc
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hne : ∀ x', (cfS f x').Nonempty := fun x' => ⟨_, y0, c0, hc0.symm, rfl⟩
  have hbdd := cfS_bddAbove l b hl
  set H : StrongDual ℝ E → ℝ := fun x' => sSup (cfS f x') with hH
  -- Lipschitz on balls
  have hlip : ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, 0 < M ∧ ∀ x' x'' : StrongDual ℝ E, ‖x'‖ ≤ R → ‖x''‖ ≤ R →
      H x' - H x'' ≤ M * ‖x' - x''‖ := by
    intro R hR
    set N := ‖l‖
    set K := R * ‖y0‖ + |c0| + ‖y0‖ ^ 2 / 2 + 1
    refine ⟨2 * (R + N) + 2 * |K - b| + 1, by positivity, fun x' x'' h1 h2 => ?_⟩
    apply le_of_forall_pos_lt_add
    intro ε hε
    set ε' := min ε 1
    have hε' : 0 < ε' := lt_min hε one_pos
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_lt_csSup (hne x') (show H x' - ε' < H x' by linarith)
    have ht' := ht
    obtain ⟨y, c, hc, rfl⟩ := ht'
    -- lower bound on t
    have ht0 : x' y0 - c0 - ‖y0‖ ^ 2 / 2 ≤ H x' := le_csSup (hbdd x') ⟨y0, c0, hc0.symm, rfl⟩
    have hx'y0 : -(R * ‖y0‖) ≤ x' y0 := by
      have := cf_le_norm (-x') y0
      rw [norm_neg, ContinuousLinearMap.neg_apply] at this
      nlinarith [norm_nonneg y0]
    have hε1 : ε' ≤ 1 := min_le_right _ _
    have hlow : -K < x' y - c - ‖y‖ ^ 2 / 2 := by
      have := le_abs_self c0
      simp only [K]; linarith
    have hup : x' y - c - ‖y‖ ^ 2 / 2 ≤ (R + N) * ‖y‖ - b - ‖y‖ ^ 2 / 2 := by
      have a1 := cf_le_norm x' y
      have a2 := cf_le_norm (-l) y
      rw [norm_neg, ContinuousLinearMap.neg_apply] at a2
      have := hl y c hc
      have : ‖x'‖ * ‖y‖ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
      linarith
    have hn : ‖y‖ ≤ 2 * (R + N) + 2 * |K - b| + 1 := by
      by_contra hcon
      push_neg at hcon
      have hN : 0 ≤ N := norm_nonneg _
      have habs := le_abs_self (K - b)
      have habs0 := abs_nonneg (K - b)
      have hy1 : 1 ≤ ‖y‖ := by linarith
      nlinarith
    have hH2 : x'' y - c - ‖y‖ ^ 2 / 2 ≤ H x'' := le_csSup (hbdd x'') ⟨y, c, hc, rfl⟩
    have hd : x' y - x'' y ≤ ‖x' - x''‖ * ‖y‖ := by
      have := cf_le_norm (x' - x'') y
      simpa using this
    have : ‖x' - x''‖ * ‖y‖ ≤ ‖x' - x''‖ * (2 * (R + N) + 2 * |K - b| + 1) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have hεε : ε' ≤ ε := min_le_left _ _
    linarith
  refine ⟨H, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x'
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨M, hM, hMl⟩ := hlip (‖x'‖ + 1) (by positivity)
    refine ⟨min 1 (ε / (2 * M)), lt_min one_pos (by positivity), fun x'' hd => ?_⟩
    rw [dist_eq_norm] at hd
    have hd1 : ‖x'' - x'‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : ‖x'' - x'‖ < ε / (2 * M) := lt_of_lt_of_le hd (min_le_right _ _)
    have hn1 : ‖x''‖ ≤ ‖x'‖ + 1 := by
      have := norm_le_insert' x'' x'
      linarith [norm_sub_rev x'' x']
    have a1 := hMl x' x'' (by linarith) hn1
    have a2 := hMl x'' x' hn1 (by linarith)
    rw [norm_sub_rev] at a1
    have : M * ‖x'' - x'‖ < ε / 2 := by
      calc M * ‖x'' - x'‖ < M * (ε / (2 * M)) := mul_lt_mul_of_pos_left hd2 hM
        _ = ε / 2 := by field_simp
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · intro x'
    unfold Shared.conj Shared.halfSqNorm
    apply le_antisymm
    · apply iSup_le
      intro y
      beta_reduce
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy, EReal.top_add_coe, EReal.sub_top]; exact bot_le
      lift f y to ℝ using ⟨hy, hf.1 y⟩ with c hc
      rw [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      apply le_csSup (hbdd x')
      exact ⟨y, c, hc.symm, by ring⟩
    · by_contra hlt
      push_neg at hlt
      obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
      rw [EReal.coe_lt_coe_iff] at hz2
      obtain ⟨t, ⟨y, c, hc, rfl⟩, htz⟩ := exists_lt_of_lt_csSup (hne x') hz2
      have : ((x' y : ℝ) : EReal) - (f y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) ≤
          ⨆ y, ((x' y : ℝ) : EReal) - (f y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) :=
        le_iSup (fun y => ((x' y : ℝ) : EReal) - (f y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal))) y
      rw [hc, ← EReal.coe_add, ← EReal.coe_sub] at this
      have h3 := lt_of_le_of_lt this hz1
      rw [EReal.coe_lt_coe_iff] at h3
      linarith

end ConjFin
end RockafellarMaxMono.Cyclic

open RockafellarMaxMono.Cyclic
open RockafellarMaxMono

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by
  exact conjfin_core f hf hlsc
