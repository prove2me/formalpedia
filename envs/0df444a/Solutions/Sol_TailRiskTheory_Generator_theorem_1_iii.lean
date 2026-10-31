-- Prove2me | solution 1 for TailRiskTheory.Generator.theorem_1_iii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:33:12.26037+00:00
-- url     : https://prove2.me/submissions/1f0804b9-9092-494d-959d-4e162308bec7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TailRiskTheory_Generator_Model
import Theorems.Thm_TailRiskTheory_Generator_theorem_1_i
import Theorems.Thm_TailRiskTheory_Generator_theorem_1_ii
import Theorems.Thm_TailRiskTheory_Generator_theorem_3

open MeasureTheory ProbabilityTheory
open TailRiskSharing.VaRConv (distFn IsAtomless)
open TailRiskSharing.VaRTail (IsMonotone IsTranslationInvariant IsMonetary IsLawInvariant)
open TailRiskSharing.TailConv (Linf)
open TailRiskTheory.Generator

private lemma linf_const_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℝ)
    {X : Ω → ℝ} (hX : X ∈ Linf P) : (fun ω => c * X ω) ∈ Linf P := by
  obtain ⟨hm, C, hC⟩ := hX
  refine ⟨hm.const_mul c, |c| * C, ?_⟩
  filter_upwards [hC] with ω hω
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hω (abs_nonneg c)

private lemma linf_div_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℝ)
    {X : Ω → ℝ} (hX : X ∈ Linf P) : (fun ω => X ω / c) ∈ Linf P := by
  have h := linf_const_mul P c⁻¹ hX
  have : (fun ω => X ω / c) = (fun ω => c⁻¹ * X ω) := by
    funext ω; rw [div_eq_inv_mul]
  rw [this]; exact h

/-- If `Z` has the law of `(cX)_p` with `c > 0`, then `Z / c` has the law of `X_p`. -/
private lemma ptail_div {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p c : ℝ) (hc : 0 < c)
    (X Z : Ω → ℝ) (h : IsPTailOf P p (fun ω => c * X ω) Z) :
    IsPTailOf P p X (fun ω => Z ω / c) := by
  intro x
  have h1 : distFn P (fun ω => Z ω / c) x = distFn P Z (c * x) := by
    unfold distFn
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [div_le_iff₀ hc, mul_comm x c]
  have h2 : distFn P (fun ω => c * X ω) (c * x) = distFn P X x := by
    unfold distFn
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    exact mul_le_mul_iff_of_pos_left hc
  rw [h1, h (c * x)]
  unfold tailDistFn
  rw [h2]

/-- The direction `ρ^*` convex risk measure `⇒` `ρ` convex, via Theorem 3 with `n = 2`. -/
private lemma convex_of_star {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho rhoStar : (Ω → ℝ) → ℝ) (hpair : IsPTailPair P p rho rhoStar)
    (hmono : IsMonotone P (Linf P) rho) (hmonoStar : IsMonotone P (Linf P) rhoStar)
    (hconv : IsConvexRM P rhoStar) : IsConvexRM P rho := by
  intro X hX Y hY lam hl0 hl1
  rcases eq_or_lt_of_le hl0 with h0 | h0
  · subst h0
    have : (fun ω => (0:ℝ) * X ω + (1 - 0) * Y ω) = Y := by funext ω; ring
    rw [this]; linarith
  rcases eq_or_lt_of_le hl1 with h1 | h1
  · subst h1
    have : (fun ω => (1:ℝ) * X ω + (1 - 1) * Y ω) = X := by funext ω; ring
    rw [this]; linarith
  have hm : 0 < 1 - lam := by linarith
  let Xs : Fin 2 → Ω → ℝ := ![fun ω => lam * X ω, fun ω => (1 - lam) * Y ω]
  have hXs : ∀ i, Xs i ∈ Linf P := by
    intro i
    fin_cases i
    · exact linf_const_mul P lam hX
    · exact linf_const_mul P (1 - lam) hY
  have h3 := theorem_3 P hP p hp0 hp1 rho rhoStar hpair hmono hmonoStar 2 Xs hXs
  have hS : (fun ω => lam * X ω + (1 - lam) * Y ω) ∈ AggSet P Xs := by
    refine ⟨Xs, fun i => ⟨hXs i, fun x => rfl⟩, ?_⟩
    funext ω
    simp [Xs, Fin.sum_univ_two]
  have hle : ((rho (fun ω => lam * X ω + (1 - lam) * Y ω) : ℝ) : EReal) ≤
      ⨆ T ∈ TailAggSet P p Xs, (rhoStar T : EReal) := by
    rw [← h3]
    exact le_iSup₂ (f := fun S (_ : S ∈ AggSet P Xs) => (rho S : EReal)) _ hS
  have hbound : (⨆ T ∈ TailAggSet P p Xs, (rhoStar T : EReal)) ≤
      ((lam * rho X + (1 - lam) * rho Y : ℝ) : EReal) := by
    refine iSup₂_le ?_
    intro T hT
    obtain ⟨Ys, hYs, rfl⟩ := hT
    obtain ⟨hY0, hY0t⟩ := hYs 0
    obtain ⟨hY1, hY1t⟩ := hYs 1
    have hZ : (fun ω => Ys 0 ω / lam) ∈ Linf P := linf_div_const P lam hY0
    have hW : (fun ω => Ys 1 ω / (1 - lam)) ∈ Linf P := linf_div_const P (1 - lam) hY1
    have hZt : IsPTailOf P p X (fun ω => Ys 0 ω / lam) :=
      ptail_div P p lam h0 X (Ys 0) hY0t
    have hWt : IsPTailOf P p Y (fun ω => Ys 1 ω / (1 - lam)) :=
      ptail_div P p (1 - lam) hm Y (Ys 1) hY1t
    have eX : rho X = rhoStar (fun ω => Ys 0 ω / lam) := hpair.2 X hX _ hZ hZt
    have eY : rho Y = rhoStar (fun ω => Ys 1 ω / (1 - lam)) := hpair.2 Y hY _ hW hWt
    have hfun : (fun ω => ∑ i, Ys i ω) =
        (fun ω => lam * (Ys 0 ω / lam) + (1 - lam) * (Ys 1 ω / (1 - lam))) := by
      funext ω
      rw [Fin.sum_univ_two]
      field_simp
    rw [hfun, EReal.coe_le_coe_iff, eX, eY]
    exact hconv _ hZ _ hW lam hl0 hl1
  exact EReal.coe_le_coe_iff.mp (hle.trans hbound)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (rho rhoStar : (Ω → ℝ) → ℝ) (hpair : IsPTailPair P p rho rhoStar) :
    (IsCoherent P rho ↔ IsCoherent P rhoStar) ∧
    (IsConvexRiskMeasure P rho ↔ IsConvexRiskMeasure P rhoStar) ∧
    (IsMonetary P (Linf P) rho ↔ IsMonetary P (Linf P) rhoStar) := by
  obtain ⟨hMo, hTI, hPH, -⟩ := theorem_1_i P hP p hp0 hp1 rho rhoStar hpair
  obtain ⟨-, hCv, -⟩ := theorem_1_ii P hP p hp0 hp1 rho rhoStar hpair
  have hMon : IsMonetary P (Linf P) rho ↔ IsMonetary P (Linf P) rhoStar :=
    ⟨fun h => ⟨hMo.1 h.1, hTI.1 h.2⟩, fun h => ⟨hMo.2 h.1, hTI.2 h.2⟩⟩
  have hConv : IsConvexRiskMeasure P rho ↔ IsConvexRiskMeasure P rhoStar := by
    constructor
    · intro h
      exact ⟨hMon.1 h.1, hCv h.2⟩
    · intro h
      exact ⟨hMon.2 h.1, convex_of_star P hP p hp0 hp1 rho rhoStar hpair
        (hMo.2 h.1.1) h.1.1 h.2⟩
  refine ⟨?_, hConv, hMon⟩
  constructor
  · intro h
    exact ⟨hConv.1 h.1, hPH.1 h.2⟩
  · intro h
    exact ⟨hConv.2 h.1, hPH.2 h.2⟩
