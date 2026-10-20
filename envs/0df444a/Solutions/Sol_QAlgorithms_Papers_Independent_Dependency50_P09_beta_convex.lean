-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P09.beta_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:46:58.110473+00:00
-- url     : https://prove2.me/submissions/5053e05a-904d-483b-8399-d398971ba83f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)


theorem g53a_specNorm_comb {n : Type} [Fintype n] [DecidableEq n] (a b : ℂ) (X Y : Matrix n n ℂ) :
    specNorm (a • X + b • Y) ≤ ‖a‖ * specNorm X + ‖b‖ * specNorm Y := by
  have e : ∀ Z : Matrix n n ℂ, specNorm Z =
      ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap Z‖ :=
    fun Z => rfl
  rw [e, e, e, map_add, map_smul, map_smul]
  exact (norm_add_le _ _).trans (by rw [norm_smul, norm_smul])

theorem g53a_feas_comb {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M0 M1 : Superop (A × B) (C × D)) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (S1 V1 S0 V0 : Op ((A × B) × (C × D)))
    (f1 : BetaFeasible M1 S1 V1) (f0 : BetaFeasible M0 S0 V0) :
    BetaFeasible (fun X => (lam : ℂ) • M1 X + ((1-lam : ℝ) : ℂ) • M0 X)
      ((lam : ℂ) • S1 + ((1-lam : ℝ) : ℂ) • S0) ((lam : ℂ) • V1 + ((1-lam : ℝ) : ℂ) • V0) := by
  obtain ⟨hS1, hV1, hp1, hm1, hsp1, hsm1, hns1⟩ := f1
  obtain ⟨hS0, hV0, hp0, hm0, hsp0, hsm0, hns0⟩ := f0
  have sa : ∀ r : ℝ, IsSelfAdjoint (r : ℂ) := fun r => by
    show star (r : ℂ) = r; simp
  have nn1 : (0 : ℂ) ≤ (lam : ℂ) := Complex.zero_le_real.mpr hl0
  have nn0 : (0 : ℂ) ≤ ((1 - lam : ℝ) : ℂ) := Complex.zero_le_real.mpr (by linarith)
  have hchoi : choi (fun X => (lam : ℂ) • M1 X + ((1-lam : ℝ) : ℂ) • M0 X) =
      (lam : ℂ) • choi M1 + ((1-lam : ℝ) : ℂ) • choi M0 := by
    ext p q; rfl
  have htb : ∀ (a b : ℂ) (X Y : Op ((A × B) × (C × D))),
      transposeBobChoi (a • X + b • Y) = a • transposeBobChoi X + b • transposeBobChoi Y := by
    intro a b X Y; ext p q; rfl
  have comb : ∀ X1 X0 : Op ((A × B) × (C × D)), X1.PosSemidef → X0.PosSemidef →
      ((lam : ℂ) • X1 + ((1-lam : ℝ) : ℂ) • X0).PosSemidef := fun X1 X0 h1 h0 =>
    (h1.smul nn1).add (h0.smul nn0)
  refine ⟨(hS1.smul (sa lam)).add (hS0.smul (sa _)), (hV1.smul (sa lam)).add (hV0.smul (sa _)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hchoi]
    have : (lam : ℂ) • V1 + ((1-lam : ℝ) : ℂ) • V0 + ((lam : ℂ) • choi M1 + ((1-lam : ℝ) : ℂ) • choi M0)
        = (lam : ℂ) • (V1 + choi M1) + ((1-lam : ℝ) : ℂ) • (V0 + choi M0) := by
      simp only [smul_add]; abel
    rw [this, htb]; exact comb _ _ hp1 hp0
  · rw [hchoi]
    have : (lam : ℂ) • V1 + ((1-lam : ℝ) : ℂ) • V0 - ((lam : ℂ) • choi M1 + ((1-lam : ℝ) : ℂ) • choi M0)
        = (lam : ℂ) • (V1 - choi M1) + ((1-lam : ℝ) : ℂ) • (V0 - choi M0) := by
      simp only [smul_sub]; abel
    rw [this, htb]; exact comb _ _ hm1 hm0
  · have : (lam : ℂ) • S1 + ((1-lam : ℝ) : ℂ) • S0 + ((lam : ℂ) • V1 + ((1-lam : ℝ) : ℂ) • V0)
        = (lam : ℂ) • (S1 + V1) + ((1-lam : ℝ) : ℂ) • (S0 + V0) := by
      simp only [smul_add]; abel
    rw [this]; exact comb _ _ hsp1 hsp0
  · have : (lam : ℂ) • S1 + ((1-lam : ℝ) : ℂ) • S0 - ((lam : ℂ) • V1 + ((1-lam : ℝ) : ℂ) • V0)
        = (lam : ℂ) • (S1 - V1) + ((1-lam : ℝ) : ℂ) • (S0 - V0) := by
      simp only [smul_sub]; abel
    rw [this]; exact comb _ _ hsm1 hsm0
  · intro a aa b bb d dd
    have e1 := hns1 a aa b bb d dd
    have e0 := hns0 a aa b bb d dd
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rw [e1, e0]
    ring

theorem g53a_beta_nonneg {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (M : Superop (A × B) (C × D)) : 0 ≤ bipartiteBeta M := by
  apply le_sInf
  rintro r ⟨S, V, _, rfl⟩
  have : 0 ≤ specNorm (traceOutput S) := by
    have e : specNorm (traceOutput S) =
      ‖(Matrix.toEuclideanLin (𝕜 := ℂ) (m := A × B) (n := A × B)).trans LinearMap.toContinuousLinearMap
        (traceOutput S)‖ := rfl
    rw [e]; exact norm_nonneg _
  exact_mod_cast this

end QAlgorithms.Papers.Independent.Dependency50.P09

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P09
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Information100.P69 (CP)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Proposition 9 (Convexity), arXiv:2010.01058v3, PDF pp.8.
 -/
theorem solution {A : Type} [Fintype A] [Nonempty A]
    {B : Type} [Fintype B] [Nonempty B]
    {C : Type} [Fintype C] [Nonempty C]
    {D : Type} [Fintype D] [Nonempty D]
    (M0 M1 : Superop (A × B) (C × D)) (h0 : CP M0) (h1 : CP M1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 1) :
    bipartiteBeta (fun X => (lam : ℂ) • M1 X + ((1-lam : ℝ) : ℂ) • M0 X) ≤
      (lam : EReal) * bipartiteBeta M1 + ((1-lam : ℝ) : EReal) * bipartiteBeta M0 := by
  obtain ⟨hl0, hl1⟩ := hlam
  rcases eq_or_lt_of_le hl0 with h | hpos
  · subst h
    have : (fun X => ((0:ℝ):ℂ) • M1 X + ((1-0:ℝ):ℂ) • M0 X) = M0 := by funext X; simp
    rw [this]; simp
  rcases eq_or_lt_of_le hl1 with h | hlt
  · subst h
    have : (fun X => ((1:ℝ):ℂ) • M1 X + ((1-1:ℝ):ℂ) • M0 X) = M1 := by funext X; simp
    rw [this]; simp
  have hb1 := g53a_beta_nonneg M1
  have hb0 := g53a_beta_nonneg M0
  have hx0 : 0 ≤ ((1-lam : ℝ) : EReal) * bipartiteBeta M0 :=
    EReal.mul_nonneg (by exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - lam)) hb0
  have hx1 : 0 ≤ (lam : EReal) * bipartiteBeta M1 :=
    EReal.mul_nonneg (by exact_mod_cast hl0) hb1
  by_cases t1 : bipartiteBeta M1 = ⊤
  · rw [t1, EReal.coe_mul_top_of_pos hpos,
      EReal.top_add_of_ne_bot (lt_of_lt_of_le EReal.bot_lt_zero hx0).ne']
    exact le_top
  by_cases t0 : bipartiteBeta M0 = ⊤
  · rw [t0, EReal.coe_mul_top_of_pos (by linarith),
      EReal.add_top_of_ne_bot (lt_of_lt_of_le EReal.bot_lt_zero hx1).ne']
    exact le_top
  have hb1e : bipartiteBeta M1 = (((bipartiteBeta M1).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal t1 (lt_of_lt_of_le EReal.bot_lt_zero hb1).ne').symm
  have hb0e : bipartiteBeta M0 = (((bipartiteBeta M0).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal t0 (lt_of_lt_of_le EReal.bot_lt_zero hb0).ne').symm
  generalize (bipartiteBeta M1).toReal = b1 at hb1e
  generalize (bipartiteBeta M0).toReal = b0 at hb0e
  rw [hb1e, hb0e, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  by_contra hc
  push Not at hc
  obtain ⟨x, hxa, hxb⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  have hxa' : lam * b1 + (1 - lam) * b0 < x := by exact_mod_cast hxa
  obtain ⟨r1, ⟨S1, V1, f1, rfl⟩, hr1⟩ := sInf_lt_iff.mp (show bipartiteBeta M1 <
      ((b1 + (x - (lam * b1 + (1 - lam) * b0)) : ℝ) : EReal) by
    rw [hb1e]; exact_mod_cast (by linarith))
  obtain ⟨r0, ⟨S0, V0, f0, rfl⟩, hr0⟩ := sInf_lt_iff.mp (show bipartiteBeta M0 <
      ((b0 + (x - (lam * b1 + (1 - lam) * b0)) : ℝ) : EReal) by
    rw [hb0e]; exact_mod_cast (by linarith))
  have hv1 : specNorm (traceOutput S1) < b1 + (x - (lam * b1 + (1 - lam) * b0)) := by
    exact_mod_cast hr1
  have hv0 : specNorm (traceOutput S0) < b0 + (x - (lam * b1 + (1 - lam) * b0)) := by
    exact_mod_cast hr0
  have hf := g53a_feas_comb M0 M1 lam hl0 hl1 S1 V1 S0 V0 f1 f0
  have hle : bipartiteBeta (fun X => (lam : ℂ) • M1 X + ((1-lam : ℝ) : ℂ) • M0 X) ≤
      ((specNorm (traceOutput ((lam : ℂ) • S1 + ((1-lam : ℝ) : ℂ) • S0)) : ℝ) : EReal) :=
    sInf_le ⟨_, _, hf, rfl⟩
  have tO : traceOutput ((lam : ℂ) • S1 + ((1-lam : ℝ) : ℂ) • S0) =
      (lam : ℂ) • traceOutput S1 + ((1-lam : ℝ) : ℂ) • traceOutput S0 := by
    ext i j
    simp [traceOutput, Finset.sum_add_distrib, Finset.mul_sum]
  have hn := g53a_specNorm_comb (lam : ℂ) ((1-lam : ℝ) : ℂ) (traceOutput S1) (traceOutput S0)
  rw [← tO, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hl0,
    Real.norm_of_nonneg (by linarith)] at hn
  have hlt2 : specNorm (traceOutput ((lam : ℂ) • S1 + ((1-lam : ℝ) : ℂ) • S0)) < x := by
    nlinarith
  have : bipartiteBeta (fun X => (lam : ℂ) • M1 X + ((1-lam : ℝ) : ℂ) • M0 X) < (x : EReal) :=
    lt_of_le_of_lt hle (by exact_mod_cast hlt2)
  exact absurd hxb (not_lt.mpr this.le)


end

