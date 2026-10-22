-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T01:10:46.128804+00:00
-- url     : https://prove2.me/submissions/9c6d03c3-8bdf-48b5-a8e9-f364446d3e89

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace SROLemma9Aux
open TwoStageSRO.AsymOpt

variable {n d r m mt : ℕ}

theorem face_subset_Xi (M : Model n d r m mt) (I : Finset (Fin mt)) : face M I ⊆ Xi M :=
  fun _ h => h.1

/-- A point of the relative interior can be pushed slightly beyond itself, away from any other
point of the set. -/
theorem extend_of_mem_intrinsicInterior {d : ℕ} {F : Set (Fin d → ℝ)} {x x' : Fin d → ℝ}
    (hx : x ∈ intrinsicInterior ℝ F) (hx' : x' ∈ F) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - x') ∈ F := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.1 hx
  have hyF : (y : Fin d → ℝ) ∈ affineSpan ℝ F := y.2
  have hx'F : x' ∈ affineSpan ℝ F := subset_affineSpan ℝ F hx'
  have hmem : ∀ t : ℝ, (y : Fin d → ℝ) + t • ((y : Fin d → ℝ) - x') ∈ affineSpan ℝ F := by
    intro t
    have := AffineMap.lineMap_mem (1 + t) hx'F hyF
    convert this using 1
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_smul, one_smul, smul_sub]
    abel
  let γ : ℝ → affineSpan ℝ F := fun t => ⟨(y : Fin d → ℝ) + t • ((y : Fin d → ℝ) - x'), hmem t⟩
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = y := by
    apply Subtype.ext
    simp [γ]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ interior ((↑) ⁻¹' F : Set (affineSpan ℝ F)) :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact isOpen_interior.mem_nhds hy)
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have h2 : γ t ∈ ((↑) ⁻¹' F : Set (affineSpan ℝ F)) := interior_subset ht
  exact ⟨t, htpos, h2⟩

/-- Points in the relative interior of the same face have the same active constraints. -/
theorem active_transfer (M : Model n d r m mt) {F : Set (Fin d → ℝ)} (hF : IsFace M F)
    {zhat zbar : Fin d → ℝ} (hzhat : zhat ∈ intrinsicInterior ℝ F)
    (hzbar : zbar ∈ intrinsicInterior ℝ F) (k : Fin mt) (hk : zbar ∈ hyperplane M k) :
    zhat ∈ hyperplane M k := by
  obtain ⟨-, I, rfl⟩ := hF
  have hzhatF : zhat ∈ face M I := intrinsicInterior_subset hzhat
  obtain ⟨t, ht, hw⟩ := extend_of_mem_intrinsicInterior hzbar hzhatF
  have h1 := (face_subset_Xi M I hw) k
  have h2 := (face_subset_Xi M I hzhatF) k
  simp only [hyperplane, Set.mem_ofPred_eq] at hk ⊢
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub] at h1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
  rw [hk] at h1
  have : t * (M.g0 k - (M.G *ᵥ zhat) k) ≥ 0 := by linarith
  have h3 : M.g0 k - (M.G *ᵥ zhat) k ≥ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  linarith

/-- One inclusion of Lemma 9: translating `B(ẑ, ε) ∩ Ξ` by `z̄ - ẑ` lands in `B(z̄, ε) ∩ Ξ`
whenever every constraint active at `z̄` is active at `ẑ` and `ε ≤ ∆_Ξ(z̄)`. -/
theorem translate_subset (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {zhat zbar : Fin d → ℝ} (hzbarX : zbar ∈ Xi M)
    (hact : ∀ k, zbar ∈ hyperplane M k → zhat ∈ hyperplane M k)
    (ε : ℝ) (hεr : (ε : EReal) ≤ radius M p zbar) (ζ : Fin d → ℝ)
    (hζ : ζ ∈ ball p zhat ε ∩ Xi M) : ζ + (zbar - zhat) ∈ ball p zbar ε ∩ Xi M := by
  obtain ⟨hb, hx⟩ := hζ
  have hb' : ‖WithLp.toLp p (ζ - zhat)‖ ≤ ε := hb
  have hdiff : ζ + (zbar - zhat) - zbar = ζ - zhat := by abel
  refine ⟨?_, ?_⟩
  · show ‖WithLp.toLp p (ζ + (zbar - zhat) - zbar)‖ ≤ ε
    rw [hdiff]; exact hb'
  · intro k
    have hxk := hx k
    have hzk := hzbarX k
    rw [Matrix.mulVec_add, Matrix.mulVec_sub]
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases hk : zbar ∈ hyperplane M k
    · have hk' := hact k hk
      simp only [hyperplane, Set.mem_ofPred_eq] at hk hk'
      linarith
    · by_contra hcon
      push Not at hcon
      obtain ⟨s, hs⟩ : ∃ s, s = (M.G *ᵥ zbar) k - M.g0 k := ⟨_, rfl⟩
      obtain ⟨a, ha⟩ : ∃ a, a = (M.G *ᵥ (ζ - zhat)) k := ⟨_, rfl⟩
      have haeq : a = (M.G *ᵥ ζ) k - (M.G *ᵥ zhat) k := by
        rw [ha, Matrix.mulVec_sub]; rfl
      have hspos : 0 < s := by
        rcases (show 0 ≤ s by linarith).lt_or_eq with h | h
        · exact h
        · exfalso; apply hk; simp only [hyperplane, Set.mem_ofPred_eq]; linarith
      have hsa : s + a < 0 := by linarith
      have ha0 : a < 0 := by linarith
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -s / a := ⟨_, rfl⟩
      have hcpos : 0 < c := by rw [hc]; exact div_pos_of_neg_of_neg (by linarith) ha0
      have hc1 : c < 1 := by
        rw [hc, div_lt_one_of_neg ha0]; linarith
      have hca : c * a = -s := by rw [hc, div_mul_cancel₀ _ ha0.ne]
      have hw : zbar + c • (ζ - zhat) ∈ hyperplane M k := by
        simp only [hyperplane, Set.mem_ofPred_eq, Matrix.mulVec_add, Matrix.mulVec_smul,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [← ha]
        linarith
      have hv0 : 0 < ‖WithLp.toLp p (ζ - zhat)‖ := by
        refine norm_pos_iff.2 fun h0 => ?_
        have : ζ - zhat = 0 := by
          have := congrArg WithLp.ofLp h0
          simpa using this
        rw [this, Matrix.mulVec_zero] at ha
        simp at ha
        linarith
      have hle : radius M p zbar ≤
          ((‖WithLp.toLp p (zbar + c • (ζ - zhat) - zbar)‖ : ℝ) : EReal) := by
        unfold radius
        exact iInf₂_le_of_le k hk (iInf₂_le _ hw)
      have hlt : ‖WithLp.toLp p (zbar + c • (ζ - zhat) - zbar)‖ < ε := by
        rw [add_sub_cancel_left, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hcpos]
        calc c * ‖WithLp.toLp p (ζ - zhat)‖ < 1 * ‖WithLp.toLp p (ζ - zhat)‖ :=
              mul_lt_mul_of_pos_right hc1 hv0
          _ ≤ ε := by rw [one_mul]; exact hb'
      exact lt_irrefl _ (lt_of_le_of_lt (hεr.trans hle) (EReal.coe_lt_coe_iff.2 hlt))

/-- On a minimal face every constraint function is constant. -/
theorem minimalFace_const (M : Model n d r m mt) {F : Set (Fin d → ℝ)} (hF : IsMinimalFace M F)
    {a b : Fin d → ℝ} (ha : a ∈ F) (hb : b ∈ F) (k : Fin mt) :
    (M.G *ᵥ a) k = (M.G *ᵥ b) k := by
  classical
  obtain ⟨⟨hne, I, rfl⟩, hmin⟩ := hF
  -- reduce to the case `(G a)_k < (G b)_k`
  suffices key : ∀ a b : Fin d → ℝ, a ∈ face M I → b ∈ face M I → ∀ k,
      ¬ (M.G *ᵥ a) k < (M.G *ᵥ b) k by
    rcases lt_trichotomy ((M.G *ᵥ a) k) ((M.G *ᵥ b) k) with h | h | h
    · exact absurd h (key a b ha hb k)
    · exact h
    · exact absurd h (key b a hb ha k)
  intro a b ha hb k hlt
  set dv := a - b with hdv
  have hGd : ∀ j, (M.G *ᵥ dv) j = (M.G *ᵥ a) j - (M.G *ᵥ b) j := by
    intro j; rw [hdv, Matrix.mulVec_sub]; rfl
  set J := Finset.univ.filter (fun j => (M.G *ᵥ dv) j < 0) with hJ
  have hJne : J.Nonempty := ⟨k, by simp [hJ, hGd]; linarith⟩
  obtain ⟨j0, hj0J, hj0min⟩ := J.exists_min_image
    (fun j => ((M.G *ᵥ a) j - M.g0 j) / (-(M.G *ᵥ dv) j)) hJne
  have hj0neg : (M.G *ᵥ dv) j0 < 0 := by simpa [hJ] using hj0J
  set t := ((M.G *ᵥ a) j0 - M.g0 j0) / (-(M.G *ᵥ dv) j0) with ht
  have hax := ha.1
  have ht0 : 0 ≤ t := div_nonneg (by linarith [hax j0]) (by linarith)
  set c := a + t • dv with hc
  have hGc : ∀ j, (M.G *ᵥ c) j = (M.G *ᵥ a) j + t * (M.G *ᵥ dv) j := by
    intro j; rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul]; rfl
  have hcX : c ∈ Xi M := by
    intro j
    rw [hGc]
    by_cases hj : (M.G *ᵥ dv) j < 0
    · have h1 : t ≤ ((M.G *ᵥ a) j - M.g0 j) / (-(M.G *ᵥ dv) j) := hj0min j (by simp [hJ, hj])
      rw [le_div_iff₀ (by linarith)] at h1
      linarith
    · push Not at hj
      have := hax j
      nlinarith
  have hcI : ∀ i ∈ I, (M.G *ᵥ c) i = M.g0 i := by
    intro i hi
    rw [hGc, hGd, ha.2 i hi, hb.2 i hi]
    ring
  have hcj0 : (M.G *ᵥ c) j0 = M.g0 j0 := by
    have e : ((M.G *ᵥ a) j0 - M.g0 j0) / -(M.G *ᵥ dv) j0 * (M.G *ᵥ dv) j0 =
        -((M.G *ᵥ a) j0 - M.g0 j0) := by
      rw [div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self hj0neg.ne]; ring
    rw [hGc, ht, e]
    ring
  have hF' : IsFace M (face M (insert j0 I)) := by
    refine ⟨⟨c, hcX, ?_⟩, insert j0 I, rfl⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with h | h
    · rw [h]; exact hcj0
    · exact hcI i h
  have hsub : face M (insert j0 I) ⊆ face M I := fun z hz =>
    ⟨hz.1, fun i hi => hz.2 i (Finset.mem_insert_of_mem hi)⟩
  have heq := hmin _ hF' hsub
  have ha' : a ∈ face M (insert j0 I) := heq ▸ ha
  have hb' : b ∈ face M (insert j0 I) := heq ▸ hb
  have h1 := ha'.2 j0 (Finset.mem_insert_self _ _)
  have h2 := hb'.2 j0 (Finset.mem_insert_self _ _)
  rw [hGd, h1, h2, sub_self] at hj0neg
  exact lt_irrefl _ hj0neg

end SROLemma9Aux

open TwoStageSRO.AsymOpt SROLemma9Aux in
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1) (F : Set (Fin d → ℝ)) (hF : IsFace M F) :
    (∀ zhat ∈ intrinsicInterior ℝ F, ∀ zbar ∈ intrinsicInterior ℝ F, ∀ ε : ℝ, 0 ≤ ε →
      (ε : EReal) ≤ min (radius M p zhat) (radius M p zbar) →
      (fun ζ => ζ + (zbar - zhat)) '' (ball p zhat ε ∩ Xi M) = ball p zbar ε ∩ Xi M) ∧
    (IsMinimalFace M F →
      ∀ zhat ∈ intrinsicInterior ℝ F, ∀ zbar ∈ intrinsicInterior ℝ F, ∀ ε : ℝ, 0 ≤ ε →
      (fun ζ => ζ + (zbar - zhat)) '' (ball p zhat ε ∩ Xi M) = ball p zbar ε ∩ Xi M) := by
  have hFX : F ⊆ Xi M := by
    obtain ⟨-, I, rfl⟩ := hF
    exact face_subset_Xi M I
  refine ⟨?_, ?_⟩
  · intro zhat hzhat zbar hzbar ε hε hεr
    have hzhatX : zhat ∈ Xi M := hFX (intrinsicInterior_subset hzhat)
    have hzbarX : zbar ∈ Xi M := hFX (intrinsicInterior_subset hzbar)
    ext ζ
    constructor
    · rintro ⟨ζ', hζ', rfl⟩
      exact translate_subset M p hzbarX (fun k hk => active_transfer M hF hzhat hzbar k hk) ε
        (hεr.trans (min_le_right _ _)) ζ' hζ'
    · intro hζ
      refine ⟨ζ + (zhat - zbar), ?_, by abel⟩
      exact translate_subset M p hzhatX (fun k hk => active_transfer M hF hzbar hzhat k hk) ε
        (hεr.trans (min_le_left _ _)) ζ hζ
  · intro hmin zhat hzhat zbar hzbar ε hε
    have hzhatF := intrinsicInterior_subset hzhat
    have hzbarF := intrinsicInterior_subset hzbar
    have hconst : ∀ k, (M.G *ᵥ zhat) k = (M.G *ᵥ zbar) k := fun k =>
      minimalFace_const M hmin hzhatF hzbarF k
    have htrans : ∀ (u v : Fin d → ℝ), (∀ k, (M.G *ᵥ u) k = (M.G *ᵥ v) k) →
        ∀ ζ ∈ ball p u ε ∩ Xi M, ζ + (v - u) ∈ ball p v ε ∩ Xi M := by
      intro u v huv ζ hζ
      refine ⟨?_, fun k => ?_⟩
      · show ‖WithLp.toLp p (ζ + (v - u) - v)‖ ≤ ε
        have : ζ + (v - u) - v = ζ - u := by abel
        rw [this]; exact hζ.1
      · have := hζ.2 k
        rw [Matrix.mulVec_add, Matrix.mulVec_sub]
        simp only [Pi.add_apply, Pi.sub_apply]
        rw [huv k]
        linarith
    ext ζ
    constructor
    · rintro ⟨ζ', hζ', rfl⟩
      exact htrans zhat zbar hconst ζ' hζ'
    · intro hζ
      refine ⟨ζ + (zhat - zbar), htrans zbar zhat (fun k => (hconst k).symm) ζ hζ, by abel⟩
