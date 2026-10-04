-- Prove2me | solution 1 for StarShapedRisk.Representation.theorem2_star_shaped_iff_min_convex
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T04:52:29.042989+00:00
-- url     : https://prove2.me/submissions/3ed58726-6bb9-46bd-aa38-91cf19e693a6

import Definitions.Def_StarShapedRisk_Representation_AcceptanceSet
import Mathlib


set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace StarShapedRisk.Representation
open StarShapedRisk.Representation

theorem sr_star_small {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hs : IsStarShaped 𝒳 ρ) (X : 𝒳.carrier) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ρ (t • X) ≤ t * ρ X := by
  have hh := hs (t • X) t⁻¹ ((one_lt_inv₀ ht0).mpr ht1)
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm


theorem sr_risk_const {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) (m : ℝ) : ρ (𝒳.const m)=m := by
  have he : (0 : 𝒳.carrier)-𝒳.const (-m)=𝒳.const m := by ext ω; simp [PositionSpace.const]
  have hh := hρ.2.1 0 (-m)
  have hn : ρ 0=0 := hρ.2.2
  rw [he,hn] at hh
  simpa using hh

theorem sr_shifts_bounds {Ω : Type*} (𝒳 : PositionSpace Ω) (A : Set 𝒳.carrier)
    (hA : IsAcceptanceSet 𝒳 A) (X : 𝒳.carrier) :
    {m : ℝ | X-𝒳.const m ∈ A}.Nonempty ∧ BddBelow {m : ℝ | X-𝒳.const m ∈ A} := by
  obtain ⟨C,hC⟩ := 𝒳.bounded X X.property
  obtain ⟨m,hm⟩ := hA.1.nonempty
  constructor
  · refine ⟨C-m,hA.2 (𝒳.const m) hm (X-𝒳.const (C-m)) ?_⟩
    intro ω
    change X.val ω-(C-m) ≤ m
    have := (abs_le.mp (hC ω)).2
    linarith
  · refine ⟨-C,?_⟩
    intro m hm
    have hac : 𝒳.const (-C-m) ∈ A := hA.2 _ hm _ (by
      intro ω
      change -C-m ≤ X.val ω-m
      have := (abs_le.mp (hC ω)).1
      linarith)
    have hh := hA.1.1 hac
    change -C-m ≤ 0 at hh
    linarith


end StarShapedRisk.Representation


set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical
namespace StarShapedRisk.Representation
variable {Ω : Type*} (𝒳 : PositionSpace Ω)

lemma sr_riskOf_risk (A : Set 𝒳.carrier) (hA : IsAcceptanceSet 𝒳 A) :
    IsRiskMeasure 𝒳 (riskOf 𝒳 A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y hYX
    apply le_csInf (sr_shifts_bounds 𝒳 A hA X).1
    intro m hm
    exact csInf_le (sr_shifts_bounds 𝒳 A hA Y).2 (hA.2 _ hm _ (fun ω => by
      change Y.val ω - m ≤ X.val ω - m
      linarith [hYX ω]))
  · intro X m
    have h1 : riskOf 𝒳 A X - m ≤ riskOf 𝒳 A (X - 𝒳.const m) := by
      apply le_csInf (sr_shifts_bounds 𝒳 A hA _).1
      intro r hr
      change _ ∈ A at hr
      have he : (X - 𝒳.const m) - 𝒳.const r = X - 𝒳.const (r + m) := by
        ext ω; simp [PositionSpace.const]; ring
      have hx := csInf_le (sr_shifts_bounds 𝒳 A hA X).2 (he ▸ hr)
      change riskOf 𝒳 A X ≤ r + m at hx
      linarith
    have h2 : riskOf 𝒳 A (X - 𝒳.const m) + m ≤ riskOf 𝒳 A X := by
      apply le_csInf (sr_shifts_bounds 𝒳 A hA X).1
      intro r hr
      change _ ∈ A at hr
      have he : (X - 𝒳.const m) - 𝒳.const (r - m) = X - 𝒳.const r := by
        ext ω; simp [PositionSpace.const]
      have hx := csInf_le (sr_shifts_bounds 𝒳 A hA _).2 (he.symm ▸ hr)
      change riskOf 𝒳 A (X - 𝒳.const m) ≤ r - m at hx
      linarith
    linarith
  · apply le_antisymm
    · have hle : riskOf 𝒳 A 0 ≤ 0 := by
        have he : IsGLB {m : ℝ | (0 : 𝒳.carrier) - 𝒳.const m ∈ A} 0 := by
          constructor
          · intro m hm
            have hc : 𝒳.const (-m) ∈ A := by
              change (0 : 𝒳.carrier) - 𝒳.const m ∈ A at hm
              have he : (0 : 𝒳.carrier) - 𝒳.const m = 𝒳.const (-m) := by
                ext ω; simp [PositionSpace.const]
              exact he ▸ hm
            have hh := hA.1.1 hc
            change -m ≤ 0 at hh
            linarith
          · intro b hb
            have hu : -b ∈ upperBounds {m : ℝ | 𝒳.const m ∈ A} := by
              intro m hm
              change 𝒳.const m ∈ A at hm
              have he : (0 : 𝒳.carrier) - 𝒳.const (-m) = 𝒳.const m := by
                ext ω; simp [PositionSpace.const]
              have hh := hb (he.symm ▸ hm)
              change b ≤ -m at hh
              linarith
            have hh := hA.1.2 hu
            linarith
        exact le_of_eq (he.csInf_eq (sr_shifts_bounds 𝒳 A hA 0).1)
      exact hle
    · apply le_csInf (sr_shifts_bounds 𝒳 A hA 0).1
      intro m hm
      have hc : 𝒳.const (-m) ∈ A := by
        change (0 : 𝒳.carrier) - 𝒳.const m ∈ A at hm
        have he : (0 : 𝒳.carrier) - 𝒳.const m = 𝒳.const (-m) := by
          ext ω; simp [PositionSpace.const]
        exact he ▸ hm
      have hh := hA.1.1 hc
      change -m ≤ 0 at hh
      linarith

lemma sr_riskOf_convex (A : Set 𝒳.carrier) (hA : IsConvexAcceptanceSet 𝒳 A) :
    IsConvexRiskMeasure 𝒳 (riskOf 𝒳 A) := by
  refine ⟨sr_riskOf_risk 𝒳 A hA.1, ?_⟩
  intro X Y t ht0 ht1
  have hs : 0 < 1 - t := sub_pos.mpr ht1
  let B := riskOf 𝒳 A (t • X + (1 - t) • Y)
  have hpair (mx my : ℝ) (hx : X - 𝒳.const mx ∈ A) (hy : Y - 𝒳.const my ∈ A) :
      B ≤ t * mx + (1 - t) * my := by
    have he : t • (X - 𝒳.const mx) + (1 - t) • (Y - 𝒳.const my) =
        (t • X + (1 - t) • Y) - 𝒳.const (t * mx + (1 - t) * my) := by
      ext ω; simp [PositionSpace.const]; ring
    apply csInf_le (sr_shifts_bounds 𝒳 A hA.1 _).2
    change _ ∈ A
    exact he ▸ hA.2 hx hy ht0.le hs.le (by ring)
  have hmy (my : ℝ) (hy : Y - 𝒳.const my ∈ A) : B ≤ t * riskOf 𝒳 A X + (1 - t) * my := by
    have h : (B - (1 - t) * my) / t ≤ riskOf 𝒳 A X := by
      apply le_csInf (sr_shifts_bounds 𝒳 A hA.1 X).1
      intro mx hx
      rw [div_le_iff₀ ht0]
      linarith [hpair mx my hx hy]
    rw [div_le_iff₀ ht0] at h
    linarith
  have h : (B - t * riskOf 𝒳 A X) / (1 - t) ≤ riskOf 𝒳 A Y := by
    apply le_csInf (sr_shifts_bounds 𝒳 A hA.1 Y).1
    intro my hy
    rw [div_le_iff₀ hs]
    linarith [hmy my hy]
  rw [div_le_iff₀ hs] at h
  linarith

lemma sr_acceptance_convex (ρ : 𝒳.carrier → ℝ) (hρ : IsConvexRiskMeasure 𝒳 ρ) :
    IsConvexAcceptanceSet 𝒳 (acceptanceSet 𝒳 ρ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have he : {m : ℝ | 𝒳.const m ∈ acceptanceSet 𝒳 ρ} = Set.Iic 0 := by
      ext m; simp [acceptanceSet, sr_risk_const 𝒳 ρ hρ.1]
    rw [he]; exact isLUB_Iic
  · intro X hX Y hYX
    exact (hρ.1.1 X Y hYX).trans hX
  · intro X hX Y hY r s hr hs hrs
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · have he : s = 1 := by linarith
      simpa [← hr0, he] using hY
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · have he : r = 1 := by linarith
      simpa [← hs0, he] using hX
    have he : s = 1 - r := by linarith
    have hh := hρ.2 X Y r hr0 (by linarith)
    rw [← he] at hh
    exact hh.trans (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hr hX)
      (mul_nonpos_of_nonneg_of_nonpos hs hY))

lemma sr_convex_star (ρ : 𝒳.carrier → ℝ) (hρ : IsConvexRiskMeasure 𝒳 ρ) :
    IsStarShaped 𝒳 ρ := by
  intro X t ht
  have ht0 : 0 < t := by linarith
  have hi0 : 0 < t⁻¹ := inv_pos.mpr ht0
  have hi1 : t⁻¹ < 1 := (inv_lt_one₀ ht0).mpr ht
  have hh := hρ.2 (t • X) 0 t⁻¹ hi0 hi1
  rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul, smul_zero, add_zero, hρ.1.2.2] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc, mul_inv_cancel₀ ht0.ne'] using hm

end StarShapedRisk.Representation

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical
namespace StarShapedRisk.Representation
variable {Ω : Type*} (𝒳 : PositionSpace Ω)

def sr_segment (Z : 𝒳.carrier) : Set 𝒳.carrier :=
  {Y | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ ω, Y.val ω ≤ t * Z.val ω}

lemma sr_segment_subset (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ)
    (hs : IsStarShaped 𝒳 ρ) (Z : 𝒳.carrier) (hz : ρ Z ≤ 0) :
    sr_segment 𝒳 Z ⊆ acceptanceSet 𝒳 ρ := by
  rintro Y ⟨t, ht0, ht1, hY⟩
  have hc : ρ (t • Z) ≤ 0 := by
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · rw [← h0, zero_smul]; exact le_of_eq hρ.2.2
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · simpa [h1] using hz
    exact (sr_star_small 𝒳 ρ hs Z t h0 h1).trans
      (mul_nonpos_of_nonneg_of_nonpos ht0 hz)
  exact (hρ.1 (t • Z) Y hY).trans hc

lemma sr_segment_convex (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ)
    (hs : IsStarShaped 𝒳 ρ) (Z : 𝒳.carrier) (hz : ρ Z ≤ 0) :
    IsConvexAcceptanceSet 𝒳 (sr_segment 𝒳 Z) := by
  have hzero : (0 : 𝒳.carrier) ∈ sr_segment 𝒳 Z :=
    ⟨0, le_rfl, zero_le_one, fun ω => by simp⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro m hm
    have hh := sr_segment_subset 𝒳 ρ hρ hs Z hz hm
    change ρ (𝒳.const m) ≤ 0 at hh
    simpa [sr_risk_const 𝒳 ρ hρ] using hh
  · intro b hb
    exact hb (show 𝒳.const 0 ∈ sr_segment 𝒳 Z by
      have he : 𝒳.const 0 = (0 : 𝒳.carrier) := by ext ω; rfl
      rw [he]; exact hzero)
  · rintro X ⟨t, ht0, ht1, ht⟩ Y hYX
    exact ⟨t, ht0, ht1, fun ω => (hYX ω).trans (ht ω)⟩
  · rintro X ⟨t, ht0, ht1, ht⟩ Y ⟨u, hu0, hu1, hu⟩ r s hr hs hrs
    refine ⟨r * t + s * u, add_nonneg (mul_nonneg hr ht0) (mul_nonneg hs hu0), ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left ht1 hr, mul_le_mul_of_nonneg_left hu1 hs]
    · intro ω
      change r * X.val ω + s * Y.val ω ≤ (r * t + s * u) * Z.val ω
      nlinarith [mul_le_mul_of_nonneg_left (ht ω) hr, mul_le_mul_of_nonneg_left (hu ω) hs]

lemma sr_segment_majorant (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ)
    (hs : IsStarShaped 𝒳 ρ) (X : 𝒳.carrier) :
    ∃ γ : 𝒳.carrier → ℝ, IsConvexRiskMeasure 𝒳 γ ∧
      (∀ Y, ρ Y ≤ γ Y) ∧ γ X = ρ X := by
  let Z := X - 𝒳.const (ρ X)
  have hz : ρ Z ≤ 0 := by dsimp [Z]; rw [hρ.2.1]; exact le_of_eq (sub_self _)
  let A := sr_segment 𝒳 Z
  have hA := sr_segment_convex 𝒳 ρ hρ hs Z hz
  have hd (Y : 𝒳.carrier) : ρ Y ≤ riskOf 𝒳 A Y := by
    apply le_csInf (sr_shifts_bounds 𝒳 A hA.1 Y).1
    intro m hm
    have hh := sr_segment_subset 𝒳 ρ hρ hs Z hz hm
    change ρ (Y - 𝒳.const m) ≤ 0 at hh
    rw [hρ.2.1] at hh
    linarith
  refine ⟨riskOf 𝒳 A, sr_riskOf_convex 𝒳 A hA, hd, le_antisymm ?_ (hd X)⟩
  apply csInf_le (sr_shifts_bounds 𝒳 A hA.1 X).2
  exact ⟨1, zero_le_one, le_rfl, fun ω => by simp [Z]⟩
end StarShapedRisk.Representation

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical
namespace StarShapedRisk.Representation
variable {Ω : Type*} (𝒳 : PositionSpace Ω)

lemma sr_family_acceptance (ρ : 𝒳.carrier → ℝ) (Γ : Set (𝒳.carrier → ℝ))
    (hc : ∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ)
    (hmin : ∀ X, IsLeast ((fun γ => γ X) '' Γ) (ρ X)) :
    (∀ A ∈ (fun γ => acceptanceSet 𝒳 γ) '' Γ, IsConvexAcceptanceSet 𝒳 A) ∧
    ∀ X, IsLeast {m : ℝ | ∃ A ∈ (fun γ => acceptanceSet 𝒳 γ) '' Γ,
      X - 𝒳.const m ∈ A} (ρ X) := by
  refine ⟨?_, ?_⟩
  · rintro A ⟨γ, hγ, rfl⟩
    exact sr_acceptance_convex 𝒳 γ (hc γ hγ)
  · intro X
    rcases (hmin X).1 with ⟨γ, hγ, he⟩
    dsimp only at he
    refine ⟨?_, ?_⟩
    · refine ⟨acceptanceSet 𝒳 γ, ⟨γ, hγ, rfl⟩, ?_⟩
      change γ (X - 𝒳.const (ρ X)) ≤ 0
      rw [(hc γ hγ).1.2.1, he]
      exact le_of_eq (sub_self _)
    · rintro m ⟨A, ⟨γ, hγ, rfl⟩, hm⟩
      change γ (X - 𝒳.const m) ≤ 0 at hm
      rw [(hc γ hγ).1.2.1] at hm
      have hh := (hmin X).2 (show γ X ∈ ((fun γ => γ X) '' Γ) from ⟨γ, hγ, rfl⟩)
      linarith

lemma sr_acceptance_family (ρ : 𝒳.carrier → ℝ) (F : Set (Set 𝒳.carrier))
    (hc : ∀ A ∈ F, IsConvexAcceptanceSet 𝒳 A)
    (hmin : ∀ X, IsLeast {m : ℝ | ∃ A ∈ F, X - 𝒳.const m ∈ A} (ρ X)) :
    ∃ Γ : Set (𝒳.carrier → ℝ), (∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ) ∧
      ∀ X, IsLeast ((fun γ => γ X) '' Γ) (ρ X) := by
  refine ⟨(fun A => riskOf 𝒳 A) '' F, ?_, ?_⟩
  · rintro γ ⟨A, hA, rfl⟩
    exact sr_riskOf_convex 𝒳 A (hc A hA)
  · intro X
    have hd (A : Set 𝒳.carrier) (hA : A ∈ F) : ρ X ≤ riskOf 𝒳 A X := by
      apply le_csInf (sr_shifts_bounds 𝒳 A (hc A hA).1 X).1
      intro m hm
      exact (hmin X).2 ⟨A, hA, hm⟩
    rcases (hmin X).1 with ⟨A, hA, hm⟩
    have he : riskOf 𝒳 A X = ρ X := le_antisymm
      (csInf_le (sr_shifts_bounds 𝒳 A (hc A hA).1 X).2 hm) (hd A hA)
    refine ⟨⟨riskOf 𝒳 A, ⟨A, hA, rfl⟩, he⟩, ?_⟩
    rintro r ⟨γ, ⟨B, hB, rfl⟩, rfl⟩
    exact hd B hB

lemma sr_min_star (ρ : 𝒳.carrier → ℝ) (Γ : Set (𝒳.carrier → ℝ))
    (hc : ∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ)
    (hmin : ∀ X, IsLeast ((fun γ => γ X) '' Γ) (ρ X)) : IsStarShaped 𝒳 ρ := by
  intro X t ht
  rcases (hmin (t • X)).1 with ⟨γ, hγ, he⟩
  dsimp only at he
  have hd := (hmin X).2 (show γ X ∈ ((fun γ => γ X) '' Γ) from ⟨γ, hγ, rfl⟩)
  have hh := sr_convex_star 𝒳 γ (hc γ hγ) X t ht
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_left hd (by linarith)).trans hh

lemma sr_canonical (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ)
    (hs : IsStarShaped 𝒳 ρ) :
    let Γ : Set (𝒳.carrier → ℝ) := {γ | IsConvexRiskMeasure 𝒳 γ ∧ ∀ Y, ρ Y ≤ γ Y}
    (∀ X, IsLeast ((fun γ => γ X) '' Γ) (ρ X)) ∧
    (∀ A ∈ (fun γ => acceptanceSet 𝒳 γ) '' Γ, IsConvexAcceptanceSet 𝒳 A) ∧
    ∀ X, IsLeast {m : ℝ | ∃ A ∈ (fun γ => acceptanceSet 𝒳 γ) '' Γ,
      X - 𝒳.const m ∈ A} (ρ X) := by
  dsimp only
  have hm (X : 𝒳.carrier) : IsLeast
      ((fun γ => γ X) '' {γ | IsConvexRiskMeasure 𝒳 γ ∧ ∀ Y, ρ Y ≤ γ Y}) (ρ X) := by
    rcases sr_segment_majorant 𝒳 ρ hρ hs X with ⟨γ, hc, hd, he⟩
    refine ⟨⟨γ, ⟨hc, hd⟩, he⟩, ?_⟩
    rintro r ⟨δ, ⟨hδ, hdδ⟩, rfl⟩
    exact hdδ X
  exact ⟨hm, sr_family_acceptance 𝒳 ρ _ (fun γ hγ => hγ.1) hm⟩
end StarShapedRisk.Representation

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Classical
namespace StarShapedRisk.Representation
theorem theorem2_star_shaped_iff_min_convex {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       ∃ Γ : Set (𝒳.carrier → ℝ), (∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ) ∧
         ∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ) (ρ X),
       ∃ 𝔄 : Set (Set 𝒳.carrier), (∀ 𝒜 ∈ 𝔄, IsConvexAcceptanceSet 𝒳 𝒜) ∧
         ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄, X - 𝒳.const m ∈ 𝒜} (ρ X)] ∧
    (IsStarShaped 𝒳 ρ →
      let Γ₀ : Set (𝒳.carrier → ℝ) :=
        {γ | IsConvexRiskMeasure 𝒳 γ ∧ ∀ Y : 𝒳.carrier, ρ Y ≤ γ Y}
      let 𝔄₀ : Set (Set 𝒳.carrier) := (fun γ => acceptanceSet 𝒳 γ) '' Γ₀
      (∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ₀) (ρ X)) ∧
      (∀ 𝒜 ∈ 𝔄₀, IsConvexAcceptanceSet 𝒳 𝒜) ∧
      ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄₀, X - 𝒳.const m ∈ 𝒜} (ρ X)) := by
  constructor
  · tfae_have 1 → 2
    · intro hs
      refine ⟨{γ | IsConvexRiskMeasure 𝒳 γ ∧ ∀ Y, ρ Y ≤ γ Y}, ?_, (sr_canonical 𝒳 ρ hρ hs).1⟩
      exact fun γ hγ => hγ.1
    tfae_have 2 → 3
    · rintro ⟨Γ, hc, hm⟩
      exact ⟨(fun γ => acceptanceSet 𝒳 γ) '' Γ, sr_family_acceptance 𝒳 ρ Γ hc hm⟩
    tfae_have 3 → 1
    · rintro ⟨F, hc, hm⟩
      rcases sr_acceptance_family 𝒳 ρ F hc hm with ⟨Γ, hΓ, hmin⟩
      exact sr_min_star 𝒳 ρ Γ hΓ hmin
    tfae_finish
  · exact sr_canonical 𝒳 ρ hρ

end StarShapedRisk.Representation


open StarShapedRisk.Representation in
theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       ∃ Γ : Set (𝒳.carrier → ℝ), (∀ γ ∈ Γ, IsConvexRiskMeasure 𝒳 γ) ∧
         ∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ) (ρ X),
       ∃ 𝔄 : Set (Set 𝒳.carrier), (∀ 𝒜 ∈ 𝔄, IsConvexAcceptanceSet 𝒳 𝒜) ∧
         ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄, X - 𝒳.const m ∈ 𝒜} (ρ X)] ∧
    (IsStarShaped 𝒳 ρ →
      let Γ₀ : Set (𝒳.carrier → ℝ) :=
        {γ | IsConvexRiskMeasure 𝒳 γ ∧ ∀ Y : 𝒳.carrier, ρ Y ≤ γ Y}
      let 𝔄₀ : Set (Set 𝒳.carrier) := (fun γ => acceptanceSet 𝒳 γ) '' Γ₀
      (∀ X : 𝒳.carrier, IsLeast ((fun γ => γ X) '' Γ₀) (ρ X)) ∧
      (∀ 𝒜 ∈ 𝔄₀, IsConvexAcceptanceSet 𝒳 𝒜) ∧
      ∀ X : 𝒳.carrier, IsLeast {m : ℝ | ∃ 𝒜 ∈ 𝔄₀, X - 𝒳.const m ∈ 𝒜} (ρ X)) := by
  exact theorem2_star_shaped_iff_min_convex 𝒳 ρ hρ

#check solution
#print axioms solution
