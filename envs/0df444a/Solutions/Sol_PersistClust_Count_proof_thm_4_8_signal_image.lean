-- Prove2me | solution 1 for PersistClust.Count.proof_thm_4_8_signal_image
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T08:15:44.723679+00:00
-- url     : https://prove2.me/submissions/2ed39893-b7a0-407e-91c8-eae0f276c8c1

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram

/-!
# Theorem 4.8, signal image (Regions III and V)

Every off-diagonal copy `q` of `D` whose base point lies in `Δ^S_{d₂} ∩ Λ^E_{d₂}`
(death `≤ birth − d₂`, birth `> d₂`) is mapped by the multi-bijection `γ` to a
point outside `Δ^N_{d₁+2cδ} ∪ Λ^W_{d₁+2cδ}`.

Paper (RR-6968, proof of Theorem 4.8, Regions III–V), writing `r = cδ`:
* Region III (`y > r`): the source lies in `Q^NE_r`, so by assertion (i) both
  coordinates of the image are `r`-close to the source's; hence
  `y' ≤ x − d₂ + 2r ≤ x − (d₁+2r)` because `d₂ ≥ d₁ + 4r`, and `x' > d₂ − r`.
* Region V (`y ≤ r`): the source lies in `Q^SE_r`, so by assertion (iii) the
  image satisfies `x' > d₂ − r`; moreover `y' ≤ 2r` (otherwise the image would
  lie in `Q^NE_r` and assertion (ii), applied to the image, would force the
  source to have `y > r`). Hence `y' ≤ x' − (d₁+2r)` because `d₂ ≥ d₁ + 5r`.

All computations are done directly in `EReal` using the arithmetic lemmas of
Mathlib, so the degenerate values `±∞` need no separate treatment.
-/

open PersistClust.Count

/-- If `x₀ ≤ x + r` (an upper bound on the image coordinate `x` in terms of the
source coordinate `x₀`) and `d₂ < x₀`, then `d₂ − r < x`. -/
theorem signal_image_lower_bound {x₀ x : EReal} {r d₂ : ℝ}
    (h : x₀ ≤ x + ((r : ℝ) : EReal)) (hd : ((d₂ : ℝ) : EReal) < x₀) :
    (((d₂ - r : ℝ)) : EReal) < x := by
  have h1 : ((d₂ : ℝ) : EReal) < x + ((r : ℝ) : EReal) := lt_of_lt_of_le hd h
  have h2 := EReal.sub_lt_of_lt_add h1
  rw [← EReal.coe_sub] at h2
  exact h2

/-- Additive form of `y ≤ x − D` for extended reals (`D` a real). -/
theorem signal_image_le_sub {y x : EReal} {D : ℝ}
    (h : y + ((D : ℝ) : EReal) ≤ x) : y ≤ x - ((D : ℝ) : EReal) :=
  (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot D))
    (Or.inl (EReal.coe_ne_top D))).mpr h

/-- Region III key estimate: if the image's death `y'` is `r`-close above the
source's death `y₀`, the source lies `d₂`-below its birth (`y₀ + d₂ ≤ x₀`), the
image's birth `x` is `r`-close above the source's birth (`x₀ ≤ x + r`), and
`r + (D + r) ≤ d₂`, then `y' + D ≤ x`. -/
theorem signal_image_key_caseA {y' y₀ x₀ x : EReal} {r D d₂ : ℝ}
    (hy' : y' ≤ y₀ + ((r : ℝ) : EReal)) (hΔ : y₀ + ((d₂ : ℝ) : EReal) ≤ x₀)
    (hx₀ : x₀ ≤ x + ((r : ℝ) : EReal)) (hsum : r + (D + r) ≤ d₂) :
    y' + ((D : ℝ) : EReal) ≤ x := by
  have key : y' + (((D + r : ℝ)) : EReal) ≤ x₀ :=
    calc y' + (((D + r : ℝ)) : EReal)
        ≤ (y₀ + ((r : ℝ) : EReal)) + (((D + r : ℝ)) : EReal) := add_le_add_left hy' _
      _ = y₀ + (((r : ℝ) : EReal) + (((D + r : ℝ)) : EReal)) := add_assoc _ _ _
      _ = y₀ + (((r + (D + r) : ℝ)) : EReal) := by rw [← EReal.coe_add]
      _ ≤ y₀ + ((d₂ : ℝ) : EReal) := add_le_add_right (EReal.coe_le_coe hsum) _
      _ ≤ x₀ := hΔ
  have key2 : y' + ((D : ℝ) : EReal) + ((r : ℝ) : EReal) ≤ x₀ := by
    rw [add_assoc, ← EReal.coe_add]
    exact key
  have key3 : y' + ((D : ℝ) : EReal) ≤ x₀ - ((r : ℝ) : EReal) :=
    (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot r))
      (Or.inl (EReal.coe_ne_top r))).mpr key2
  exact le_trans key3 (EReal.sub_le_of_le_add hx₀)

theorem solution
    (D D' : EReal × EReal → ℕ∞) (hD : IsDiagramLike D) (hD' : IsDiagramLike D')
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (γ : Copies D ≃ Copies D') (hγ : SatisfiesIIV γ (c * δ) (c * δ))
    (d₁ d₂ : ℝ) (hd₁ : 0 ≤ d₁) (hδc : δ < (d₂ - d₁) / (5 * c))
    (hsep : IsSeparated D d₁ d₂) :
    ∀ (q : (EReal × EReal) × ℕ) (hq : (q.2 : ℕ∞) < D q.1), q.1 ∈ DeltaS d₂ ∩ LamE d₂ →
      pt (γ (Sum.inl ⟨q, hq⟩)) ∉ DeltaN (d₁ + 2 * c * δ) ∪ LamW (d₁ + 2 * c * δ) := by
  intro q hq hqin
  obtain ⟨hi, hii, hiii, hiv⟩ := hγ
  set a : Copies D := Sum.inl ⟨q, hq⟩ with ha
  have hpt_a : pt a = q.1 := by rw [ha]; rfl
  obtain ⟨hDeltaS, hLamE⟩ := hqin
  have hLamE' : ((d₂ : ℝ) : EReal) < q.1.1 := hLamE
  have hDeltaS' : q.1.2 ≤ q.1.1 - ((d₂ : ℝ) : EReal) := hDeltaS
  -- basic real inequalities; from now on `r = c * δ` and `d₁ + 5r < d₂`
  have hcδ : 0 < c * δ := mul_pos hc hδ
  have hd2 : d₁ + 5 * (c * δ) < d₂ := by
    have h5c : (0 : ℝ) < 5 * c := by positivity
    have h := (lt_div_iff₀ h5c).mp hδc
    linarith
  -- `r < x₀` because `x₀ > d₂`
  have hxr : ((c * δ : ℝ) : EReal) < q.1.1 :=
    lt_trans (EReal.coe_lt_coe_iff.mpr (by linarith)) hLamE'
  -- the source's death is `d₂`-below its birth, in additive form
  have hD_le : q.1.2 + ((d₂ : ℝ) : EReal) ≤ q.1.1 := EReal.add_le_of_le_sub hDeltaS'
  by_cases hy0 : q.1.2 ≤ ((c * δ : ℝ) : EReal)
  · -- Region V: `y₀ ≤ r`, so `pt a ∈ Q^SE_r`
    have hmem : pt a ∈ QSE (c * δ) := by rw [hpt_a]; exact ⟨hxr, hy0⟩
    have hclose := hiii a hmem
    rw [hpt_a] at hclose
    have hx01 : q.1.1 ≤ (pt (γ a)).1 + ((c * δ : ℝ) : EReal) := hclose.1
    have hx_low : (((d₂ - c * δ : ℝ)) : EReal) < (pt (γ a)).1 :=
      signal_image_lower_bound hx01 hLamE'
    have hgoal1 : ((d₁ + 2 * c * δ : ℝ) : EReal) < (pt (γ a)).1 :=
      lt_trans (EReal.coe_lt_coe_iff.mpr (by linarith)) hx_low
    have hgoal2 : (pt (γ a)).2 ≤ (pt (γ a)).1 - ((d₁ + 2 * c * δ : ℝ) : EReal) := by
      refine signal_image_le_sub ?_
      by_cases hy' : (pt (γ a)).2 ≤ ((c * δ : ℝ) : EReal)
      · -- sub-case `y' ≤ r`: then `y' + D ≤ r + D < d₂ - r < x`
        have h1 : (pt (γ a)).2 + ((d₁ + 2 * c * δ : ℝ) : EReal) ≤
            ((c * δ : ℝ) : EReal) + ((d₁ + 2 * c * δ : ℝ) : EReal) :=
          add_le_add_left hy' _
        have h2 : ((c * δ : ℝ) : EReal) + ((d₁ + 2 * c * δ : ℝ) : EReal) ≤
            (((d₂ - c * δ : ℝ)) : EReal) := by
          rw [← EReal.coe_add]
          exact EReal.coe_le_coe_iff.mpr (by linarith)
        exact le_trans (le_trans h1 h2) (le_of_lt hx_low)
      · -- sub-case `r < y'`: the image lies in `Q^NE_r`, so (ii) forces `y' ≤ y₀ + r ≤ 2r`
        have hy'r : ((c * δ : ℝ) : EReal) < (pt (γ a)).2 := not_le.mp hy'
        have hx'r : ((c * δ : ℝ) : EReal) < (pt (γ a)).1 :=
          lt_trans (EReal.coe_lt_coe_iff.mpr (by linarith)) hx_low
        have hmem2 : pt (γ a) ∈ QNE (c * δ) := ⟨hx'r, hy'r⟩
        have hh := hii (γ a) hmem2
        rw [Equiv.symm_apply_apply] at hh
        rw [hpt_a] at hh
        have hy'2 : (pt (γ a)).2 ≤ q.1.2 + ((c * δ : ℝ) : EReal) := hh.2.2
        have hy'3 : (pt (γ a)).2 ≤ (((2 * (c * δ) : ℝ)) : EReal) :=
          le_trans hy'2
            (le_trans (add_le_add_left hy0 ((c * δ : ℝ) : EReal))
              (by rw [← EReal.coe_add]; exact EReal.coe_le_coe_iff.mpr (by linarith)))
        have h1 : (pt (γ a)).2 + ((d₁ + 2 * c * δ : ℝ) : EReal) ≤
            (((2 * (c * δ) : ℝ)) : EReal) + ((d₁ + 2 * c * δ : ℝ) : EReal) :=
          add_le_add_left hy'3 _
        have h2 : (((2 * (c * δ) : ℝ)) : EReal) + ((d₁ + 2 * c * δ : ℝ) : EReal) ≤
            (((d₂ - c * δ : ℝ)) : EReal) := by
          rw [← EReal.coe_add]
          exact EReal.coe_le_coe_iff.mpr (by linarith)
        exact le_trans (le_trans h1 h2) (le_of_lt hx_low)
    intro hmem3
    simp only [Set.mem_union, Set.mem_ofPred_eq, DeltaN, LamW] at hmem3
    obtain h | h := hmem3
    · exact absurd (lt_of_le_of_lt hgoal2 h) (lt_irrefl _)
    · exact absurd (lt_of_le_of_lt h hgoal1) (lt_irrefl _)
  · -- Region III: `r < y₀`, so `pt a ∈ Q^NE_r`
    have hy0r : ((c * δ : ℝ) : EReal) < q.1.2 := not_le.mp hy0
    have hmem : pt a ∈ QNE (c * δ) := by rw [hpt_a]; exact ⟨hxr, hy0r⟩
    have hclose := hi a hmem
    rw [hpt_a] at hclose
    have hx01 : q.1.1 ≤ (pt (γ a)).1 + ((c * δ : ℝ) : EReal) := hclose.1.1
    have hx_low : (((d₂ - c * δ : ℝ)) : EReal) < (pt (γ a)).1 :=
      signal_image_lower_bound hx01 hLamE'
    have hgoal1 : ((d₁ + 2 * c * δ : ℝ) : EReal) < (pt (γ a)).1 :=
      lt_trans (EReal.coe_lt_coe_iff.mpr (by linarith)) hx_low
    have hgoal2 : (pt (γ a)).2 ≤ (pt (γ a)).1 - ((d₁ + 2 * c * δ : ℝ) : EReal) := by
      refine signal_image_le_sub ?_
      exact signal_image_key_caseA hclose.2.2 hD_le hx01 (by linarith)
    intro hmem3
    simp only [Set.mem_union, Set.mem_ofPred_eq, DeltaN, LamW] at hmem3
    obtain h | h := hmem3
    · exact absurd (lt_of_le_of_lt hgoal2 h) (lt_irrefl _)
    · exact absurd (lt_of_le_of_lt h hgoal1) (lt_irrefl _)
