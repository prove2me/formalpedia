-- Prove2me | solution 1 for OddOrder.Peterfalvi.S09.reduced_inequality_of_estimates
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T07:34:43.653723+00:00
-- url     : https://prove2.me/submissions/868461aa-51cf-456d-b50a-42ae6e4d8d0f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/Hypothesis71.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_Hypothesis71

-- ===== OddOrder/Peterfalvi/S09_NonexistenceCertain/Hypothesis71.lean =====
namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_4_to_7_5

open scoped Classical in
/-- Reduced form of the family inequality used in Peterfalvi (7.10).

Starting from (7.5), it inserts:
* the identity contribution on `G₀`, expressed as
  `1 ≤ Σ_{g∈G₀} |χ(g)|²`;
* a lower bound `c ≤ ‖χ^{ρ_i}‖²` for the distinguished index;
* nonnegative contributions for the indices outside the chosen `𝓑`-set.

The output is exactly the real-valued reduced inequality later converted into
the `CharacterEstimateData.base_estimate` field. -/
theorem _root_.solution {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {k : ℕ}
    (F : FamilyHypothesis71 G k)
    (χ : ClassFunction G ℂ) (hχ : ClassFunction.inner χ χ = 1)
    (i : Fin k) (B : Finset (Fin k)) (c : ℝ)
    (hB_ne : ∀ j ∈ B, i ≠ j)
    (hG0 :
      (1 : ℝ) ≤
        ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0),
          ‖(χ : G → ℂ) g‖ ^ 2)
    (hi : c ≤ F.chiRhoNormSq χ i)
    (hgood : ∀ j : Fin k, i ≠ j → j ∉ B →
      (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ) ≤
        F.chiRhoNormSq χ j) :
    ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
        (c - (Nat.card (F.A i) : ℝ) / (Nat.card (F.L i) : ℝ) -
          ∑ j ∈ B, (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ)) ≤ 0 := by
  classical
  let ratio : Fin k → ℝ := fun j =>
    (Nat.card (F.A j) : ℝ) / (Nat.card (F.L j) : ℝ)
  let term : Fin k → ℝ := fun j => F.chiRhoNormSq χ j - ratio j
  let g0sum : ℝ :=
    ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ F.G0), ‖(χ : G → ℂ) g‖ ^ 2
  let g0term : ℝ := (Nat.card G : ℝ)⁻¹ * (g0sum - (Nat.card F.G0 : ℝ))
  have h75 : g0term + ∑ j : Fin k, term j ≤ 0 := by
    simpa [g0term, g0sum, term, ratio] using family_inequality F χ hχ
  have hG_pos : (0 : ℝ) < Nat.card G := by exact_mod_cast Nat.card_pos (α := G)
  have hG0_lower :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) ≤ g0term := by
    have hsub :
        1 - (Nat.card F.G0 : ℝ) ≤ g0sum - (Nat.card F.G0 : ℝ) := by
      dsimp [g0sum]
      linarith [hG0]
    have hmul := mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hG_pos.le)
    calc
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ))
          = (Nat.card G : ℝ)⁻¹ * (1 - (Nat.card F.G0 : ℝ)) := by
              rw [div_eq_inv_mul, mul_comm]
      _ ≤ (Nat.card G : ℝ)⁻¹ * (g0sum - (Nat.card F.G0 : ℝ)) := hmul
      _ = g0term := rfl
  have hnorm_nonneg : ∀ j : Fin k, 0 ≤ F.chiRhoNormSq χ j := by
    intro j
    let : Fintype (F.L j) := F.fintypeL j
    let : Invertible (Nat.card (F.L j) : ℂ) := F.invertibleL j
    simpa [FamilyHypothesis71.chiRhoNormSq] using
      Hypothesis71.ClassFunction.inner_self_re_nonneg ((F.hyp71 j).chiRhoCF χ)
  have hterm_i : c - ratio i ≤ term i := by
    dsimp [term]
    linarith [hi]
  have hB_bound : -(∑ j ∈ B, ratio j) ≤ ∑ j ∈ B, term j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have hnonneg := hnorm_nonneg j
    dsimp [term]
    linarith
  have hB_subset : B ⊆ (Finset.univ : Finset (Fin k)).erase i := by
    intro j hj
    rw [Finset.mem_erase]
    exact ⟨(hB_ne j hj).symm, by simp⟩
  have hB_to_erase :
      (∑ j ∈ B, term j) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, term j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hB_subset ?_
    intro j hj_erase hjB
    rw [Finset.mem_erase] at hj_erase
    have hij : i ≠ j := hj_erase.1.symm
    have hj_good := hgood j hij hjB
    dsimp [term]
    linarith
  have hsum_terms :
      c - ratio i - ∑ j ∈ B, ratio j ≤ ∑ j : Fin k, term j := by
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin k)) term
      (Finset.mem_univ i)
    linarith
  have htarget :
      ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
          (c - ratio i - ∑ j ∈ B, ratio j) ≤ 0 := by
    have hle :
        ((1 - (Nat.card F.G0 : ℝ)) / (Nat.card G : ℝ)) +
            (c - ratio i - ∑ j ∈ B, ratio j) ≤
          g0term + ∑ j : Fin k, term j := by
      linarith
    exact le_trans hle h75
  simpa [ratio] using htarget

end Section_7_4_to_7_5

end OddOrder.Peterfalvi.S09
