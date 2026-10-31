-- Prove2me | solution 1 for Viterbo.cEHZ_pentagonK_prod_pentagonT
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:49:15.947989+00:00
-- url     : https://prove2.me/submissions/e3249829-d5ce-40a3-8cb6-25f49a8709bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Viterbo
import Definitions.Def_SymmetricPolar
import Theorems.Thm_Viterbo_cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable
import Theorems.Thm_Viterbo_isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard
import Mathlib

section
section
/-!
# Viterbo pentagon, Part A: support function of `T`, convex domains, the diagonal billiards,
and the witness of the minimum.
-/

set_option linter.unusedSimpArgs false

namespace Viterbo.PentA

open Viterbo OAI.SymmetricPolar Set Real

/-! ## Constants -/

/-- `c = cos (π/5)`. -/
noncomputable def cc : ℝ := Real.cos (π / 5)
/-- `S = sin (π/5)`. -/
noncomputable def ss : ℝ := Real.sin (π / 5)

lemma ss_pos : 0 < ss := by
  unfold ss
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · linarith [Real.pi_pos]

lemma cc_bounds : 0.809 < cc ∧ cc < 0.80903 := by
  have h := Real.cos_pi_div_five
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  simp only [cc]; rw [h]
  constructor <;> nlinarith

/-! ## Trig values -/

lemma cos4 : Real.cos (4 * π / 5) = -cc := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.cos_pi_sub]; rfl
lemma sin4 : Real.sin (4 * π / 5) = ss := by
  rw [show 4 * π / 5 = π - π / 5 by ring, Real.sin_pi_sub]; rfl
lemma cos6 : Real.cos (6 * π / 5) = -cc := by
  rw [show 6 * π / 5 = π / 5 + π by ring, Real.cos_add_pi]; rfl
lemma sin6 : Real.sin (6 * π / 5) = -ss := by
  rw [show 6 * π / 5 = π / 5 + π by ring, Real.sin_add_pi]; rfl

/-! ## Coordinates -/

lemma rv_eq (k : ℕ) : rotatedVertex k = !₂[Real.sin (2 * π * k / 5), -Real.cos (2 * π * k / 5)] := by
  unfold rotatedVertex
  rw [show -(π / 2) + 2 * π * k / 5 = 2 * π * k / 5 - π / 2 by ring, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two]

/-! ## Values at `2πk/5` -/

lemma C0 : Real.cos (2 * π * ((0:ℕ):ℝ) / 5) = 1 := by
  simp
lemma S0 : Real.sin (2 * π * ((0:ℕ):ℝ) / 5) = 0 := by
  simp
lemma C2 : Real.cos (2 * π * ((2:ℕ):ℝ) / 5) = -cc := by
  rw [show 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, cos4]
lemma S2 : Real.sin (2 * π * ((2:ℕ):ℝ) / 5) = ss := by
  rw [show 2 * π * ((2:ℕ):ℝ) / 5 = 4 * π / 5 by push_cast; ring, sin4]
lemma C3 : Real.cos (2 * π * ((3:ℕ):ℝ) / 5) = -cc := by
  rw [show 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, cos6]
lemma S3 : Real.sin (2 * π * ((3:ℕ):ℝ) / 5) = -ss := by
  rw [show 2 * π * ((3:ℕ):ℝ) / 5 = 6 * π / 5 by push_cast; ring, sin6]

lemma pv0 (k : ℕ) : pentagonVertex k 0 = Real.cos (2 * π * k / 5) := rfl
lemma pv1 (k : ℕ) : pentagonVertex k 1 = Real.sin (2 * π * k / 5) := rfl
lemma rv0 (k : ℕ) : rotatedVertex k 0 = Real.sin (2 * π * k / 5) := by rw [rv_eq]; rfl
lemma rv1 (k : ℕ) : rotatedVertex k 1 = -Real.cos (2 * π * k / 5) := by rw [rv_eq]; rfl


/-! ## Vertex coordinates -/

lemma pv_0_0 : pentagonVertex 0 0 = 1 := by rw [pv0, C0]
lemma pv_0_1 : pentagonVertex 0 1 = 0 := by rw [pv1, S0]
lemma rv_0_0 : rotatedVertex 0 0 = 0 := by rw [rv0, S0]
lemma rv_0_1 : rotatedVertex 0 1 = -(1) := by rw [rv1, C0]
lemma pv_2_0 : pentagonVertex 2 0 = -cc := by rw [pv0, C2]
lemma pv_2_1 : pentagonVertex 2 1 = ss := by rw [pv1, S2]
lemma rv_2_0 : rotatedVertex 2 0 = ss := by rw [rv0, S2]
lemma rv_2_1 : rotatedVertex 2 1 = cc := by rw [rv1, C2, neg_neg]
lemma pv_3_0 : pentagonVertex 3 0 = -cc := by rw [pv0, C3]
lemma pv_3_1 : pentagonVertex 3 1 = -ss := by rw [pv1, S3]
lemma rv_3_0 : rotatedVertex 3 0 = -ss := by rw [rv0, S3]
lemma rv_3_1 : rotatedVertex 3 1 = cc := by rw [rv1, C3, neg_neg]

/-! ## Hulls of five points -/

lemma mem_hull5 (f : ℕ → Position 2) {k : ℕ} (hk : k < 5) :
    f k ∈ convexHull ℝ (f '' ↑(Finset.range 5)) :=
  subset_convexHull ℝ _ ⟨k, by simpa using hk, rfl⟩

/-! ## Interior, frontier, normal cones -/

/-! ## Convex domains -/

lemma isBounded_hull5 (f : ℕ → Position 2) :
    Bornology.IsBounded (convexHull ℝ (f '' ↑(Finset.range 5))) :=
  isBounded_convexHull.mpr ((Finset.range 5).finite_toSet.image f).isBounded

lemma cc_pos : 0 < cc := by linarith [cc_bounds.1]

lemma zero_mem_interior_T : (0 : Position 2) ∈ interior pentagonT := by
  have hss := ss_pos
  have hcc := cc_pos
  have hU : IsOpen ({x : Position 2 | 0 < cc - x 1} ∩ ({x : Position 2 | 0 < (1 - (cc - x 1) / (1 + cc)) + x 0 / ss} ∩
      {x : Position 2 | 0 < (1 - (cc - x 1) / (1 + cc)) - x 0 / ss})) := by
    refine (isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop)))
  refine interior_maximal ?_ hU ⟨?_, ?_, ?_⟩
  · rintro x ⟨h0, h2, h3⟩
    simp only [mem_ofPred_eq] at h0 h2 h3
    set l0 := (cc - x 1) / (1 + cc) with hl0
    have hx : x = ∑ i : Fin 3, (![l0, ((1 - l0) + x 0 / ss) / 2, ((1 - l0) - x 0 / ss) / 2] i) •
        (![rotatedVertex 0, rotatedVertex 2, rotatedVertex 3] i) := by
      ext i
      fin_cases i <;>
      simp [Fin.sum_univ_three, rv_0_0, rv_0_1, rv_2_0, rv_2_1, rv_3_0, rv_3_1, hl0] <;> field_simp <;> ring
    rw [hx]
    apply (convex_convexHull ℝ _).sum_mem
    · intro i _
      fin_cases i <;> simp <;> [positivity; linarith; linarith]
    · simp [Fin.sum_univ_three]; ring
    · intro i _
      fin_cases i <;> exact mem_hull5 _ (by norm_num)
  all_goals simp only [mem_ofPred_eq, PiLp.zero_apply]
  · linarith
  · simp only [zero_add, zero_div, add_zero, sub_zero]
    have := (div_lt_one (by linarith : (0:ℝ) < 1 + cc)).mpr (by linarith : cc < 1 + cc); linarith
  · simp only [zero_add, zero_div, add_zero, sub_zero]
    have := (div_lt_one (by linarith : (0:ℝ) < 1 + cc)).mpr (by linarith : cc < 1 + cc); linarith

lemma zero_mem_interior_K : (0 : Position 2) ∈ interior pentagonK := by
  have hss := ss_pos
  have hcc := cc_pos
  have hU : IsOpen ({x : Position 2 | 0 < x 0 + cc} ∩ ({x : Position 2 | 0 < (1 - (x 0 + cc) / (1 + cc)) + x 1 / ss} ∩
      {x : Position 2 | 0 < (1 - (x 0 + cc) / (1 + cc)) - x 1 / ss})) := by
    refine (isOpen_lt continuous_const (by fun_prop)).inter
      ((isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop)))
  refine interior_maximal ?_ hU ⟨?_, ?_, ?_⟩
  · rintro x ⟨h0, h2, h3⟩
    simp only [mem_ofPred_eq] at h0 h2 h3
    set l0 := (x 0 + cc) / (1 + cc) with hl0
    have hx : x = ∑ i : Fin 3, (![l0, ((1 - l0) + x 1 / ss) / 2, ((1 - l0) - x 1 / ss) / 2] i) •
        (![pentagonVertex 0, pentagonVertex 2, pentagonVertex 3] i) := by
      ext i
      fin_cases i <;>
      simp [Fin.sum_univ_three, pv_0_0, pv_0_1, pv_2_0, pv_2_1, pv_3_0, pv_3_1, hl0] <;> field_simp <;> ring
    rw [hx]
    apply (convex_convexHull ℝ _).sum_mem
    · intro i _
      fin_cases i <;> simp <;> [positivity; linarith; linarith]
    · simp [Fin.sum_univ_three]; ring
    · intro i _
      fin_cases i <;> exact mem_hull5 _ (by norm_num)
  all_goals simp only [mem_ofPred_eq, PiLp.zero_apply]
  · linarith
  · simp only [zero_add, zero_div, add_zero, sub_zero]
    have := (div_lt_one (by linarith : (0:ℝ) < 1 + cc)).mpr (by linarith : cc < 1 + cc); linarith
  · simp only [zero_add, zero_div, add_zero, sub_zero]
    have := (div_lt_one (by linarith : (0:ℝ) < 1 + cc)).mpr (by linarith : cc < 1 + cc); linarith

theorem isConvexDomain_pentagonK : IsConvexDomain pentagonK :=
  ⟨isBounded_hull5 _, convex_convexHull ℝ _, ⟨0, zero_mem_interior_K⟩⟩

theorem isConvexDomain_pentagonT : IsConvexDomain pentagonT :=
  ⟨isBounded_hull5 _, convex_convexHull ℝ _, ⟨0, zero_mem_interior_T⟩⟩

/-! ## The diagonal billiards -/

end Viterbo.PentA

end
end

section
section
namespace Viterbo.CEHZStep

theorem convK : Viterbo.IsConvexDomain Viterbo.pentagonK := Viterbo.PentA.isConvexDomain_pentagonK
theorem convT : Viterbo.IsConvexDomain Viterbo.pentagonT := Viterbo.PentA.isConvexDomain_pentagonT
theorem zeroT : (0 : OAI.SymmetricPolar.Position 2) ∈ interior Viterbo.pentagonT := Viterbo.PentA.zero_mem_interior_T

theorem step :
    Viterbo.cEHZ (Viterbo.pentagonK ×ˢ Viterbo.pentagonT) =
      ENNReal.ofReal (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) := by
  obtain ⟨L, hL, -, -, -, ⟨m, q, hm, hq, hlen⟩, hmin⟩ :=
    Viterbo.cEHZ_prod_eq_min_action_and_min_billiard_and_min_notTranslatable 2 (by norm_num)
      Viterbo.pentagonK Viterbo.pentagonT convK convT zeroT
  have hI := (Viterbo.isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard).1
  have hLeast : IsLeast {L : ℝ | ∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position 2), m ≤ 3 ∧
        Viterbo.NotTranslatableIntoInterior Viterbo.pentagonK q ∧
        L = Viterbo.polygonLength Viterbo.pentagonT q} L := by
    refine ⟨⟨m, q, by omega, hq, hlen.symm⟩, ?_⟩
    rintro x ⟨m', q', hm', hq', rfl⟩
    exact hmin m' q' (by omega) hq'
  rw [hL, hLeast.unique hI]

end Viterbo.CEHZStep

theorem Viterbo.cEHZ_pentagonK_prod_pentagonT : Viterbo.cEHZ (Viterbo.pentagonK ×ˢ Viterbo.pentagonT) =
      ENNReal.ofReal (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) :=
  Viterbo.CEHZStep.step

end
end

section
open Viterbo

theorem solution :
    cEHZ (pentagonK ×ˢ pentagonT) =
      ENNReal.ofReal (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) := by
  apply Viterbo.cEHZ_pentagonK_prod_pentagonT <;> assumption

end
