-- Prove2me | solution 1 for TalagrandConc.LinearSuprema.eq_8_1_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T06:03:54.507974+00:00
-- url     : https://prove2.me/submissions/c0a2ce41-6f55-45f2-963a-64b916563745

import Mathlib
import Definitions.Def_TalagrandConc_LinearSuprema_Basic



namespace TalagrandConc.LinearSuprema

open scoped ENNReal

/-- weight of the disagreement set -/
noncomputable def disWeight {N : ℕ} (α x y : Fin N → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => y i ≠ x i), |α i|

lemma disWeight_nonneg {N : ℕ} (α x y : Fin N → ℝ) : 0 ≤ disWeight α x y :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- any point of the mismatch hull dominates the disagreement weight of some point of `A` -/
lemma exists_disWeight_le_of_mem_hull {N : ℕ} (A : Set (Fin N → ℝ)) (x : Fin N → ℝ)
    (α : Fin N → ℝ) (s : Fin N → ℝ) (hs : s ∈ mismatchHull A x) :
    ∃ y ∈ A, disWeight α x y ≤ ∑ i, |α i| * s i := by
  let P : Set (Fin N → ℝ) := {s | ∃ y ∈ A, disWeight α x y ≤ ∑ i, |α i| * s i}
  have hsub : mismatchVectors A x ⊆ P := by
    rintro s ⟨hs01, y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    unfold disWeight
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : y i ≠ x i
    · rw [if_pos h]
      have : s i = 1 := by
        rcases hs01 i with h0 | h1
        · exact absurd (hxy i h0).symm h
        · exact h1
      rw [this, mul_one]
    · rw [if_neg h]
      rcases hs01 i with h0 | h1
      · rw [h0, mul_zero]
      · rw [h1, mul_one]; exact abs_nonneg _
  have hconv : Convex ℝ P := by
    intro s hs t ht a b ha hb hab
    obtain ⟨ys, hys, hs'⟩ := hs
    obtain ⟨yt, hyt, ht'⟩ := ht
    have key : ∑ i, |α i| * (a • s + b • t) i = a * ∑ i, |α i| * s i + b * ∑ i, |α i| * t i := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rcases le_total (disWeight α x ys) (disWeight α x yt) with h | h
    · refine ⟨ys, hys, ?_⟩
      rw [key]
      calc disWeight α x ys = a * disWeight α x ys + b * disWeight α x ys := by
            rw [← add_mul, hab, one_mul]
        _ ≤ a * ∑ i, |α i| * s i + b * ∑ i, |α i| * t i := by
            gcongr
            exact h.trans ht'
    · refine ⟨yt, hyt, ?_⟩
      rw [key]
      calc disWeight α x yt = a * disWeight α x yt + b * disWeight α x yt := by
            rw [← add_mul, hab, one_mul]
        _ ≤ a * ∑ i, |α i| * s i + b * ∑ i, |α i| * t i := by
            gcongr
            exact h.trans hs'
  exact convexHull_min hsub hconv hs

lemma cs_abs {N : ℕ} (α s : Fin N → ℝ) :
    ∑ i, |α i| * s i ≤ coeffNorm α * Real.sqrt (∑ i, s i ^ 2) := by
  unfold coeffNorm
  have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |α i|) s
  simpa [sq_abs] using this

/-- a point of `A` minimizing the disagreement weight -/
lemma exists_min_disWeight {N : ℕ} (A : Set (Fin N → ℝ)) (hA : A.Nonempty) (x α : Fin N → ℝ) :
    ∃ y ∈ A, ∀ z ∈ A, disWeight α x y ≤ disWeight α x z := by
  let T : Set ℝ := (fun y => disWeight α x y) '' A
  have hTfin : T.Finite := by
    apply Set.Finite.subset (Set.finite_range (fun I : Finset (Fin N) => ∑ i ∈ I, |α i|))
    rintro _ ⟨y, _, rfl⟩
    exact ⟨Finset.univ.filter (fun i => y i ≠ x i), rfl⟩
  have hTne : T.Nonempty := hA.image _
  obtain ⟨v, ⟨y, hy, rfl⟩, hmin⟩ := Set.exists_min_image T id hTfin hTne
  exact ⟨y, hy, fun z hz => hmin _ ⟨z, hz, rfl⟩⟩

/-- Lemma 4.1.2 in ENNReal form -/
lemma lemma_4_1_2_core {N : ℕ} (A : Set (Fin N → ℝ)) (hA : A.Nonempty) (x α : Fin N → ℝ) :
    ∃ y ∈ A, ENNReal.ofReal (disWeight α x y) ≤
      ENNReal.ofReal (coeffNorm α) * convexDistance A x := by
  obtain ⟨y, hy, hmin⟩ := exists_min_disWeight A hA x α
  refine ⟨y, hy, ?_⟩
  -- for every s in the hull: disWeight α x y ≤ ‖α‖ * ‖s‖
  have hpt : ∀ s ∈ mismatchHull A x,
      disWeight α x y ≤ coeffNorm α * Real.sqrt (∑ i, s i ^ 2) := by
    intro s hs
    obtain ⟨z, hz, hzs⟩ := exists_disWeight_le_of_mem_hull A x α s hs
    exact (hmin z hz).trans (hzs.trans (cs_abs α s))
  have hcn : 0 ≤ coeffNorm α := Real.sqrt_nonneg _
  by_cases h0 : coeffNorm α = 0
  · -- then the weight is zero (hull nonempty)
    have hs1 : (fun _ : Fin N => (1 : ℝ)) ∈ mismatchHull A x := by
      apply subset_convexHull
      obtain ⟨z, hz⟩ := hA
      exact ⟨fun i => Or.inr rfl, z, hz, fun i h => absurd h one_ne_zero⟩
    have := hpt _ hs1
    rw [h0, zero_mul] at this
    have : disWeight α x y = 0 := le_antisymm this (disWeight_nonneg _ _ _)
    rw [this, ENNReal.ofReal_zero]; exact zero_le
  · have hne : ENNReal.ofReal (coeffNorm α) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact lt_of_le_of_ne hcn (Ne.symm h0)
    rw [← ENNReal.div_le_iff' hne ENNReal.ofReal_ne_top]
    unfold convexDistance
    refine le_iInf₂ fun s hs => ?_
    rw [ENNReal.div_le_iff' hne ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul hcn]
    exact ENNReal.ofReal_le_ofReal (hpt s hs)

lemma coeffNorm_le_sigma {N : ℕ} (F : Set (Fin N → ℝ)) (hσfinite : BddAbove (coeffNorm '' F))
    (α : Fin N → ℝ) (hα : α ∈ F) : coeffNorm α ≤ sigma F :=
  le_csSup hσfinite ⟨α, hα, rfl⟩

theorem eq_8_1_3_core {N : ℕ} (F : Set (Fin N → ℝ))
    (hσfinite : BddAbove (coeffNorm '' F))
    (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hA : (linearSublevel F r a).Nonempty)
    (α : Fin N → ℝ) (hα : α ∈ F) :
    ∃ y ∈ linearSublevel F r a,
      ENNReal.ofReal (∑ i ∈ Finset.univ.filter (fun i => y i ≠ x i), |α i|) ≤
          ENNReal.ofReal (coeffNorm α) * convexDistance (linearSublevel F r a) x ∧
        ENNReal.ofReal (coeffNorm α) * convexDistance (linearSublevel F r a) x ≤
          ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by
  obtain ⟨y, hy, hle⟩ := lemma_4_1_2_core (linearSublevel F r a) hA x α
  refine ⟨y, hy, hle, ?_⟩
  gcongr
  exact coeffNorm_le_sigma F hσfinite α hα

/-- the linear forms are bounded on bounded inputs -/
lemma bddAbove_forms {N : ℕ} (F : Set (Fin N → ℝ)) (hσfinite : BddAbove (coeffNorm '' F))
    (z : Fin N → ℝ) : BddAbove ((fun α : Fin N → ℝ => ∑ i, α i * z i) '' F) := by
  obtain ⟨B, hB⟩ := hσfinite
  refine ⟨B * Real.sqrt (∑ i, z i ^ 2), ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  have hB' : coeffNorm α ≤ B := hB ⟨α, hα, rfl⟩
  calc ∑ i, α i * z i ≤ coeffNorm α * Real.sqrt (∑ i, z i ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ α z
    _ ≤ B * Real.sqrt (∑ i, z i ^ 2) := by gcongr

lemma mismatchHull_empty {N : ℕ} (x : Fin N → ℝ) :
    mismatchHull (∅ : Set (Fin N → ℝ)) x = ∅ := by
  unfold mismatchHull
  have : mismatchVectors (∅ : Set (Fin N → ℝ)) x = ∅ := by
    ext s; simp [mismatchVectors]
  rw [this, convexHull_empty]

lemma convexDistance_empty {N : ℕ} (x : Fin N → ℝ) :
    convexDistance (∅ : Set (Fin N → ℝ)) x = ⊤ := by
  unfold convexDistance
  rw [mismatchHull_empty]
  simp

theorem eq_8_1_2_core {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ENNReal.ofReal (linearSupremum F (fun i => r i + x i) - a) ≤
      ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by
  by_cases hA : (linearSublevel F r a).Nonempty
  · have key : ∀ α ∈ F, ENNReal.ofReal (∑ i, α i * (r i + x i) - a) ≤
        ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by
      intro α hα
      obtain ⟨y, hy, h1, h2⟩ := eq_8_1_3_core F hσfinite r x a hx hA α hα
      refine le_trans ?_ (h1.trans h2)
      apply ENNReal.ofReal_le_ofReal
      have hyA : linearSupremum F (fun i => r i + y i) ≤ a := hy.2
      have hle : ∑ i, α i * (r i + y i) ≤ linearSupremum F (fun i => r i + y i) :=
        le_csSup (bddAbove_forms F hσfinite _) ⟨α, hα, rfl⟩
      have hdiff : ∑ i, α i * (r i + x i) - ∑ i, α i * (r i + y i) ≤
          ∑ i ∈ Finset.univ.filter (fun i => y i ≠ x i), |α i| := by
        rw [← Finset.sum_sub_distrib, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro i _
        by_cases h : y i ≠ x i
        · rw [if_pos h]
          have e : α i * (r i + x i) - α i * (r i + y i) = α i * (x i - y i) := by ring
          rw [e]
          calc α i * (x i - y i) ≤ |α i * (x i - y i)| := le_abs_self _
            _ = |α i| * |x i - y i| := abs_mul _ _
            _ ≤ |α i| * 1 := by
                gcongr
                rw [abs_le]
                constructor <;> linarith [(hx i).1, (hx i).2, (hy.1 i).1, (hy.1 i).2]
            _ = |α i| := mul_one _
        · rw [if_neg h]
          push_neg at h
          rw [h, sub_self]
      linarith
    rcases eq_or_ne (ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x) ⊤
      with htop | htop
    · rw [htop]; exact le_top
    · rw [← ENNReal.ofReal_toReal htop] at key ⊢
      apply ENNReal.ofReal_le_ofReal
      have hne : ((fun α : Fin N → ℝ => ∑ i, α i * (r i + x i)) '' F).Nonempty := hF.image _
      rw [sub_le_iff_le_add]
      apply csSup_le hne
      rintro _ ⟨α, hα, rfl⟩
      have := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 (key α hα)
      linarith
  · have hAe : linearSublevel F r a = ∅ := Set.not_nonempty_iff_eq_empty.1 hA
    rw [hAe, convexDistance_empty, ENNReal.mul_top]
    · exact le_top
    · rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hσ

end TalagrandConc.LinearSuprema

open TalagrandConc.LinearSuprema


theorem solution {N : ℕ} (F : Set (Fin N → ℝ))
    (hF : F.Nonempty) (hσfinite : BddAbove (coeffNorm '' F))
    (hσ : 0 < sigma F) (r x : Fin N → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ENNReal.ofReal (linearSupremum F (fun i => r i + x i) - a) ≤
      ENNReal.ofReal (sigma F) * convexDistance (linearSublevel F r a) x := by
  exact eq_8_1_2_core F hF hσfinite hσ r x a hx
