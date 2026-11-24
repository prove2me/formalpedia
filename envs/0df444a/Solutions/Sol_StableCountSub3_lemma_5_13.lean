-- Prove2me | solution 1 for StableCountSub3.lemma_5_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:16:48.369415+00:00
-- url     : https://prove2.me/submissions/9a091e4e-cc56-4393-bcc1-e5f14274e5be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StableCountSub3_Credits
import Theorems.Thm_StableCountSub3_theorem_2_10
import Theorems.Thm_StableCountSub3_lemma_5_5
import Theorems.Thm_StableCountSub3_lemma_5_11

open StableMatching

noncomputable section

namespace StableCountSub3.L513

open Classical

variable {n : ℕ}

theorem mem_stableSet (I : Instance n) (μ : Matching n) : μ ∈ stableSet I ↔ I.IsStable μ := by
  unfold stableSet; simp

theorem mem_downsets (I : Instance n) (D : Finset (Rot n)) : D ∈ downsets I ↔ IsDownset I D := by
  unfold downsets
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Transfer along the rotation representation `μ ↦ D(μ)` (Theorem 2.10). -/
theorem sum_stable_eq (I : Instance n) (f : Finset (Rot n) → Fin n → ℝ) :
    ∑ μ ∈ stableSet I, ∑ m, f (Dof I μ) m = ∑ D ∈ downsets I, ∑ m, f D m := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := theorem_2_10 I
  apply Finset.sum_nbij' (fun μ => Dof I μ) (fun D => muOf I D)
  · intro μ hμ
    simp only [mem_stableSet] at hμ
    simp only [mem_downsets]
    exact (h1 μ hμ).2.2
  · intro D hD
    simp only [mem_downsets] at hD
    simp only [mem_stableSet]
    exact (h4 D hD).1
  · intro μ hμ
    simp only [mem_stableSet] at hμ
    exact h3 μ hμ
  · intro D hD
    simp only [mem_downsets] at hD
    exact (h4 D hD).2
  · intro μ _
    rfl

theorem card_downsets (I : Instance n) :
    (downsets I).card = StableCount.numStable I := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := theorem_2_10 I
  have hS : StableCount.numStable I = (stableSet I).card := by
    unfold StableCount.numStable
    rw [Fintype.card_subtype]
    congr 1
  rw [hS]
  symm
  apply Finset.card_nbij' (fun μ => Dof I μ) (fun D => muOf I D)
  · intro μ hμ
    simp only [Finset.mem_coe, mem_stableSet] at hμ
    simp only [Finset.mem_coe, mem_downsets]
    exact (h1 μ hμ).2.2
  · intro D hD
    simp only [Finset.mem_coe, mem_downsets] at hD
    simp only [Finset.mem_coe, mem_stableSet]
    exact (h4 D hD).1
  · intro μ hμ
    simp only [Finset.mem_coe, mem_stableSet] at hμ
    exact h3 μ hμ
  · intro D hD
    simp only [Finset.mem_coe, mem_downsets] at hD
    exact (h4 D hD).2

/-- The number of pointed matchings `(D, m)` (with `D` a downset) satisfying `P`. -/
def A (I : Instance n) (P : Finset (Rot n) → Fin n → Prop) [∀ D m, Decidable (P D m)] : ℝ :=
  ∑ D ∈ downsets I, ∑ m, if P D m then (1 : ℝ) else 0

theorem A_eq_card (I : Instance n) (P : Finset (Rot n) → Fin n → Prop)
    [∀ D m, Decidable (P D m)] :
    A I P = (Nat.card {p : Finset (Rot n) × Fin n // IsDownset I p.1 ∧ P p.1 p.2} : ℝ) := by
  unfold A
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_product' (f := fun D m => if P D m then (1 : ℝ) else 0), Finset.sum_boole]
  congr 2
  ext p
  simp [mem_downsets]

theorem two_ne_three : (2 : ℕ∞) ≠ 3 := by
  intro h
  have : ((2 : ℕ) : ℕ∞) = ((3 : ℕ) : ℕ∞) := by exact_mod_cast h
  exact absurd (ENat.natCast_inj.mp this) (by decide)

theorem inI_not_simple (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir)
    (a : Fin n) (ha : InI I D a dir) : ¬ IsSimple I D a dir := by
  obtain ⟨m, hm, rfl⟩ := ha
  have h := ((lemma_5_5 I D hD dir).1 m hm).2.1
  intro hS
  unfold IsSimple at hS
  rw [hS] at h
  exact two_ne_three h

theorem card_I_eq_card_C (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir) :
    (Finset.univ.filter fun m => InI I D m dir).card =
      (Finset.univ.filter fun m => InC I D m dir).card := by
  have hset : (Finset.univ.filter fun m => InI I D m dir) =
      (Finset.univ.filter fun m => InC I D m dir).image fun m => image I D m dir := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rfl
  rw [hset]
  apply Finset.card_image_of_injOn
  intro m hm m' hm' h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hm hm'
  exact (lemma_5_5 I D hD dir).2 m m' hm hm' h

/-- For a fixed downset and direction, the simple men and the images are disjoint and there are as
many images as men of `C`. -/
theorem simple_add_C_le (I : Instance n) (D : Finset (Rot n)) (hD : IsDownset I D) (dir : Dir) :
    (∑ m, if IsSimple I D m dir then (1 : ℝ) else 0) + (∑ m, if InC I D m dir then (1 : ℝ) else 0)
      ≤ n := by
  have hCI : (∑ m, if InC I D m dir then (1 : ℝ) else 0) =
      ∑ m, if InI I D m dir then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole, Finset.sum_boole, card_I_eq_card_C I D hD dir]
  rw [hCI, ← Finset.sum_add_distrib]
  calc (∑ m : Fin n, ((if IsSimple I D m dir then (1 : ℝ) else 0) +
          if InI I D m dir then (1 : ℝ) else 0))
      ≤ ∑ _m : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m _
        by_cases hI : InI I D m dir
        · have := inI_not_simple I D hD dir m hI
          simp [this, hI]
        · by_cases hS : IsSimple I D m dir <;> simp [hS, hI]
    _ = n := by simp

theorem A_add_C_le (I : Instance n) (dir : Dir) :
    A I (fun D m => IsSimple I D m dir) + A I (fun D m => InC I D m dir) ≤
      (StableCount.numStable I : ℝ) * n := by
  unfold A
  rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ _D ∈ downsets I, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro D hD
        exact simple_add_C_le I D ((mem_downsets I D).mp hD) dir
    _ = _ := by rw [Finset.sum_const, card_downsets, nsmul_eq_mul]

theorem A_or_le (I : Instance n) :
    A I (fun D m => IsSimple I D m .bwd ∨ IsSimple I D m .fwd) ≤
      (StableCount.numStable I : ℝ) * n := by
  unfold A
  calc _ ≤ ∑ _D ∈ downsets I, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro D _
        calc (∑ m, if (IsSimple I D m .bwd ∨ IsSimple I D m .fwd) then (1 : ℝ) else 0)
            ≤ ∑ _m : Fin n, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro m _
              split_ifs <;> norm_num
          _ = n := by simp
    _ = _ := by rw [Finset.sum_const, card_downsets, nsmul_eq_mul]

theorem A_add_eq (I : Instance n) :
    A I (fun D m => IsSimple I D m .bwd) + A I (fun D m => IsSimple I D m .fwd) =
      A I (fun D m => IsSimple I D m .bwd ∨ IsSimple I D m .fwd) +
        A I (fun D m => IsSimple I D m .bwd ∧ IsSimple I D m .fwd) := by
  unfold A
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases h1 : IsSimple I D m .bwd <;> by_cases h2 : IsSimple I D m .fwd <;> simp [h1, h2]

theorem es_eq (I : Instance n) :
    es I = 1 / ((StableCount.numStable I : ℝ) * n) *
      (A I (fun D m => IsSimple I D m .bwd) + A I (fun D m => IsSimple I D m .fwd)) := by
  unfold es avgDm
  have h := sum_stable_eq I (fun D m =>
    (if IsSimple I D m .bwd then (1 : ℝ) else 0) + (if IsSimple I D m .fwd then 1 else 0))
  rw [h]
  unfold A
  rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro D _
  rw [Finset.sum_add_distrib]

theorem pc_eq (I : Instance n) :
    pc I = 1 / ((StableCount.numStable I : ℝ) * n) * A I (fun D m => InC I D m .bwd) := by
  unfold pc avgDm
  have h := sum_stable_eq I (fun D m => if InC I D m .bwd then (1 : ℝ) else 0)
  rw [h]
  rfl

end StableCountSub3.L513

end

open StableCountSub3 StableCountSub3.L513 in
open Classical in
theorem solution {n : ℕ} (I : Instance n) :
    es I ≤ 1 + pc I ∧ es I ≤ 2 * (1 - pc I) ∧ es I ≤ 4 / 3 := by
  set X : ℝ := (StableCount.numStable I : ℝ) * n with hX
  set a := A I (fun D m => IsSimple I D m .bwd)
  set b := A I (fun D m => IsSimple I D m .fwd)
  set c := A I (fun D m => InC I D m .bwd)
  set c' := A I (fun D m => InC I D m .fwd)
  set d := A I (fun D m => IsSimple I D m .bwd ∧ IsSimple I D m .fwd)
  set o := A I (fun D m => IsSimple I D m .bwd ∨ IsSimple I D m .fwd)
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := lemma_5_11 I
  have hdc : d = c := by
    simp only [d, c, A_eq_card]
    exact_mod_cast Nat.card_congr e1
  have hdc' : d = c' := by
    simp only [d, c', A_eq_card]
    exact_mod_cast Nat.card_congr e2
  have hsum : a + b = o + d := A_add_eq I
  have ho : o ≤ X := A_or_le I
  have hbwd : a + c ≤ X := A_add_C_le I .bwd
  have hfwd : b + c' ≤ X := A_add_C_le I .fwd
  have hes : es I = 1 / X * (a + b) := es_eq I
  have hpc : pc I = 1 / X * c := pc_eq I
  have hX0 : 0 ≤ X := by positivity
  have h1 : es I ≤ 1 + pc I ∧ es I ≤ 2 * (1 - pc I) := by
    rcases hX0.eq_or_lt with h0 | hpos
    · rw [hes, hpc, ← h0]; norm_num
    · have he : 0 < 1 / X := by positivity
      have heX : 1 / X * X = 1 := by field_simp
      rw [hes, hpc]
      constructor
      · have := mul_le_mul_of_nonneg_left (show a + b ≤ X + c by linarith) he.le
        nlinarith
      · have := mul_le_mul_of_nonneg_left (show a + b ≤ 2 * X - 2 * c by linarith) he.le
        nlinarith
  refine ⟨h1.1, h1.2, ?_⟩
  linarith [h1.1, h1.2]
