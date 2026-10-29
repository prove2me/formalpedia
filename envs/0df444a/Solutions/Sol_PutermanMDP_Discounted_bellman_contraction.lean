-- Prove2me | solution 1 for PutermanMDP.Discounted.bellman_contraction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:22:37.526736+00:00
-- url     : https://prove2.me/submissions/4dee521e-6b39-45e1-bdb3-8dd5e01f9636

import Mathlib
import Definitions.Def_PutermanMDP_Discounted_Operators

open Filter Topology
open PutermanMDP.Discounted

theorem aux_abs_tsum_le {S : Type} (p : S → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : HasSum p 1)
    (w : S → ℝ) (K : ℝ) (hK : ∀ j, |w j| ≤ K) : |∑' j, p j * w j| ≤ K := by
  have hg : HasSum (fun j => p j * K) K := by simpa using hp.mul_right K
  have := tsum_of_norm_bounded (f := fun j => p j * w j) hg (by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 j)]
    exact mul_le_mul_of_nonneg_left (hK j) (hp0 j))
  simpa [Real.norm_eq_abs] using this

theorem aux_summable {S : Type} (p : S → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : HasSum p 1)
    (w : S → ℝ) (K : ℝ) (hK : ∀ j, |w j| ≤ K) : Summable (fun j => p j * w j) := by
  refine Summable.of_norm_bounded (g := fun j => p j * K) (hp.summable.mul_right K) ?_
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 j)]
  exact mul_le_mul_of_nonneg_left (hK j) (hp0 j)

theorem solution {S : Type} [Countable S] [Nonempty S] {A : S → Type}
    [∀ s, MeasurableSpace (A s)] [∀ s, StandardBorelSpace (A s)]
    [∀ s, Nonempty (A s)] (M : Model S A) :
    (∀ v : S → ℝ, BoundedValue v → BoundedValue (bellman M v)) ∧
    (∀ u v : S → ℝ, BoundedValue u → BoundedValue v →
      supNorm (bellman M u - bellman M v) ≤ M.discount * supNorm (u - v)) := by
  have hl0 := M.discount_nonneg
  -- bound on each term
  have termBound : ∀ v : S → ℝ, ∀ C, (∀ s, |v s| ≤ C) → ∀ s (a : A s),
      |M.reward s a + M.discount * ∑' j : S, M.trans s a j * v j| ≤ M.bound + M.discount * C := by
    intro v C hC s a
    have h1 := M.reward_bounded s a
    have h2 := aux_abs_tsum_le _ (M.trans_nonneg s a) (M.trans_sum s a) v C hC
    calc _ ≤ |M.reward s a| + |M.discount * ∑' j : S, M.trans s a j * v j| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hl0]
        have := mul_le_mul_of_nonneg_left h2 hl0
        linarith
  have bddA : ∀ v : S → ℝ, ∀ C, (∀ s, |v s| ≤ C) → ∀ s,
      BddAbove (Set.range fun a : A s =>
        M.reward s a + M.discount * ∑' j : S, M.trans s a j * v j) := by
    intro v C hC s
    refine ⟨M.bound + M.discount * C, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact (abs_le.mp (termBound v C hC s a)).2
  refine ⟨?_, ?_⟩
  · rintro v ⟨C, hC⟩
    refine ⟨M.bound + M.discount * C, fun s => ?_⟩
    unfold bellman
    rw [abs_le]
    constructor
    · obtain ⟨a⟩ := (inferInstance : Nonempty (A s))
      exact le_trans (abs_le.mp (termBound v C hC s a)).1 (le_ciSup (bddA v C hC s) a)
    · exact ciSup_le fun a => (abs_le.mp (termBound v C hC s a)).2
  · rintro u v ⟨Cu, hCu⟩ ⟨Cv, hCv⟩
    have hdiff : ∀ s, |(u - v) s| ≤ Cu + Cv := by
      intro s
      rw [Pi.sub_apply]
      have := abs_sub (u s) (v s)
      linarith [hCu s, hCv s]
    have bddD : BddAbove (Set.range fun s => |(u - v) s|) :=
      ⟨Cu + Cv, by rintro _ ⟨s, rfl⟩; exact hdiff s⟩
    set D := supNorm (u - v) with hD
    have hDj : ∀ j, |u j - v j| ≤ D := by
      intro j
      have := le_ciSup bddD j
      rw [hD]; unfold supNorm; exact this
    -- one-sided comparison
    have oneSide : ∀ (u v : S → ℝ) Cu Cv, (∀ s, |u s| ≤ Cu) → (∀ s, |v s| ≤ Cv) →
        (∀ j, |u j - v j| ≤ D) → ∀ s, bellman M u s ≤ bellman M v s + M.discount * D := by
      intro u v Cu Cv hCu hCv hDj s
      unfold bellman
      apply ciSup_le
      intro a
      have hsu := aux_summable _ (M.trans_nonneg s a) (M.trans_sum s a) u Cu hCu
      have hsv := aux_summable _ (M.trans_nonneg s a) (M.trans_sum s a) v Cv hCv
      have hsub : ∑' j : S, M.trans s a j * u j - ∑' j : S, M.trans s a j * v j
          = ∑' j : S, M.trans s a j * (u j - v j) := by
        rw [← hsu.tsum_sub hsv]
        congr 1; ext j; ring
      have hb := aux_abs_tsum_le _ (M.trans_nonneg s a) (M.trans_sum s a)
        (fun j => u j - v j) D hDj
      rw [← hsub] at hb
      have h3 := (abs_le.mp hb).2
      have h4 := le_ciSup (bddA v Cv hCv s) a
      have h5 := mul_le_mul_of_nonneg_left h3 hl0
      nlinarith
    have hDj' : ∀ j, |v j - u j| ≤ D := fun j => by rw [abs_sub_comm]; exact hDj j
    apply ciSup_le
    intro s
    rw [Pi.sub_apply, abs_le]
    have e1 := oneSide u v Cu Cv hCu hCv hDj s
    have e2 := oneSide v u Cv Cu hCv hCu hDj' s
    constructor <;> linarith
