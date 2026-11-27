-- Prove2me | solution 1 for SkutellaCQP.MaxSNP.Supplement.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:36.086134+00:00
-- url     : https://prove2.me/submissions/4d702ca6-d2e9-45f5-8aa3-40aa0fe47b57

import Mathlib
import Definitions.Def_SkutellaCQP_MaxSNP_Supplement_SDP

open SkutellaCQP
open SkutellaCQP.MaxSNP
open SkutellaCQP.MaxSNP.Supplement

/-- Lemma 5.2, p. 26: both bounds, for arbitrary correlated assignment laws. -/
theorem solution {n : ℕ} (p : Two → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (v : Vectors n) (Z : ℝ) (hv : SDPFeasible p w v Z)
    (μ : (Fin n → Two) → ℝ) (hμ : IsAssignmentLaw μ)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 1 ≤ ρ₁) (hρ₂ : ρ₁ ≤ ρ₂)
    (hb : ProbabilityBounds v μ ρ₁ ρ₂) :
    expectedValue p w μ ≤ ρ₁ * (3 * linearValue p w v / 4) +
      ρ₂ * (Z - 3 * linearValue p w v / 4) ∧
    ρ₁ * (3 * linearValue p w v / 4) +
      ρ₂ * (Z - 3 * linearValue p w v / 4) ≤ ρ₂ * Z := by
        obtain ⟨hm1, hj1, hanti, hVV, hT, hZ⟩ := hv
        obtain ⟨hmarg, hjoint⟩ := hb
        set a := assignment v with ha_def
        have ha0 : ∀ i j, 0 ≤ a i j := by
          intro i j
          have h := abs_real_inner_le_norm (v.machine i) (v.job j)
          rw [hm1 i, hj1 j, one_mul] at h
          have := (abs_le.mp h).1
          simp only [ha_def, assignment]
          linarith
        have hL : linearValue p w v = ∑ j, ∑ i, w j * p i j * a i j := by
          unfold linearValue dotProduct
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          simp [SkutellaCQP.NoRel.cvec, SkutellaCQP.NoRel.vec, ha_def]
        have hL0 : 0 ≤ linearValue p w v := by
          rw [hL]
          exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
            mul_nonneg (mul_nonneg (hw j) (hp i j).le) (ha0 i j)
        refine ⟨?_, ?_⟩
        swap
        · nlinarith
        have hasym : ∀ i j k, SkutellaCQP.NoRel.prec p w i k j → ¬ SkutellaCQP.NoRel.prec p w i j k := by
          intro i j k h1 h2
          unfold SkutellaCQP.NoRel.prec at h1 h2
          rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
          · linarith
          · linarith
          · linarith
          · exact absurd (h1'.trans h2') (lt_irrefl _)
        have hirr : ∀ i j, ¬ SkutellaCQP.NoRel.prec p w i j j := by
          intro i j h
          exact hasym i j j h h
        -- the quadratic term
        set A : Two → Fin n → Fin n → ℝ := fun i j k =>
          if SkutellaCQP.NoRel.prec p w i k j then a i j * a i k * (w j * p i k) else 0 with hA
        have hDD : dotProduct (SkutellaCQP.NoRel.vec a) (Matrix.mulVec (SkutellaCQP.NoRel.Dmat p w) (SkutellaCQP.NoRel.vec a))
            = 2 * ∑ i, ∑ j, ∑ k, A i j k := by
          have hpt : ∀ i j h k, SkutellaCQP.NoRel.vec a (i, j) *
              (SkutellaCQP.NoRel.Dmat p w (i, j) (h, k) * SkutellaCQP.NoRel.vec a (h, k)) =
              if h = i then A i j k + A i k j else 0 := by
            intro i j h k
            simp only [SkutellaCQP.NoRel.vec, SkutellaCQP.NoRel.Dmat, hA]
            by_cases hh : h = i
            · subst hh
              by_cases hjk : j = k
              · subst hjk; simp [hirr]
              · by_cases h1 : SkutellaCQP.NoRel.prec p w h k j
                · have h2 := hasym h j k h1
                  simp [hjk, h1, h2]; ring
                · by_cases h2 : SkutellaCQP.NoRel.prec p w h j k
                  · simp [hjk, h1, h2]; ring
                  · simp [hjk, h1, h2]
            · simp [hh, Ne.symm hh]
          unfold dotProduct Matrix.mulVec dotProduct
          simp only [Fintype.sum_prod_type, Finset.mul_sum, hpt]
          have h1 : ∀ i j, (∑ h : Two, ∑ k : Fin n, if h = i then A i j k + A i k j else 0)
              = ∑ k, (A i j k + A i k j) := by
            intro i j
            rw [Finset.sum_comm]
            simp
          simp only [h1, two_mul, Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Finset.sum_comm
        have hZ' : SkutellaCQP.NoRel.ZCQP p w a = (1/2) * linearValue p w v +
            (1/2) * (2 * ∑ i, ∑ j, ∑ k, A i j k + ∑ j, ∑ i, w j * p i j * a i j ^ 2) := by
          unfold SkutellaCQP.NoRel.ZCQP
          rw [Matrix.add_mulVec, dotProduct_add, hDD]
          have hd : dotProduct (SkutellaCQP.NoRel.vec a)
              (Matrix.mulVec (Matrix.diagonal (SkutellaCQP.NoRel.cvec p w)) (SkutellaCQP.NoRel.vec a))
              = ∑ j, ∑ i, w j * p i j * a i j ^ 2 := by
            unfold dotProduct
            simp only [Matrix.mulVec_diagonal]
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            simp only [SkutellaCQP.NoRel.cvec, SkutellaCQP.NoRel.vec]
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
            ring
          rw [hd]
          rfl
        have hE : expectedValue p w μ = ∑ j, w j * ∑ i, (marginal μ i j * p i j +
            ∑ k, if SkutellaCQP.NoRel.prec p w i k j then joint μ i j k * p i k else 0) := by
          have hc : ∀ σ j, SkutellaCQP.NoRel.compl p w σ j = ∑ i, ((if σ j = i then p i j else 0) +
              ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
                (if σ j = i ∧ σ k = i then p i k else 0) else 0) := by
            intro σ j
            unfold SkutellaCQP.NoRel.compl
            rw [Finset.sum_eq_single (σ j)]
            · simp only [if_true, true_and, Finset.sum_filter]
              congr 1
              refine Finset.sum_congr rfl fun k _ => ?_
              by_cases h1 : SkutellaCQP.NoRel.prec p w (σ j) k j <;> by_cases h2 : σ k = σ j <;> simp [h1, h2]
            · intro i _ hi
              have : ¬ σ j = i := fun h => hi h.symm
              simp [this]
            · simp
          have hm : ∀ i j, marginal μ i j * p i j = ∑ σ, μ σ * (if σ j = i then p i j else 0) := by
            intro i j
            unfold marginal
            rw [Finset.sum_filter, Finset.sum_mul]
            refine Finset.sum_congr rfl fun σ _ => ?_
            split_ifs <;> simp
          have hjt : ∀ i j k, (if SkutellaCQP.NoRel.prec p w i k j then joint μ i j k * p i k else 0)
              = ∑ σ, μ σ * (if SkutellaCQP.NoRel.prec p w i k j then
                (if σ j = i ∧ σ k = i then p i k else 0) else 0) := by
            intro i j k
            unfold joint
            split_ifs with h
            · rw [Finset.sum_filter, Finset.sum_mul]
              refine Finset.sum_congr rfl fun σ _ => ?_
              split_ifs <;> simp
            · simp
          unfold expectedValue SkutellaCQP.NoRel.E SkutellaCQP.NoRel.val
          simp only [hc, hm, hjt]
          simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
          congr 1
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun σ _ => by ring
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun σ _ => by ring
        set T' : ℝ := ∑ j, w j * ∑ i, ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
          triple v i j k * p i k else 0 with hT'
        have hVV' : vectorValue p w v = linearValue p w v + T' := by
          rw [hL, hT']
          unfold vectorValue
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [mul_add, Finset.sum_filter, Finset.mul_sum]
          congr 1
          · simp only [ha_def]; ring
        set S2 : ℝ := ∑ j, ∑ i, w j * p i j * a i j ^ 2 with hS2
        have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (hw j) (hp i j).le) (sq_nonneg _)
        have hQ : ∑ i, ∑ j, ∑ k, A i j k = ∑ j, ∑ i, ∑ k, A i j k := Finset.sum_comm
        have hB : expectedValue p w μ ≤ ∑ j, w j * ∑ i, (ρ₁ / 2 * (a i j + (1 + a i j) * a i j / 2) * p i j +
            ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
              ρ₂ / 2 * (triple v i j k + a i j * a i k) * p i k else 0) := by
          rw [hE]
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hw j)
          apply Finset.sum_le_sum
          intro i _
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (hmarg i j) (hp i j).le
          · apply Finset.sum_le_sum
            intro k _
            split_ifs
            · exact mul_le_mul_of_nonneg_right (hjoint i j k) (hp i k).le
            · exact le_refl _
        have hsplit : (∑ j, w j * ∑ i, (ρ₁ / 2 * (a i j + (1 + a i j) * a i j / 2) * p i j +
            ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
              ρ₂ / 2 * (triple v i j k + a i j * a i k) * p i k else 0)) =
            ∑ j, ∑ i, (ρ₁ * (3 / 4 * (w j * p i j * a i j) + 1 / 4 * (w j * p i j * a i j ^ 2)) +
              ρ₂ / 2 * (w j * ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
                triple v i j k * p i k else 0) + ρ₂ / 2 * ∑ k, A i j k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h2 : w j * (∑ k, if SkutellaCQP.NoRel.prec p w i k j then
              ρ₂ / 2 * (triple v i j k + a i j * a i k) * p i k else 0) =
              ρ₂ / 2 * (w j * ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
                triple v i j k * p i k else 0) + ρ₂ / 2 * ∑ k, A i j k := by
            simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [hA]
            split_ifs <;> ring
          rw [mul_add, h2]
          ring
        have hfin : (∑ j, ∑ i, (ρ₁ * (3 / 4 * (w j * p i j * a i j) + 1 / 4 * (w j * p i j * a i j ^ 2)) +
              ρ₂ / 2 * (w j * ∑ k, if SkutellaCQP.NoRel.prec p w i k j then
                triple v i j k * p i k else 0) + ρ₂ / 2 * ∑ k, A i j k)) =
            ρ₁ * (3 / 4 * linearValue p w v + 1 / 4 * S2) + ρ₂ / 2 * T' +
              ρ₂ / 2 * ∑ j, ∑ i, ∑ k, A i j k := by
          rw [hL, hS2, hT']
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hZ', hQ] at hZ
        rw [hVV'] at hVV
        have hρ0 : 0 ≤ ρ₂ := by linarith
        have k1 := mul_nonneg hρ0 (sub_nonneg.mpr hVV)
        have k2 := mul_nonneg hρ0 (sub_nonneg.mpr hZ)
        have k3 := mul_nonneg (sub_nonneg.mpr hρ₂) hS20
        rw [hsplit, hfin] at hB
        nlinarith
