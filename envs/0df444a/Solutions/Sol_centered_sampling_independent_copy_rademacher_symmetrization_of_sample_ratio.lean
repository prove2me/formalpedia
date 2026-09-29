-- Prove2me | solution 1 for centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T03:47:06.128663+00:00
-- url     : https://prove2.me/submissions/fb7ae8ef-44ca-4cb4-b83d-33f50cf666a8

import Definitions.Def_matrix_completion_rademacher
import Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

namespace ProveSymBij

abbrev Pt (n1 n2 : ℕ) := Finset (Fin n1 × Fin n2)

/-- Pair-swap on `S = εᶜ`: `swapL (Ω,Ω') = (Ω\S)∪(Ω'∩S)`, `swapR = (Ω'\S)∪(Ω∩S)`. -/
def swapL {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.1 \ epsᶜ) ∪ (q.2 ∩ epsᶜ)
def swapR {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) : Pt n1 n2 :=
  (q.2 \ epsᶜ) ∪ (q.1 ∩ epsᶜ)

/-- The swap is involutive (on the pair). -/
theorem swap_invol {n1 n2 : ℕ} (eps : Pt n1 n2) (q : Pt n1 n2 × Pt n1 n2) :
    (swapL eps (swapL eps q, swapR eps q), swapR eps (swapL eps q, swapR eps q)) = q := by
  have hL : swapL eps (swapL eps q, swapR eps q) = q.1 := by
    ext a
    simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]
    by_cases he : a ∈ eps <;> simp [he]
  have hR : swapR eps (swapL eps q, swapR eps q) = q.2 := by
    ext a
    simp only [swapL, swapR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_compl]
    by_cases he : a ∈ eps <;> simp [he]
  rw [Prod.ext_iff]; exact ⟨hL, hR⟩

/-- Weight product preservation. -/
theorem wprod {n1 n2 : ℕ} (p : ℝ) (eps Ω Ω' : Pt n1 n2) :
    bernoulliObservationWeight p ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)) *
        bernoulliObservationWeight p ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ))
      = bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' := by
  have d1 : Disjoint (Ω \ epsᶜ) (Ω' ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have d2 : Disjoint (Ω' \ epsᶜ) (Ω ∩ epsᶜ) := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [Finset.mem_sdiff, Finset.mem_inter] at ha hb; exact ha.2 hb.2
  have e1 : (Ω \ epsᶜ).card + (Ω ∩ epsᶜ).card = Ω.card :=
    Finset.card_sdiff_add_card_inter Ω epsᶜ
  have e2 : (Ω' \ epsᶜ).card + (Ω' ∩ epsᶜ).card = Ω'.card :=
    Finset.card_sdiff_add_card_inter Ω' epsᶜ
  have hcard : ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card + ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card
      = Ω.card + Ω'.card := by
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2]; omega
  unfold bernoulliObservationWeight
  set N := Fintype.card (Fin n1 × Fin n2) with hN
  set a := ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)).card with ha
  set b := ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)).card with hb
  have hcΩ : Ω.card ≤ N := Finset.card_le_univ _
  have hcΩ' : Ω'.card ≤ N := Finset.card_le_univ _
  have hca : a ≤ N := ha ▸ Finset.card_le_univ _
  have hcb : b ≤ N := hb ▸ Finset.card_le_univ _
  rw [show p ^ a * (1-p) ^ (N - a) * (p ^ b * (1-p) ^ (N - b))
        = p ^ (a + b) * (1-p) ^ ((N - a) + (N - b)) from by rw [pow_add, pow_add]; ring,
    show p ^ Ω.card * (1-p) ^ (N - Ω.card) * (p ^ Ω'.card * (1-p) ^ (N - Ω'.card))
        = p ^ (Ω.card + Ω'.card) * (1-p) ^ ((N - Ω.card) + (N - Ω'.card)) from by
          rw [pow_add, pow_add]; ring]
  rw [hcard]; congr 2; omega

/-- The `univ`-sign difference at `(Ω,Ω')` equals the `eps`-sign difference at the
swapped pair: `radDiff(Ω,Ω',univ) = radDiff(swapL, swapR, eps)`. -/
theorem swap_mat {n1 n2 : ℕ} (p : ℝ) (X : RealMatrix n1 n2) (eps Ω Ω' : Pt n1 n2) :
    rademacherSampledMatrix Ω Finset.univ p X - rademacherSampledMatrix Ω' Finset.univ p X
      = rademacherSampledMatrix ((Ω \ epsᶜ) ∪ (Ω' ∩ epsᶜ)) eps p X
        - rademacherSampledMatrix ((Ω' \ epsᶜ) ∪ (Ω ∩ epsᶜ)) eps p X := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold rademacherSampledMatrix rademacherSign
  simp only [Finset.mem_univ, if_true, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  by_cases he : (i,j) ∈ eps <;> by_cases h : (i,j) ∈ Ω <;> by_cases h' : (i,j) ∈ Ω' <;>
    simp [he, h, h']

theorem spectralNorm_nonneg {n1 n2 : ℕ} (A : RealMatrix n1 n2) : 0 ≤ spectralNorm A :=
  norm_nonneg _

theorem weights_sum_one {n1 n2 : ℕ} (p : ℝ) (w0 : Fin n1 × Fin n2) :
    ∑ Omega : Finset (Fin n1 × Fin n2), bernoulliObservationWeight p Omega = 1 := by
  have h := bernoulli_powerset_expectation_single_coordinate (n₁ := n1) (n₂ := n2) p
    w0 (fun _ => (1:ℝ))
  simpa [bernoulliExpectation] using h

theorem weight_nonneg {n1 n2 : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n1 × Fin n2)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have h1 : (0:ℝ) ≤ 1 - p := by linarith
  positivity

theorem radWeight_nonneg {n1 n2 : ℕ} (eps : Finset (Fin n1 × Fin n2)) :
    0 ≤ rademacherObservationWeight eps := by
  unfold rademacherObservationWeight; positivity

theorem rad_weights_sum_one {n1 n2 : ℕ} :
    ∑ eps : Finset (Fin n1 × Fin n2), rademacherObservationWeight eps = 1 := by
  unfold rademacherObservationWeight
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, ← mul_pow]
  norm_num

/-- Per-`eps` invariance of the pair-expectation of the difference moment. -/
theorem pair_eps_invariant {n1 n2 : ℕ} (p : ℝ) (X : RealMatrix n1 n2) (q : ℕ)
    (eps : Pt n1 n2) :
    (∑ Ω : Pt n1 n2, ∑ Ω' : Pt n1 n2,
        bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
          spectralNorm (rademacherSampledMatrix Ω Finset.univ p X
              - rademacherSampledMatrix Ω' Finset.univ p X) ^ q)
      = ∑ Ω : Pt n1 n2, ∑ Ω' : Pt n1 n2,
        bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
          spectralNorm (rademacherSampledMatrix Ω eps p X
              - rademacherSampledMatrix Ω' eps p X) ^ q := by
  -- collapse to a single product sum, reindex by the involution, expand back
  rw [← Finset.sum_product', ← Finset.sum_product']
  apply Finset.sum_nbij' (fun z => (swapL eps z, swapR eps z)) (fun z => (swapL eps z, swapR eps z))
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact Finset.mem_univ _
  · intro z _; exact swap_invol eps z
  · intro z _; exact swap_invol eps z
  · intro z _
    -- f z = g (swap z):  univ-term at z = eps-term at (swapL z, swapR z)
    show bernoulliObservationWeight p z.1 * bernoulliObservationWeight p z.2 *
          spectralNorm (rademacherSampledMatrix z.1 Finset.univ p X -
            rademacherSampledMatrix z.2 Finset.univ p X) ^ q
        = bernoulliObservationWeight p (swapL eps z) * bernoulliObservationWeight p (swapR eps z) *
          spectralNorm (rademacherSampledMatrix (swapL eps z) eps p X -
            rademacherSampledMatrix (swapR eps z) eps p X) ^ q
    simp only [swapL, swapR]
    rw [wprod p eps z.1 z.2, swap_mat p X eps z.1 z.2]

end ProveSymBij

open ProveSymBij in
/-- `centered_sampling_independent_copy_rademacher_symmetrization_of_sample_ratio`.
Rademacher symmetrization (equality, hence `≤`): the Bernoulli-centered difference
equals the all-`+1` Rademacher difference (`ε = univ`), and a weight-preserving
pair-swap involution `(Ω,Ω') ↦ ((Ω\εᶜ)∪(Ω'∩εᶜ), (Ω'\εᶜ)∪(Ω∩εᶜ))` shows the
pair-expectation of the difference moment is the same for every sign pattern `ε`;
averaging over `ε` (sign weights sum to 1) and swapping `∑_ε ∑_pair` gives the result.
Source: Candès–Recht 2009/2012, §6.1 (symmetrization). -/
theorem solution :
    ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
      bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            spectralNorm
              (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                centeredSamplingFluctuation Omega'
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
        bernoulliPairExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega Omega' =>
            rademacherExpectation
              (fun eps =>
                spectralNorm
                  (rademacherSampledMatrix Omega eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X -
                    rademacherSampledMatrix Omega' eps
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q)) := by
  intro n₁ n₂ m q X hn₁ hn₂ hm hq
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set w0 : Fin n₁ × Fin n₂ := (⟨0, hn₁⟩, ⟨0, hn₂⟩) with hw0
  -- Step A: the Bernoulli-centered difference = the univ-sign Rademacher difference.
  have hA : ∀ Ω Ω' : Pt n₁ n₂,
      centeredSamplingFluctuation Ω p X - centeredSamplingFluctuation Ω' p X
        = rademacherSampledMatrix Ω Finset.univ p X - rademacherSampledMatrix Ω' Finset.univ p X := by
    intro Ω Ω'
    funext i j
    simp only [Matrix.sub_apply]
    unfold centeredSamplingFluctuation
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    unfold samplingProjection rademacherSampledMatrix rademacherSign
    simp only [Finset.mem_univ, if_true]
    by_cases h : (i,j) ∈ Ω <;> by_cases h' : (i,j) ∈ Ω' <;> simp [h, h'] <;> ring
  -- rewrite LHS via hA
  have hLHS : bernoulliPairExpectation p
      (fun Omega Omega' =>
        spectralNorm (centeredSamplingFluctuation Omega p X -
          centeredSamplingFluctuation Omega' p X) ^ q)
      = ∑ Ω : Pt n₁ n₂, ∑ Ω' : Pt n₁ n₂,
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            spectralNorm (rademacherSampledMatrix Ω Finset.univ p X
                - rademacherSampledMatrix Ω' Finset.univ p X) ^ q := by
    unfold bernoulliPairExpectation
    apply Finset.sum_congr rfl; intro Ω _
    apply Finset.sum_congr rfl; intro Ω' _
    simp only []
    rw [hA Ω Ω']
  rw [hLHS]
  -- RHS = ∑_eps w_eps · (pair-sum at eps);  by pair_eps_invariant each pair-sum = the univ one.
  -- RHS bernoulliPairExpectation of (rademacherExpectation ...) :
  --   ∑_Ω ∑_Ω' wΩ wΩ' · ∑_eps wε ‖radDiff(Ω,Ω',ε)‖^q
  -- swap sums to put eps outside, use invariance, then ∑_eps wε = 1.
  have hRHS : bernoulliPairExpectation p
      (fun Omega Omega' =>
        rademacherExpectation (fun eps =>
          spectralNorm (rademacherSampledMatrix Omega eps p X -
            rademacherSampledMatrix Omega' eps p X) ^ q))
      = ∑ Ω : Pt n₁ n₂, ∑ Ω' : Pt n₁ n₂,
          bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            spectralNorm (rademacherSampledMatrix Ω Finset.univ p X
                - rademacherSampledMatrix Ω' Finset.univ p X) ^ q := by
    unfold bernoulliPairExpectation rademacherExpectation
    -- pull wΩ wΩ' inside the eps sum, swap eps to outside
    have hstep : ∀ Ω Ω' : Pt n₁ n₂,
        bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            (∑ eps : Pt n₁ n₂, rademacherObservationWeight eps *
              spectralNorm (rademacherSampledMatrix Ω eps p X -
                rademacherSampledMatrix Ω' eps p X) ^ q)
          = ∑ eps : Pt n₁ n₂, rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
                spectralNorm (rademacherSampledMatrix Ω eps p X -
                  rademacherSampledMatrix Ω' eps p X) ^ q) := by
      intro Ω Ω'; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro eps _; ring
    simp only [hstep]
    -- reorder eps to outermost:  ∑Ω ∑Ω' ∑eps = ∑Ω ∑eps ∑Ω' = ∑eps ∑Ω ∑Ω'
    rw [Finset.sum_congr rfl (fun Ω _ => Finset.sum_comm (γ := Pt n₁ n₂)
        (f := fun Ω' eps => rademacherObservationWeight eps *
          (bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
            spectralNorm (rademacherSampledMatrix Ω eps p X -
              rademacherSampledMatrix Ω' eps p X) ^ q)))]
    rw [Finset.sum_comm (γ := Pt n₁ n₂)]
    -- factor wε out of each eps-slice and apply per-eps invariance
    have hslice : ∀ eps : Pt n₁ n₂,
        (∑ Ω : Pt n₁ n₂, ∑ Ω' : Pt n₁ n₂,
            rademacherObservationWeight eps *
              (bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
                spectralNorm (rademacherSampledMatrix Ω eps p X -
                  rademacherSampledMatrix Ω' eps p X) ^ q))
          = rademacherObservationWeight eps *
              (∑ Ω : Pt n₁ n₂, ∑ Ω' : Pt n₁ n₂,
                bernoulliObservationWeight p Ω * bernoulliObservationWeight p Ω' *
                  spectralNorm (rademacherSampledMatrix Ω Finset.univ p X -
                    rademacherSampledMatrix Ω' Finset.univ p X) ^ q) := by
      intro eps
      rw [pair_eps_invariant p X q eps, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro Ω _
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun eps _ => hslice eps)]
    -- ∑eps wε · C = (∑eps wε) · C = 1 · C = C
    rw [← Finset.sum_mul, rad_weights_sum_one, one_mul]
  rw [hRHS]
