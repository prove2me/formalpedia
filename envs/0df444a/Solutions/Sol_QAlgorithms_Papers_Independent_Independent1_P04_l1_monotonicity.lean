-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.l1_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:06:08.433584+00:00
-- url     : https://prove2.me/submissions/20872537-2ea8-4907-99a5-3b517670bfd5

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

noncomputable section
open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P04.A3L1

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma l1_eq {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Coherence.l1Coherence ρ = ∑ i, ∑ j, if i ≠ j then ‖ρ i j‖ else 0 := by
  unfold Coherence.l1Coherence
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]

lemma l1_nonneg {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ Coherence.l1Coherence ρ := by
  unfold Coherence.l1Coherence
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma l1_smul {d : ℕ} (c : ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Coherence.l1Coherence (c • ρ) = ‖c‖ * Coherence.l1Coherence ρ := by
  unfold Coherence.l1Coherence
  simp [norm_mul, Finset.mul_sum]

lemma l1_sum {d a : ℕ} (M : Fin a → Matrix (Fin d) (Fin d) ℂ) :
    Coherence.l1Coherence (∑ n, M n) ≤ ∑ n, Coherence.l1Coherence (M n) := by
  unfold Coherence.l1Coherence
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Matrix.sum_apply]
  exact norm_sum_le _ _

/-- column sparsity from preservation of diagonal states -/
lemma sparse {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (hK : PreservesDiagonalBranch K)
    (j : Fin d) (a b : Fin e) (hab : a ≠ b) : ‖K a j‖ * ‖K b j‖ = 0 := by
  have hX : (Matrix.diagonal (Pi.single j (1:ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hD : BasisDiagonal (Matrix.diagonal (Pi.single j (1:ℂ))) := by
    intro i k hik; simp [Matrix.diagonal_apply_ne _ hik]
  have := hK _ hX hD a b hab
  simp only [conjSuperop, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [Finset.sum_eq_single j] at this
  · simp at this
    rcases this with h | h <;> simp [h]
  · intro k _ hk; simp [Pi.single_apply, hk]
  · simp

def col {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (i : Fin d) : ℝ := ∑ a, ‖K a i‖

lemma col_sq {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (hK : PreservesDiagonalBranch K)
    (i : Fin d) : col K i ^ 2 = ∑ a, ‖K a i‖ ^ 2 := by
  unfold col
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · ring
  · intro b _ hb; exact sparse K hK i a b (Ne.symm hb)
  · simp

lemma entry_bound {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (hK : PreservesDiagonalBranch K)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (a b : Fin e) (hab : a ≠ b) :
    ‖(K * ρ * Kᴴ) a b‖ ≤
      ∑ i, ∑ j, if i ≠ j then ‖K a i‖ * ‖ρ i j‖ * ‖K b j‖ else 0 := by
  have hexp : (K * ρ * Kᴴ) a b = ∑ i, ∑ j, K a i * ρ i j * star (K b j) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hexp2 : (K * ρ * Kᴴ) a b = ∑ i, ∑ j, if i ≠ j then K a i * ρ i j * star (K b j) else 0 := by
    rw [hexp]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      have h0 := sparse K hK i a b hab
      have : K a i * star (K b i) = 0 := by
        rw [← norm_eq_zero, norm_mul, norm_star]; exact h0
      simp only [ne_eq, not_true_eq_false, if_false]
      calc K a i * ρ i i * star (K b i) = ρ i i * (K a i * star (K b i)) := by ring
        _ = 0 := by rw [this, mul_zero]
    · simp [hij]
  rw [hexp2]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  split_ifs <;> simp [norm_mul]

lemma swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, F a b i j) = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := by
  calc (∑ a, ∑ b, ∑ i, ∑ j, F a b i j) = ∑ a, ∑ i, ∑ b, ∑ j, F a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, F a b i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm

lemma core {d e : ℕ} (K : Matrix (Fin e) (Fin d) ℂ) (hK : PreservesDiagonalBranch K)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Coherence.l1Coherence (K * ρ * Kᴴ) ≤
      ∑ i, ∑ j, if i ≠ j then ‖ρ i j‖ * (col K i * col K j) else 0 := by
  rw [l1_eq]
  calc (∑ a, ∑ b, if a ≠ b then ‖(K * ρ * Kᴴ) a b‖ else 0)
      ≤ ∑ a, ∑ b, ∑ i, ∑ j, if i ≠ j then ‖K a i‖ * ‖ρ i j‖ * ‖K b j‖ else 0 := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs with hab
        · exact entry_bound K hK ρ a b hab
        · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
          split_ifs <;> positivity
    _ = ∑ i, ∑ j, ∑ a, ∑ b, if i ≠ j then ‖K a i‖ * ‖ρ i j‖ * ‖K b j‖ else 0 := by
        exact swap4 _
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · rw [col, col, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
        · simp

lemma family {d a : ℕ} (dims : Fin a → ℕ) (K : (n : Fin a) → Matrix (Fin (dims n)) (Fin d) ℂ)
    (hK : IncoherentInstrument dims K) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    ∑ n, Coherence.l1Coherence (K n * ρ * (K n)ᴴ) ≤ Coherence.l1Coherence ρ := by
  obtain ⟨hsum, hpres⟩ := hK
  have hcol : ∀ i, ∑ n, col (K n) i ^ 2 = 1 := by
    intro i
    have h1 := congrArg (fun M => M i i) hsum
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply_eq] at h1
    have h2 : ((∑ n, ∑ x, ‖K n x i‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h1]; push_cast
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ => ?_
      rw [RCLike.star_def, Complex.conj_mul']
    have h3 : (∑ n, ∑ x, ‖K n x i‖ ^ 2 : ℝ) = 1 := by exact_mod_cast h2
    rw [← h3]
    exact Finset.sum_congr rfl fun n _ => col_sq _ (hpres n) i
  have hpair : ∀ i j, ∑ n, col (K n) i * col (K n) j ≤ 1 := by
    intro i j
    have : ∑ n, col (K n) i * col (K n) j ≤ ∑ n, (col (K n) i ^ 2 + col (K n) j ^ 2) / 2 :=
      Finset.sum_le_sum fun n _ => by nlinarith [sq_nonneg (col (K n) i - col (K n) j)]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hcol, hcol] at this
    linarith
  calc ∑ n, Coherence.l1Coherence (K n * ρ * (K n)ᴴ)
      ≤ ∑ n, ∑ i, ∑ j, (if i ≠ j then ‖ρ i j‖ * (col (K n) i * col (K n) j) else 0) :=
        Finset.sum_le_sum fun n _ => core (K n) (hpres n) ρ
    _ = ∑ i, ∑ j, ∑ n, (if i ≠ j then ‖ρ i j‖ * (col (K n) i * col (K n) j) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ ∑ i, ∑ j, (if i ≠ j then ‖ρ i j‖ else 0) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        split_ifs
        · rw [← Finset.mul_sum]
          calc ‖ρ i j‖ * ∑ n, col (K n) i * col (K n) j ≤ ‖ρ i j‖ * 1 :=
                mul_le_mul_of_nonneg_left (hpair i j) (norm_nonneg _)
            _ = _ := mul_one _
        · simp
    _ = _ := (l1_eq ρ).symm

theorem main :
    CoherenceSelective (fun _ rho => Coherence.l1Coherence rho) ∧
    CoherenceMonotone (fun _ rho => Coherence.l1Coherence rho) := by
  constructor
  · intro d _ a dims _ K hK rho _
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) (family dims K hK rho)
    unfold selectiveContribution
    simp only
    split_ifs with hp
    · rw [l1_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, ← mul_assoc,
        mul_inv_cancel₀ hp.ne', one_mul]
      rfl
    · exact l1_nonneg _
  · intro d e _ _ a K hK rho _
    unfold krausApply
    exact (l1_sum _).trans (family (fun _ => e) K hK rho)

end QAlgorithms.Papers.Independent.Independent1.P04.A3L1

theorem solution :
    QAlgorithms.Papers.Independent.Independent1.P04.CoherenceSelective
      (fun _ rho => QAlgorithms.Coherence.l1Coherence rho) ∧
    QAlgorithms.Papers.Independent.Independent1.P04.CoherenceMonotone
      (fun _ rho => QAlgorithms.Coherence.l1Coherence rho) :=
  QAlgorithms.Papers.Independent.Independent1.P04.A3L1.main
