-- Prove2me | solution 1 for SkutellaCQP.NoRel.three_halves_rounding
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T23:26:06.378262+00:00
-- url     : https://prove2.me/submissions/fb17fb3a-80ef-4a8f-b918-d35f92b89092

-- Complete checked reconstruction of the native three-halves scheduling-rounding theorem.
-- Licensed under Apache 2.0.
import Definitions.Def_SkutellaCQP_NoRel_Setting


-- Begin ExpectationLinear

open Finset
namespace SkutellaCQP.NoRel.Proof

variable {m n : ℕ}

theorem expectation_sum {ι : Type*} (s : Finset ι) (μ : (Fin n → Fin m) → ℝ)
    (f : ι → (Fin n → Fin m) → ℝ) :
    E μ (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, E μ (f i) := by
  simp only [E, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_add (μ : (Fin n → Fin m) → ℝ)
    (f g : (Fin n → Fin m) → ℝ) : E μ (fun σ => f σ + g σ) = E μ f + E μ g := by
  simp [E, mul_add, Finset.sum_add_distrib]

theorem expectation_const_mul (μ : (Fin n → Fin m) → ℝ) (c : ℝ)
    (f : (Fin n → Fin m) → ℝ) : E μ (fun σ => c * f σ) = c * E μ f := by
  simp only [E, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end SkutellaCQP.NoRel.Proof
-- End ExpectationLinear

-- Begin MarginalMoments

open Finset
namespace SkutellaCQP.NoRel.Proof

variable {m n : ℕ}

theorem expectation_ind {a : Fin m → Fin n → ℝ} {μ : (Fin n → Fin m) → ℝ}
    (hμ : IsPairwiseRounding a μ) (i : Fin m) (j : Fin n) :
    E μ (fun σ => ind σ i j) = a i j := by
  classical
  simpa only [E, ind, Finset.sum_filter, mul_ite, mul_one, mul_zero] using hμ.2.2.1 j i

theorem expectation_ind_mul {a : Fin m → Fin n → ℝ} {μ : (Fin n → Fin m) → ℝ}
    (hμ : IsPairwiseRounding a μ) (i h : Fin m) (j k : Fin n) (hjk : j ≠ k) :
    E μ (fun σ => ind σ i j * ind σ h k) = a i j * a h k := by
  classical
  have he : (fun σ : Fin n → Fin m => ind σ i j * ind σ h k) =
      fun σ => if σ j = i ∧ σ k = h then (1:ℝ) else 0 := by
    funext σ
    simp only [ind]
    split_ifs <;> simp_all
  rw [he]
  simpa only [E, Finset.sum_filter, mul_ite, mul_one, mul_zero] using hμ.2.2.2 j k hjk i h

end SkutellaCQP.NoRel.Proof
-- End MarginalMoments

-- Begin SmithOrder

namespace SkutellaCQP.NoRel.Proof

lemma prec_irrefl {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ¬ prec p w i j j := by
  simp [prec]

lemma prec_asymm {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) (j k : Fin n) (h : prec p w i j k) : ¬ prec p w i k j := by
  unfold prec at *
  rcases h with h | ⟨h, hjk⟩
  · rintro (h' | ⟨h', _⟩) <;> linarith
  · rintro (h' | ⟨_, hkj⟩)
    · linarith
    · exact (not_lt_of_ge hjk.le) hkj

lemma prec_ne {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) {j k : Fin n} (h : prec p w i j k) : j ≠ k := by
  intro he
  subst k
  exact prec_irrefl p w i j h

lemma Dmat_split {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (x y : Fin m × Fin n) :
    Dmat p w x y =
      (if x.1 = y.1 ∧ prec p w x.1 y.2 x.2 then w x.2 * p x.1 y.2 else 0) +
      (if y.1 = x.1 ∧ prec p w y.1 x.2 y.2 then w y.2 * p y.1 x.2 else 0) := by
  classical
  rcases x with ⟨i,j⟩
  rcases y with ⟨h,k⟩
  by_cases hm : i = h
  · subst h
    by_cases hj : j = k
    · subst k
      simp [Dmat, prec_irrefl]
    · by_cases hk : prec p w i k j
      · simp [Dmat, hj, hk, prec_asymm p w i k j hk]
      · simp [Dmat, hj, hk]
  · simp [Dmat, hm, Ne.symm hm]

end SkutellaCQP.NoRel.Proof
-- End SmithOrder

-- Begin ExpectedTerms

open Finset
namespace SkutellaCQP.NoRel.Proof

variable {m n : ℕ}

theorem expectation_own_terms (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    {a : Fin m → Fin n → ℝ} {μ : (Fin n → Fin m) → ℝ}
    (hμ : IsPairwiseRounding a μ) :
    E μ (fun σ => ∑ i, ∑ j, w j*p i j*ind σ i j) =
      ∑ i, ∑ j, w j*p i j*a i j := by
  simp_rw [expectation_sum, expectation_const_mul, expectation_ind hμ]

theorem expectation_waiting_terms (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    {a : Fin m → Fin n → ℝ} {μ : (Fin n → Fin m) → ℝ}
    (hμ : IsPairwiseRounding a μ) :
    E μ (fun σ => ∑ i, ∑ j, ∑ k ∈ univ.filter (fun k => prec p w i k j),
      w j*p i k*ind σ i j*ind σ i k) =
      ∑ i, ∑ j, ∑ k ∈ univ.filter (fun k => prec p w i k j),
        w j*p i k*a i j*a i k := by
  simp_rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≠ j := prec_ne p w i (Finset.mem_filter.mp hk).2
  have he : (fun σ : Fin n → Fin m => w j*p i k*ind σ i j*ind σ i k) =
      fun σ => (w j*p i k)*(ind σ i j*ind σ i k) := by
    funext σ
    ring
  rw [he, expectation_const_mul, expectation_ind_mul hμ i i j k (Ne.symm hkj)]
  ring

end SkutellaCQP.NoRel.Proof
-- End ExpectedTerms

-- Begin QuadraticExpansion

open Finset Matrix
open scoped BigOperators
namespace SkutellaCQP.NoRel.Proof

noncomputable def orderedKernel {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  fun x y => if x.1 = y.1 ∧ prec p w x.1 y.2 x.2 then w x.2 * p x.1 y.2 else 0

lemma Dmat_eq_kernel_add_transpose {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) :
    Dmat p w = orderedKernel p w + (orderedKernel p w).transpose := by
  ext x y
  exact Dmat_split p w x y

lemma linear_expansion {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    cvec p w ⬝ᵥ vec a = ∑ i, ∑ j, w j * p i j * a i j := by
  simp only [dotProduct, cvec, vec, Fintype.sum_prod_type]

lemma orderedKernel_expansion {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    vec a ⬝ᵥ (orderedKernel p w *ᵥ vec a) =
      ∑ i, ∑ j, ∑ k ∈ univ.filter (fun k => prec p w i k j),
        w j * p i k * a i j * a i k := by
  classical
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, vec, orderedKernel]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [sum_eq_single i]
  · simp only [true_and, mul_sum, sum_filter]
    apply sum_congr rfl
    intro k _
    by_cases h : prec p w i k j
    · simp only [h, if_true]
      ring
    · simp [h]
  · intro h _ hne
    simp [Ne.symm hne]
  · simp

lemma quadratic_expansion {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    (1 / 2 : ℝ) * (vec a ⬝ᵥ (Dmat p w *ᵥ vec a)) =
      ∑ i, ∑ j, ∑ k ∈ univ.filter (fun k => prec p w i k j),
        w j * p i k * a i j * a i k := by
  rw [Dmat_eq_kernel_add_transpose, add_mulVec, dotProduct_add,
    dotProduct_transpose_mulVec, orderedKernel_expansion]
  ring

lemma ZQP_expansion {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    ZQP p w a = (∑ i, ∑ j, w j * p i j * a i j) +
      ∑ i, ∑ j, ∑ k ∈ univ.filter (fun k => prec p w i k j),
        w j * p i k * a i j * a i k := by
  rw [ZQP, linear_expansion, quadratic_expansion]

end SkutellaCQP.NoRel.Proof
-- End QuadraticExpansion

-- Begin AssignmentValue

open Finset Matrix
open scoped BigOperators
namespace SkutellaCQP.NoRel.Proof

lemma own_ind {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) :
    (∑ i, ∑ j, w j * p i j * ind σ i j) = ∑ j, w j * p (σ j) j := by
  classical
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp [ind, mul_ite]

lemma waiting_ind {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) :
    (∑ i, ∑ j, ∑ k ∈ univ.filter (fun k => prec p w i k j),
      w j * p i k * ind σ i j * ind σ i k) =
    ∑ j, ∑ k ∈ univ.filter (fun k => prec p w (σ j) k j ∧ σ k = σ j),
      w j * p (σ j) k := by
  classical
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_eq_single (σ j)]
  · simp [ind, sum_filter, mul_ite, ite_and]
  · intro i _ hne
    simp [ind, Ne.symm hne]
  · simp

lemma val_ind {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) : val p w σ = ZQP p w (ind σ) := by
  rw [ZQP_expansion, own_ind, waiting_ind]
  simp [val, compl, mul_add, mul_sum, sum_add_distrib]

lemma ind_feasible {m n : ℕ} (σ : Fin n → Fin m) : Feasible (ind σ) := by
  classical
  constructor
  · intro j
    simp [ind]
  · intro i j
    simp only [ind]
    split_ifs <;> norm_num

lemma linear_le_val {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (σ : Fin n → Fin m) :
    cvec p w ⬝ᵥ vec (ind σ) ≤ val p w σ := by
  rw [linear_expansion, own_ind]
  unfold val compl
  apply sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hw j)
  exact le_add_of_nonneg_right (sum_nonneg fun k _ => (hp (σ j) k).le)

end SkutellaCQP.NoRel.Proof
-- End AssignmentValue

-- Begin ExpectedValue

namespace SkutellaCQP.NoRel.Proof

variable {m n : ℕ}

theorem expected_value_eq_ZQP (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    {a : Fin m → Fin n → ℝ} {μ : (Fin n → Fin m) → ℝ}
    (hμ : IsPairwiseRounding a μ) : E μ (val p w) = ZQP p w a := by
  have he : val p w = fun σ => ZQP p w (ind σ) := funext (val_ind p w)
  rw [he]
  simp_rw [ZQP_expansion]
  rw [expectation_add, expectation_own_terms p w hμ, expectation_waiting_terms p w hμ]

end SkutellaCQP.NoRel.Proof
-- End ExpectedValue

-- Begin ObjectiveGap

open Finset Matrix
namespace SkutellaCQP.NoRel.Proof

variable {m n : ℕ}

theorem objective_gap (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ) :
    ZQP p w a = ZCQP p w a + (1/2)*
      (cvec p w ⬝ᵥ vec a - vec a ⬝ᵥ (Matrix.diagonal (cvec p w) *ᵥ vec a)) := by
  simp only [ZQP, ZCQP, Matrix.add_mulVec, dotProduct_add]
  ring

theorem diagonal_nonneg (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) :
    0 ≤ vec a ⬝ᵥ (Matrix.diagonal (cvec p w) *ᵥ vec a) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_nonneg
  intro x _
  change 0 ≤ a x.1 x.2 * (w x.2 * p x.1 x.2 * a x.1 x.2)
  nlinarith [mul_nonneg (mul_nonneg (hw x.2) (hp x.1 x.2).le) (sq_nonneg (a x.1 x.2))]

theorem objective_three_halves (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (Z : ℝ) (hZ : CQP'Feasible p w a Z) :
    ZQP p w a ≤ (3/2)*Z := by
  rw [objective_gap]
  have hdiag := diagonal_nonneg p w hp hw a
  rcases hZ with ⟨_, hq, hc⟩
  linarith

end SkutellaCQP.NoRel.Proof
-- End ObjectiveGap

-- Begin AssignmentFeasible

open Finset Matrix
namespace SkutellaCQP.NoRel.Proof

lemma diagonal_ind {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) :
    vec (ind σ) ⬝ᵥ (Matrix.diagonal (cvec p w) *ᵥ vec (ind σ)) =
      cvec p w ⬝ᵥ vec (ind σ) := by
  classical
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply sum_congr rfl
  intro x _
  rcases x with ⟨i,j⟩
  by_cases h : σ j = i <;> simp [vec, ind, h]

lemma ZCQP_ind_eq_val {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) : ZCQP p w (ind σ) = val p w σ := by
  have h := objective_gap p w (ind σ)
  rw [diagonal_ind, sub_self, mul_zero, add_zero] at h
  exact h.symm.trans (val_ind p w σ).symm

lemma assignment_feasible {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (σ : Fin n → Fin m) :
    CQP'Feasible p w (ind σ) (val p w σ) :=
  ⟨ind_feasible σ, (ZCQP_ind_eq_val p w σ).le, linear_le_val p w hp hw σ⟩

end SkutellaCQP.NoRel.Proof
-- End AssignmentFeasible

-- Begin RootAssembly

namespace SkutellaCQP.NoRel
open Proof

theorem three_halves_rounding {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    (∀ σ : Fin n → Fin m, CQP'Feasible p w (ind σ) (val p w σ)) ∧
    ∀ (a : Fin m → Fin n → ℝ) (Z : ℝ), CQP'Feasible p w a Z →
      ∀ μ : (Fin n → Fin m) → ℝ, IsPairwiseRounding a μ → E μ (val p w) ≤ (3 / 2) * Z := by
  refine ⟨assignment_feasible p w hp hw, ?_⟩
  intro a Z hZ μ hμ
  rw [expected_value_eq_ZQP p w hμ]
  exact objective_three_halves p w hp hw a Z hZ

end SkutellaCQP.NoRel
-- End RootAssembly

-- Begin Solution

open SkutellaCQP.NoRel

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) :
    (∀ σ : Fin n → Fin m, CQP'Feasible p w (ind σ) (val p w σ)) ∧
    ∀ (a : Fin m → Fin n → ℝ) (Z : ℝ), CQP'Feasible p w a Z →
      ∀ μ : (Fin n → Fin m) → ℝ, IsPairwiseRounding a μ → E μ (val p w) ≤ (3 / 2) * Z := SkutellaCQP.NoRel.three_halves_rounding p w hp hw
-- End Solution
