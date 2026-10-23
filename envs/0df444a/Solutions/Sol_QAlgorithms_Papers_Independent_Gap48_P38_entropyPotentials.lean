-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P38.entropyPotentials
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:01:27.975203+00:00
-- url     : https://prove2.me/submissions/25197a77-b88b-44b0-a6f1-3d07e765637d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix Polynomial

theorem x4_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x4_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x4_tr_aeval, x4_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x4_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x4_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x4_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x4_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x4_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x4_tr_pow_swap _ _ k hk]

namespace X4TR

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ} (I : Fin m → Type) [∀ i, Fintype (I i)]

def Mat (psi : EuclideanSpace ℂ (∀ i, I i)) (s : Finset (Fin m)) :
    Matrix (Restricted I s) (Restricted I (Finset.univ \ s)) ℂ :=
  fun x z => psi (subsystemIndex I s x z)

lemma red_eq (psi : EuclideanSpace ℂ (∀ i, I i)) (s : Finset (Fin m)) :
    subsystemReduction I (pureDensity psi) s = Mat I psi s * (Mat I psi s)ᴴ := by
  ext x y
  simp [subsystemReduction, traceRight, pureDensity, Matrix.mul_apply, Mat]

/-- complement of the complement -/
def ee (s : Finset (Fin m)) :
    Restricted I (Finset.univ \ (Finset.univ \ s)) ≃ Restricted I s where
  toFun w := fun i => w ⟨i.1, by simp [i.2]⟩
  invFun x := fun i => x ⟨i.1, by simpa using i.2⟩
  left_inv w := rfl
  right_inv x := rfl

lemma idx_eq (s : Finset (Fin m)) (u : Restricted I (Finset.univ \ s))
    (w : Restricted I (Finset.univ \ (Finset.univ \ s))) :
    subsystemIndex I (Finset.univ \ s) u w = subsystemIndex I s (ee I s w) u := by
  funext i
  by_cases hi : i ∈ s
  · simp [subsystemIndex, hi, ee]
  · simp [subsystemIndex, hi]

lemma red_compl (psi : EuclideanSpace ℂ (∀ i, I i)) (s : Finset (Fin m)) :
    subsystemReduction I (pureDensity psi) (Finset.univ \ s) =
      ((Mat I psi s)ᴴ * Mat I psi s)ᵀ := by
  ext u v
  simp only [subsystemReduction, traceRight, pureDensity, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Mat, idx_eq]
  refine Fintype.sum_equiv (ee I s) _ _ (fun w => ?_)
  simp [mul_comm]

lemma compl (psi : EuclideanSpace ℂ (∀ i, I i)) (s : Finset (Fin m)) :
    registerEntropy I (pureDensity psi) (Finset.univ \ s) = registerEntropy I (pureDensity psi) s := by
  unfold registerEntropy
  rw [red_compl, red_eq, x4_ent_swap]

end X4TR

namespace X4TR
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38
attribute [local instance] Classical.propDecidable Classical.decEq

lemma ceq (I : Fin 4 → Type) [∀ i, Fintype (I i)] (psi : EuclideanSpace ℂ (∀ i, I i))
    (s t : Finset (Fin 4)) (h : Finset.univ \ s = t) :
    registerEntropy I (pureDensity psi) s = registerEntropy I (pureDensity psi) t := by
  rw [← h, compl]

lemma cmi_sym (I : Fin 4 → Type) [∀ i, Fintype (I i)] (psi : EuclideanSpace ℂ (∀ i, I i)) :
    registerCMI I (pureDensity psi) {2} {3} {0} = registerCMI I (pureDensity psi) {2} {3} {1} := by
  unfold registerCMI
  rw [ceq I psi ({2} ∪ {0}) ({3} ∪ {1}) (by decide), ceq I psi ({3} ∪ {0}) ({2} ∪ {1}) (by decide),
    ceq I psi {0} ({2} ∪ {3} ∪ {1}) (by decide), ceq I psi ({2} ∪ {3} ∪ {0}) {1} (by decide)]
  ring

end X4TR

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P38

theorem solution
    (I : Fin 4 → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (psi : EuclideanSpace ℂ (∀ i, I i)) (hpsi : ‖psi‖ = 1) :
    let rho := pureDensity psi
    let Kinitial := registerMutualInfo I rho {0,2} {3} / 2
    let Kfinal := registerMutualInfo I rho {0} {3} / 2
    let Sinitial := registerMutualInfo I rho {0,2} {1} / 2
    let Sfinal := registerMutualInfo I rho {0} {1,2} / 2
    Kinitial - Kfinal = registerCMI I rho {2} {3} {0} / 2 ∧
    Kinitial - Kfinal = cornerQ I rho ∧ Sfinal - Sinitial = cornerE I rho := by
  intro rho Kinitial Kfinal Sinitial Sfinal
  have h1 : Kinitial - Kfinal = registerCMI I rho {2} {3} {0} / 2 := by
    simp only [Kinitial, Kfinal, registerMutualInfo, registerCMI]
    rw [show ({0, 2} : Finset (Fin 4)) = {2} ∪ {0} by decide,
      show ({2} ∪ {0} ∪ {3} : Finset (Fin 4)) = {2} ∪ {3} ∪ {0} by decide,
      show ({0} ∪ {3} : Finset (Fin 4)) = {3} ∪ {0} by decide]
    ring
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, cornerQ, X4TR.cmi_sym I psi]
  · simp only [Sinitial, Sfinal, cornerE, registerMutualInfo]
    rw [show ({0} ∪ {1, 2} : Finset (Fin 4)) = {0, 2} ∪ {1} by decide,
      show ({1, 2} : Finset (Fin 4)) = {1} ∪ {2} by decide,
      show ({0, 2} : Finset (Fin 4)) = {0} ∪ {2} by decide]
    ring
