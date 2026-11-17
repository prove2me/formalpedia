-- Prove2me | solution 1 for QAOAE3Lin2.Typical.eq_55
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-16T13:02:32.2686+00:00
-- url     : https://prove2.me/submissions/ddf3816a-5bed-447a-a79b-813da6b9e9ce

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

open QAlgorithms QAOAE3Lin2.Typical

open scoped Matrix

/-- The exponential of a skew-Hermitian matrix is unitary. -/
theorem ct_exp_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : Aᴴ = -A) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h1 : star (NormedSpace.exp A) = NormedSpace.exp (-A) := by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hA]
  rw [h1, ← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

/-- `-(i t) H` is skew-Hermitian for Hermitian `H` and real `t`. -/
theorem ct_skew {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (t : ℝ) : (-(Complex.I * (t : ℂ)) • H)ᴴ = -(-(Complex.I * (t : ℂ)) • H) := by
  rw [Matrix.conjTranspose_smul, hH.eq]
  have hstar : star (-(Complex.I * (t : ℂ))) = Complex.I * (t : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hstar, neg_smul, neg_neg]

theorem ct_problem_herm {n : ℕ} (f : Qubits n → ℝ) : (problemHamiltonian f).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun y z => ?_)
  simp only [problemHamiltonian, Matrix.diagonal_apply]
  by_cases h : y = z
  · subst h; simp
  · have h' : ¬ z = y := fun hh => h hh.symm
    simp [h, h']

theorem ct_pauliX_herm : pauliX.IsHermitian := by
  refine Matrix.IsHermitian.ext (fun a b => ?_)
  simp only [pauliX, Matrix.of_apply]
  by_cases h : a = b
  · subst h; simp
  · have h' : ¬ b = a := fun hh => h hh.symm
    simp [h, h']

theorem ct_embed_herm {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (hM : M.IsHermitian)
    (w : Fin k ↪ Fin n) : (embedOp M w).IsHermitian := by
  refine Matrix.IsHermitian.ext (fun y z => ?_)
  simp only [embedOp, Matrix.of_apply]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · have h' : ∀ a : Fin n, a ∉ Set.range w → z a = y a := fun a ha => (h a ha).symm
    rw [if_pos h, if_pos h']
    exact hM.apply (y ∘ w) (z ∘ w)
  · have h' : ¬ ∀ a : Fin n, a ∉ Set.range w → z a = y a :=
      fun hh => h (fun a ha => (hh a ha).symm)
    rw [if_neg h, if_neg h', star_zero]

theorem ct_mixer_herm (n : ℕ) : (qaoaMixer n).IsHermitian := by
  unfold qaoaMixer Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact ct_embed_herm _ (ct_pauliX_herm.submatrix _) _

theorem ct_qaoa_unitary {n : ℕ} (f : Qubits n → ℝ) (β θ : Fin 1 → ℝ) :
    qaoaUnitary f 1 β θ ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  have h : qaoaUnitary f 1 β θ =
      NormedSpace.exp (-(Complex.I * (β 0 : ℂ)) • qaoaMixer n) *
        NormedSpace.exp (-(Complex.I * (θ 0 : ℂ)) • problemHamiltonian f) := by
    simp [qaoaUnitary, orderedProd, List.ofFn_succ]
  rw [h]
  exact mul_mem (ct_exp_unitary _ (ct_skew _ (ct_mixer_herm n) _))
    (ct_exp_unitary _ (ct_skew _ (ct_problem_herm f) _))

/-- The measurement probabilities of a vector sum to its squared norm. -/
theorem ct_prob_sum {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    ∑ x, prob ψ x = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  unfold prob ket
  rw [EuclideanSpace.inner_single_left]
  simp

theorem ct_uniform_norm (ι : Type) [Fintype ι] [Nonempty ι] : ‖uniformState ι‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ x : ι, ‖(uniformState ι) x‖ ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    intro x
    show ‖((Real.sqrt (Fintype.card ι))⁻¹ : ℂ)‖ ^ 2 = _
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt hc.le]
  have h : ‖uniformState ι‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']
  have hnn := norm_nonneg (uniformState ι)
  nlinarith

/-- The measurement probabilities of the level-one QAOA state sum to one. -/
theorem ct_state_prob_sum {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (γ β : ℝ) : ∑ x, prob (QAOAE3Lin2.General.qaoaState1 tri rhs γ β) x = 1 := by
  have hnorm : ‖QAOAE3Lin2.General.qaoaState1 tri rhs γ β‖ = 1 := by
    unfold QAOAE3Lin2.General.qaoaState1
    rw [act_norm_of_mem_unitaryGroup (ct_qaoa_unitary _ _ _), ct_uniform_norm]
  rw [ct_prob_sum, hnorm]; norm_num

/-- The number of satisfied equations as a sum of `½ (1 + d z_a z_b z_c)`. -/
theorem ct_satCount_eq {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool)
    (x : Qubits n) :
    QAOAE3Lin2.General.satCount tri rhs x =
      ∑ i : Fin m, ((1 : ℝ) / 2 + 1 / 2 * QAOAE3Lin2.General.sgn rhs i *
        (QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.1 *
          QAOAE3Lin2.General.spin x (tri i).2.2)) := by
  unfold QAOAE3Lin2.General.satCount
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold QAOAE3Lin2.General.sgn QAOAE3Lin2.General.spin
  generalize x (tri i).1 = a
  generalize x (tri i).2.1 = b
  generalize x (tri i).2.2 = c
  generalize rhs i = r
  cases a <;> cases b <;> cases c <;> cases r <;> norm_num

theorem solution {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (rhs : Fin m → Bool) (γ : ℝ) :
    QAOAE3Lin2.General.expSat tri rhs (-γ) (Real.pi / 4) = (m : ℝ) / 2 + ∑ i, clauseTerm tri rhs i γ := by
  let P : Qubits n → ℝ := fun x => prob (QAOAE3Lin2.General.qaoaState1 tri rhs (-γ) (Real.pi / 4)) x
  let S : Fin m → Qubits n → ℝ := fun i x =>
    QAOAE3Lin2.General.spin x (tri i).1 * QAOAE3Lin2.General.spin x (tri i).2.1 *
      QAOAE3Lin2.General.spin x (tri i).2.2
  have hsum : ∑ x, P x = 1 := ct_state_prob_sum tri rhs (-γ) (Real.pi / 4)
  show ∑ x, P x * QAOAE3Lin2.General.satCount tri rhs x =
    (m : ℝ) / 2 + ∑ i, 1 / 2 * QAOAE3Lin2.General.sgn rhs i * ∑ x, P x * S i x
  calc ∑ x, P x * QAOAE3Lin2.General.satCount tri rhs x
      = ∑ x, P x * ∑ i : Fin m, ((1 : ℝ) / 2 + 1 / 2 * QAOAE3Lin2.General.sgn rhs i * S i x) :=
        Finset.sum_congr rfl (fun x _ => by rw [ct_satCount_eq tri rhs x])
    _ = ∑ x, (P x * ((m : ℝ) / 2) +
          ∑ i : Fin m, 1 / 2 * QAOAE3Lin2.General.sgn rhs i * (P x * S i x)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_add, Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = (m : ℝ) / 2 * ∑ x, P x +
          ∑ i : Fin m, 1 / 2 * QAOAE3Lin2.General.sgn rhs i * ∑ x, P x * S i x := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun x _ => by ring)
        · exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
    _ = (m : ℝ) / 2 + ∑ i, 1 / 2 * QAOAE3Lin2.General.sgn rhs i * ∑ x, P x * S i x := by
        rw [hsum, mul_one]
