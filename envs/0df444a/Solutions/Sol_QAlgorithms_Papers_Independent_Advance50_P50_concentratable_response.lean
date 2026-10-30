-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P50.concentratable_response
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:06:47.82323+00:00
-- url     : https://prove2.me/submissions/e6e54dfb-0116-489d-a02e-cccf924028d9

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

theorem s110k_tp_mul {I : Type*} [Fintype I] (k : ℕ) (A B : Mat I) :
    tensorPower k (A * B) = tensorPower k A * tensorPower k B := by
  ext x y
  simp only [tensorPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

theorem s110k_response_eq {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) (rho : Mat I) :
    M.response rho = (tensorPower k rho * M.effective).trace.re := by
  unfold ExpectationModel.response ExpectationModel.effective
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem s110k_tp_trace {I : Type*} [Fintype I] (k : ℕ) (A : Mat I) :
    (tensorPower k A).trace = A.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, tensorPower]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem s110q_pure_trace {I : Type} [Fintype I] (rho : Matrix I I ℂ) (h : IsPure rho) :
    rho.trace = 1 := by
  obtain ⟨v, hv, rfl⟩ := h
  have h2 : ∑ i, ‖v i‖ ^ 2 = (1:ℝ) := by
    rw [← EuclideanSpace.norm_sq_eq, hv]; norm_num
  simp only [Matrix.trace, Matrix.diag, pureDensity, Matrix.of_apply]
  have : ∀ i, v i * conj (v i) = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro i; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [this]
  rw [← Complex.ofReal_sum, h2]; simp

def s110q_mix {n : ℕ} (Q : Finset (Fin n)) (u v : Qubits n) : Qubits n :=
  fun j => if j ∈ Q then u j else v j

def s110q_g {n : ℕ} (Q : Finset (Fin n)) (x : Copies (Qubits n) 2) : Copies (Qubits n) 2 :=
  ![s110q_mix Q (x 1) (x 0), s110q_mix Q (x 0) (x 1)]

theorem s110q_swap_apply {n : ℕ} (Q : Finset (Fin n)) (y x : Copies (Qubits n) 2) :
    subsystemSwap Q y x = if y = s110q_g Q x then 1 else 0 := by
  have hf : ∀ j : Fin n, (if j ∈ Q then copySwap Bool else (1 : Mat (Copies Bool 2)))
      (fun c => y c j) (fun c => x c j) =
      if (∀ c : Fin 2, y c j = s110q_g Q x c j) then 1 else 0 := by
    intro j
    by_cases hj : j ∈ Q
    · simp [hj, copySwap, s110q_g, s110q_mix, Fin.forall_fin_two]
    · simp [hj, Matrix.one_apply, s110q_g, s110q_mix, Fin.forall_fin_two, funext_iff]
  unfold subsystemSwap pairedSiteProduct
  simp only [hf]
  rw [Finset.prod_boole]
  congr 1
  simp only [Finset.mem_univ, true_implies, eq_iff_iff]
  constructor
  · intro h; funext c j; exact h j c
  · rintro rfl j c; rfl

theorem s110q_lhs {n : ℕ} (Q : Finset (Fin n)) (rho : Mat (Qubits n)) :
    (tensorPower 2 rho * subsystemSwap Q).trace =
      ∑ a : Qubits n, ∑ b : Qubits n, rho a (s110q_mix Q b a) * rho b (s110q_mix Q a b) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, s110q_swap_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← (finTwoArrowEquiv (Qubits n)).symm.sum_comp, Fintype.sum_prod_type]
  simp [Fin.prod_univ_two, finTwoArrowEquiv, tensorPower, s110q_g]


open QAlgorithms.Papers.Independent.Gap48.P38 in
def s110q_e {n : ℕ} (Q : Finset (Fin n)) :
    Restricted (fun _ : Fin n => Bool) Q × Restricted (fun _ : Fin n => Bool) (Finset.univ \ Q)
      ≃ Qubits n where
  toFun p := subsystemIndex (fun _ => Bool) Q p.1 p.2
  invFun x := (fun i => x i.1, fun i => x i.1)
  left_inv p := by
    obtain ⟨a, z⟩ := p
    ext i
    · simp [subsystemIndex, i.2]
    · have : i.1 ∉ Q := (Finset.mem_sdiff.mp i.2).2
      simp [subsystemIndex, this]
  right_inv x := by
    funext j
    by_cases h : j ∈ Q <;> simp [subsystemIndex, h]

open QAlgorithms.Papers.Independent.Gap48.P38 in
theorem s110q_mix_idx {n : ℕ} (Q : Finset (Fin n)) a b z w :
    s110q_mix Q (subsystemIndex (fun _ : Fin n => Bool) Q b w)
      (subsystemIndex (fun _ : Fin n => Bool) Q a z) =
      subsystemIndex (fun _ : Fin n => Bool) Q b z := by
  funext j
  by_cases h : j ∈ Q <;> simp [s110q_mix, subsystemIndex, h]

open QAlgorithms.Papers.Independent.Gap48.P38 in
theorem s110q_swap_trace {n : ℕ} (Q : Finset (Fin n)) (rho : Mat (Qubits n)) :
    (tensorPower 2 rho * subsystemSwap Q).trace =
      (subsystemReduction (fun _ => Bool) rho Q * subsystemReduction (fun _ => Bool) rho Q).trace := by
  rw [s110q_lhs]
  rw [← (s110q_e Q).sum_comp]
  simp_rw [← (s110q_e Q).sum_comp (fun b => rho _ (s110q_mix Q b _) * rho b _)]
  simp only [Fintype.sum_prod_type, s110q_e, Equiv.coe_fn_mk, s110q_mix_idx]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, subsystemReduction, traceRight,
    Matrix.of_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]


theorem s110r_prod_expand {n : ℕ} (Q : Finset (Fin n)) (s o : Fin n → ℂ) :
    ∏ j, (if j ∈ Q then o j + s j else o j) =
      ∑ t ∈ Q.powerset, ∏ j, (if j ∈ t then s j else o j) := by
  rw [← Finset.prod_mul_prod_compl Q]
  have h1 : ∏ j ∈ Q, (if j ∈ Q then o j + s j else o j) = ∏ j ∈ Q, (s j + o j) :=
    Finset.prod_congr rfl (fun j hj => by rw [if_pos hj, add_comm])
  have h2 : ∏ j ∈ Qᶜ, (if j ∈ Q then o j + s j else o j) = ∏ j ∈ Qᶜ, o j :=
    Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.mem_compl.mp hj)])
  rw [h1, h2, Finset.prod_add, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have htQ : t ⊆ Q := Finset.mem_powerset.mp ht
  rw [← Finset.prod_mul_prod_compl t]
  have h3 : ∏ j ∈ t, (if j ∈ t then s j else o j) = ∏ j ∈ t, s j :=
    Finset.prod_congr rfl (fun j hj => by rw [if_pos hj])
  have h4 : ∏ j ∈ tᶜ, (if j ∈ t then s j else o j) = ∏ j ∈ tᶜ, o j :=
    Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.mem_compl.mp hj)])
  have h5 : tᶜ = (Q \ t) ∪ Qᶜ := by
    ext j; simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro h; by_cases hq : j ∈ Q
      · exact Or.inl ⟨hq, h⟩
      · exact Or.inr hq
    · rintro (⟨_, h⟩ | h)
      · exact h
      · exact fun ht => h (htQ ht)
  have hd : Disjoint (Q \ t) Qᶜ := by
    rw [Finset.disjoint_left]; intro j hj; simp only [Finset.mem_sdiff] at hj
    simp [hj.1]
  rw [h3, h4, h5, Finset.prod_union hd, mul_assoc]

theorem s110r_paired_expand {n : ℕ} (Q : Finset (Fin n)) :
    pairedSiteProduct (fun j => if j ∈ Q then 1 + copySwap Bool else 1) =
      ∑ A ∈ Q.powerset, subsystemSwap A := by
  ext y x
  rw [Matrix.sum_apply]
  unfold subsystemSwap pairedSiteProduct
  have := s110r_prod_expand Q (fun j => copySwap Bool (fun c => y c j) (fun c => x c j))
    (fun j => (1 : Mat (Copies Bool 2)) (fun c => y c j) (fun c => x c j))
  convert this using 2 with j
  · show (if j ∈ Q then 1 + copySwap Bool else (1 : Mat (Copies Bool 2))) _ _ = _
    by_cases h : j ∈ Q
    · rw [if_pos h, Matrix.add_apply, if_pos h]
    · rw [if_neg h, if_neg h]
  · rename_i t _
    refine Finset.prod_congr rfl (fun j _ => ?_)
    show (if j ∈ t then copySwap Bool else (1 : Mat (Copies Bool 2))) _ _ = _
    by_cases h : j ∈ t
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]

end QAlgorithms.Papers.Independent.Advance50.P50

open QAlgorithms QAlgorithms.Papers.Independent.Advance50.P50
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)
open QAlgorithms.Papers.Independent.Information100.P32 (purity)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

theorem solution {n : ℕ} (Q : Finset (Fin n))
    (M : ExpectationModel (Qubits n) 2) (hobs : M.effective = concentratableObservable Q)
    (rho : Mat (Qubits n)) (hpure : IsPure rho) :
    M.response rho = 1 - ((2 : ℝ) ^ Q.card)⁻¹ *
      ∑ A ∈ Q.powerset, purity (subsystemReduction (fun _ => Bool) rho A) := by
  have hc : ((2 : ℂ) ^ Q.card)⁻¹ = (((2 : ℝ) ^ Q.card)⁻¹ : ℝ) := by push_cast; rfl
  rw [s110k_response_eq, hobs, concentratableObservable, s110r_paired_expand, Matrix.mul_sub,
    Matrix.mul_one, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.mul_sum,
    Matrix.trace_sum, s110k_tp_trace, s110q_pure_trace rho hpure, hc]
  simp only [s110q_swap_trace, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum]
  simp [purity]
