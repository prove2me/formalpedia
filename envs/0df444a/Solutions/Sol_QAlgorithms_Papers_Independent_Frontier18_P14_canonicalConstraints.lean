-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.canonicalConstraints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:25:22.867654+00:00
-- url     : https://prove2.me/submissions/4ca23ca6-a7be-4579-954c-e05d873f61f4

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

lemma x8_ann_single {n : ℕ} (j : Fin n) (m : Fin n → ℕ) (r : ℂ) :
    annihilate n j (Finsupp.single m r) =
      if m j = 0 then 0 else
        Finsupp.single (Function.update m j (m j - 1)) (r * (Real.sqrt (m j : ℝ) : ℂ)) := by
  unfold annihilate
  rw [Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
  split_ifs with h
  · simp
  · simp [coreKet, Finsupp.smul_single, mul_comm]

lemma x8_cre_single {n : ℕ} (j : Fin n) (m : Fin n → ℕ) (r : ℂ) :
    create n j (Finsupp.single m r) =
      Finsupp.single (Function.update m j (m j + 1)) (r * (Real.sqrt ((m j : ℝ) + 1) : ℂ)) := by
  unfold create
  rw [Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]
  simp [coreKet, Finsupp.smul_single, mul_comm]


private lemma x8_sq (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = (x : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma x8_ccr_same {n : ℕ} (j : Fin n) :
    annihilate n j * create n j = create n j * annihilate n j + 1 := by
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply, x8_cre_single,
    x8_ann_single, Function.update_self, Function.update_idem, Nat.add_sub_cancel,
    Function.update_eq_self, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  by_cases h : m j = 0
  · simp [h]
  · rw [if_neg h, x8_cre_single, Function.update_self, Function.update_idem,
      Nat.sub_add_cancel (Nat.pos_of_ne_zero h), Function.update_eq_self,
      ← Finsupp.single_add]
    congr 1
    have e1 : ((m j + 1 : ℕ) : ℝ) = (m j : ℝ) + 1 := by push_cast; ring
    have e2 : (((m j - 1 : ℕ) : ℝ) + 1) = (m j : ℝ) := by
      rw [Nat.cast_sub (Nat.pos_of_ne_zero h)]; push_cast; ring
    rw [e1, e2, mul_assoc, x8_sq _ (by positivity), mul_assoc, x8_sq _ (by positivity)]
    push_cast; ring

lemma x8_ccr_ne {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    annihilate n j * create n k = create n k * annihilate n j := by
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, x8_cre_single, x8_ann_single,
    Function.update_of_ne hjk]
  by_cases h : m j = 0
  · simp [h]
  · rw [if_neg h, if_neg h, x8_cre_single, Function.update_of_ne (Ne.symm hjk),
      Function.update_comm hjk]
    congr 1; ring

lemma x8_aa {n : ℕ} (j k : Fin n) :
    annihilate n j * annihilate n k = annihilate n k * annihilate n j := by
  by_cases hjk : j = k
  · subst hjk; rfl
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, x8_ann_single]
  by_cases hk : m k = 0 <;> by_cases hj : m j = 0
  · simp [hk, hj]
  · simp only [hk, hj, if_true, if_false, map_zero, x8_ann_single,
      Function.update_of_ne (Ne.symm hjk)]
  · simp only [hk, hj, if_true, if_false, map_zero, x8_ann_single,
      Function.update_of_ne hjk]
  · simp only [hk, hj, if_false, x8_ann_single, Function.update_of_ne hjk,
      Function.update_of_ne (Ne.symm hjk)]
    rw [Function.update_comm hjk]
    congr 1; ring

lemma x8_cc {n : ℕ} (j k : Fin n) :
    create n j * create n k = create n k * create n j := by
  by_cases hjk : j = k
  · subst hjk; rfl
  apply Finsupp.lhom_ext
  intro m r
  simp only [Module.End.mul_apply, x8_cre_single, Function.update_of_ne hjk,
    Function.update_of_ne (Ne.symm hjk)]
  rw [Function.update_comm hjk]
  congr 1; ring

variable {n : ℕ}

lemma x8_ac (k l : Fin n) :
    annihilate n k * create n l = create n l * annihilate n k + if k = l then 1 else 0 := by
  split_ifs with h
  · subst h; exact x8_ccr_same k
  · rw [x8_ccr_ne k l h, add_zero]

lemma x8_ca (k l : Fin n) :
    create n k * annihilate n l = annihilate n l * create n k - if k = l then 1 else 0 := by
  rw [x8_ac l k]
  by_cases h : k = l
  · subst h; simp only [if_true]; abel
  · simp only [h, Ne.symm h, if_false]; abel

lemma x8_comm_pair1 (k l : Fin n) (x y u v : ℂ) :
    commutator (x • annihilate n k + y • create n k) (u • create n l + v • annihilate n l) =
      (if k = l then x * u - y * v else 0) • (1 : Module.End ℂ (Core n)) := by
  unfold commutator
  simp only [add_mul, mul_add, smul_mul_smul_comm]
  rw [x8_ac k l, x8_aa k l, x8_cc k l, x8_ca k l]
  split_ifs <;> module

lemma x8_comm_pair2 (k l : Fin n) (x y u v : ℂ) :
    commutator (x • annihilate n k + y • create n k) (u • annihilate n l + v • create n l) =
      (if k = l then x * v - y * u else 0) • (1 : Module.End ℂ (Core n)) := by
  unfold commutator
  simp only [add_mul, mul_add, smul_mul_smul_comm]
  rw [x8_ac k l, x8_aa k l, x8_cc k l, x8_ca k l]
  split_ifs <;> module

lemma x8_comm_sum (X Y : Fin n → Module.End ℂ (Core n)) :
    commutator (∑ k, X k) (∑ l, Y l) = ∑ k, ∑ l, commutator (X k) (Y l) := by
  unfold commutator
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x i => X i * Y x)]
  have h1 := Finset.sum_sub_distrib (s := Finset.univ) (fun k => ∑ l, X k * Y l)
    (fun k => ∑ l, Y l * X k)
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (Finset.sum_sub_distrib (s := Finset.univ) (fun l => X k * Y l) (fun l => Y l * X k)).symm

lemma x8_c1 (B C : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    commutator (outputAnnihilator B C i) (outputCreator B C j) =
      (∑ k, (B i k * star (B j k) - C i k * star (C j k))) • (1 : Module.End ℂ (Core n)) := by
  unfold outputAnnihilator outputCreator
  rw [x8_comm_sum]
  simp only [x8_comm_pair1, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.sum_smul]

lemma x8_c2 (B C : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    commutator (outputAnnihilator B C i) (outputAnnihilator B C j) =
      (∑ k, (B i k * C j k - C i k * B j k)) • (1 : Module.End ℂ (Core n)) := by
  unfold outputAnnihilator
  rw [x8_comm_sum]
  simp only [x8_comm_pair2, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    ← Finset.sum_smul]

lemma x8_smul_one_inj (c d : ℂ) (h : c • (1 : Module.End ℂ (Core n)) = d • 1) : c = d := by
  have hv : (coreKet (fun _ => 0) : Core n) ≠ 0 := by
    unfold coreKet; exact Finsupp.single_ne_zero.2 one_ne_zero
  have := congrArg (fun T => T (coreKet (fun _ => 0) : Core n)) h
  simp only [LinearMap.smul_apply, Module.End.one_apply] at this
  exact smul_left_injective ℂ hv this

lemma x8_M1 (B C : Matrix (Fin n) (Fin n) ℂ)
    (hcanon : ∀ i j,
      commutator (outputAnnihilator B C i) (outputCreator B C j) =
        if i = j then 1 else 0) :
    B * B.conjTranspose - C * C.conjTranspose = 1 := by
  ext i j
  have h := hcanon i j
  rw [x8_c1, show (if i = j then (1 : Module.End ℂ (Core n)) else 0) =
    (if i = j then (1 : ℂ) else 0) • 1 by split_ifs <;> simp] at h
  have h' := x8_smul_one_inj _ _ h
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  rw [← h', Finset.sum_sub_distrib]

lemma x8_M2 (B C : Matrix (Fin n) (Fin n) ℂ)
    (hcomm : ∀ i j,
      commutator (outputAnnihilator B C i) (outputAnnihilator B C j) = 0) :
    B * C.transpose - C * B.transpose = 0 := by
  ext i j
  have h := hcomm i j
  rw [x8_c2, show (0 : Module.End ℂ (Core n)) = (0 : ℂ) • 1 by simp] at h
  have h' := x8_smul_one_inj _ _ h
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
  rw [← h', Finset.sum_sub_distrib]

lemma x8_SGS (B C : Matrix (Fin n) (Fin n) ℂ)
    (h1 : B * B.conjTranspose - C * C.conjTranspose = 1)
    (h2 : B * C.transpose - C * B.transpose = 0) :
    doubled B C * modeMetric n * (doubled B C).conjTranspose = modeMetric n := by
  have h1e : ∀ i j, ∑ k, (B i k * star (B j k) - C i k * star (C j k)) =
      if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun h1 i) j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] at this
    rw [Finset.sum_sub_distrib, this]
  have h2e : ∀ i j, ∑ k, (B i k * C j k - C i k * B j k) = 0 := by
    intro i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.zero_apply] at this
    rw [Finset.sum_sub_distrib, this]
  ext (i | i) (j | j) <;>
    simp [doubled, modeMetric, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply,
      Matrix.one_apply]
  · rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]; exact h1e i j
  · rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]; exact h2e i j
  · have := congrArg (starRingEnd ℂ) (h2e j i)
    simp only [map_sum, map_sub, map_mul, map_zero] at this
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← this]
    exact Finset.sum_congr rfl fun k _ => by ring
  · have := congrArg (starRingEnd ℂ) (h1e i j)
    simp only [map_sum, map_sub, map_mul, Complex.star_def, Complex.conj_conj] at this
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← neg_eq_iff_eq_neg, ← Finset.sum_neg_distrib]
    rw [show (if i = j then (1 : ℂ) else 0) = (starRingEnd ℂ) (if i = j then 1 else 0) by
      split_ifs <;> simp, ← this]
    exact Finset.sum_congr rfl fun k _ => by ring

lemma x8_GG : modeMetric n * modeMetric n = 1 := by
  unfold modeMetric
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

lemma x8_number (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.conjTranspose * B = 1) :
    ∑ j, outputCreator B 0 j * outputAnnihilator B 0 j = ∑ j, create n j * annihilate n j := by
  unfold outputCreator outputAnnihilator
  simp only [Matrix.zero_apply, star_zero, zero_smul, add_zero]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  have hl : ∀ l, ∑ j, (star (B j l) * B j k) • (create n l * annihilate n k) =
      (if l = k then (1 : ℂ) else 0) • (create n l * annihilate n k) := by
    intro l
    rw [← Finset.sum_smul]
    have := congrFun (congrFun hB l) k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at this
    rw [this]
  rw [Finset.sum_congr rfl fun l _ => hl l]
  simp [ite_smul]

theorem x8_main
    (n : ℕ) (B C : Matrix (Fin n) (Fin n) ℂ)
    (hcanon : ∀ i j,
      commutator (outputAnnihilator B C i) (outputCreator B C j) =
        if i = j then 1 else 0)
    (hcomm : ∀ i j,
      commutator (outputAnnihilator B C i) (outputAnnihilator B C j) = 0) :
    doubled B C * modeMetric n * (doubled B C).conjTranspose = modeMetric n ∧
    (doubled B C)⁻¹ = modeMetric n * (doubled B C).conjTranspose * modeMetric n ∧
    Complex.normSq (Matrix.det (doubled B C)) = 1 ∧
    (C = 0 → ∑ j, outputCreator B C j * outputAnnihilator B C j =
      ∑ j, create n j * annihilate n j) := by
  have h1 := x8_M1 B C hcanon
  have h2 := x8_M2 B C hcomm
  have hS := x8_SGS B C h1 h2
  set S := doubled B C
  set G := modeMetric n
  have hGG : G * G = 1 := x8_GG
  refine ⟨hS, ?_, ?_, ?_⟩
  · apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hS, hGG]
  · have hd := congrArg Matrix.det hS
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hd
    have hG : G.det * G.det = 1 := by rw [← Matrix.det_mul, hGG, Matrix.det_one]
    have hG0 : G.det ≠ 0 := by
      intro h; rw [h, zero_mul] at hG; exact zero_ne_one hG
    have h3 : S.det * star S.det = 1 := by
      have : S.det * star S.det * G.det = 1 * G.det := by linear_combination hd
      exact mul_right_cancel₀ hG0 this
    rw [Complex.star_def, Complex.mul_conj] at h3
    exact_mod_cast h3
  · intro hC
    subst hC
    apply x8_number
    rw [mul_eq_one_comm]
    simpa using h1

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution
    (n : ℕ) (B C : Matrix (Fin n) (Fin n) ℂ)
    (hcanon : ∀ i j,
      commutator (outputAnnihilator B C i) (outputCreator B C j) =
        if i = j then 1 else 0)
    (hcomm : ∀ i j,
      commutator (outputAnnihilator B C i) (outputAnnihilator B C j) = 0) :
    doubled B C * modeMetric n * (doubled B C).conjTranspose = modeMetric n ∧
    (doubled B C)⁻¹ = modeMetric n * (doubled B C).conjTranspose * modeMetric n ∧
    Complex.normSq (Matrix.det (doubled B C)) = 1 ∧
    (C = 0 → ∑ j, outputCreator B C j * outputAnnihilator B C j =
      ∑ j, create n j * annihilate n j) :=
  x8_main n B C hcanon hcomm
