-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P27.decohered_and_random_fidelities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T00:55:36.724989+00:00
-- url     : https://prove2.me/submissions/911e4ea0-1fe7-4848-9961-3ac02bd6129a

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P27

-- part B

open scoped Matrix

namespace X7P27

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tr1 (P : Matrix (ι × ι) (ι × ι) ℂ) : Matrix ι ι ℂ := fun x y => ∑ m, P (m, x) (m, y)

def trR (M : Matrix (ι × ι) (ι × ι) ℂ) : Matrix ι ι ℂ := Matrix.of fun j k => ∑ h, M (j, h) (k, h)

lemma single_entry (P : Matrix (ι × ι) (ι × ι) ℂ) (a b k l : ι × ι) :
    (P * (Matrix.single a b (1:ℂ) : Matrix (ι × ι) (ι × ι) ℂ) * P) k l = P k a * P b l := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, Finset.mul_sum]
  simp [ite_and]

lemma front3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (g : α → β → γ → M) : ∑ a, ∑ b, ∑ c, g a b c = ∑ c, ∑ a, ∑ b, g a b c := by
  calc ∑ a, ∑ b, ∑ c, g a b c = ∑ a, ∑ c, ∑ b, g a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma gen (P : Matrix (ι × ι) (ι × ι) ℂ) (hP : P * P = P) :
    ∑ a, ∑ b, (P * Matrix.kronecker (trR (P * (Matrix.single a b (1:ℂ) : Matrix (ι × ι) (ι × ι) ℂ) * P)) (1 : Matrix ι ι ℂ) * P) a b =
      ∑ x, ∑ y, tr1 P x y * tr1 P y x := by
  have hPe : ∀ k l, ∑ a, P k a * P a l = P k l := fun k l => by
    rw [← Matrix.mul_apply, hP]
  have h1 : ∀ a b, (P * Matrix.kronecker (trR (P * (Matrix.single a b (1:ℂ) : Matrix (ι × ι) (ι × ι) ℂ) * P)) (1 : Matrix ι ι ℂ) * P) a b =
      ∑ m : ι × ι, ∑ n : ι × ι, ∑ h : ι, (P a m * P (m.1, h) a) * (P b (n.1, h) * P n b) *
        (if m.2 = n.2 then 1 else 0) := by
    intro a b
    have hk : ∀ m n : ι × ι, Matrix.kronecker (trR (P * (Matrix.single a b (1:ℂ) : Matrix (ι × ι) (ι × ι) ℂ) * P))
        (1 : Matrix ι ι ℂ) m n = (∑ h, P (m.1, h) a * P b (n.1, h)) * (if m.2 = n.2 then 1 else 0) := by
      rintro ⟨m1, m2⟩ ⟨n1, n2⟩
      simp only [trR, single_entry]
      show (∑ x, P (m1, x) a * P b (n1, x)) * (1 : Matrix ι ι ℂ) m2 n2 = _
      rw [Matrix.one_apply]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, hk, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun h _ => ?_
    ring
  simp only [h1]
  -- move a, b inside
  have h2 : ∑ a : ι × ι, ∑ b : ι × ι, ∑ m : ι × ι, ∑ n : ι × ι, ∑ h : ι,
      (P a m * P (m.1, h) a) * (P b (n.1, h) * P n b) * (if m.2 = n.2 then (1:ℂ) else 0) =
      ∑ m : ι × ι, ∑ n : ι × ι, ∑ h : ι,
        (∑ a, P (m.1, h) a * P a m) * (∑ b, P n b * P b (n.1, h)) * (if m.2 = n.2 then (1:ℂ) else 0) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [front3]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [front3]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [front3]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h2]
  simp only [hPe]
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, tr1,
    Finset.sum_mul, Finset.mul_sum]
  have e1 : ∀ m1 m2 n1 : ι, (∑ n2 : ι, ∑ h : ι, if m2 = n2 then P (m1, h) (m1, m2) * P (n1, n2) (n1, h) else 0) =
      ∑ h : ι, P (m1, h) (m1, m2) * P (n1, m2) (n1, h) := by
    intro m1 m2 n1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_ite_eq]; simp
  simp only [e1]
  calc _ = ∑ m1 : ι, ∑ h : ι, ∑ m2 : ι, ∑ n1 : ι, P (m1, h) (m1, m2) * P (n1, m2) (n1, h) :=
        Finset.sum_congr rfl fun m1 _ => front3 _
    _ = ∑ h : ι, ∑ m1 : ι, ∑ m2 : ι, ∑ n1 : ι, P (m1, h) (m1, m2) * P (n1, m2) (n1, h) := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [front3, front3]

end X7P27

-- part F

noncomputable section

open MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace X7P27

noncomputable instance cen {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) := SeminormedAddGroup.toContinuousENorm

abbrev G (d : ℕ) := Matrix.unitaryGroup (Fin d) ℂ

instance haar (d : ℕ) : (QAlgorithms.Schur.unitaryHaar d).IsHaarMeasure := by
  unfold QAlgorithms.Schur.unitaryHaar; infer_instance

instance prob (d : ℕ) : IsProbabilityMeasure (QAlgorithms.Schur.unitaryHaar d) :=
  ⟨Measure.haarMeasure_self⟩

lemma int_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (A B : Matrix m m ℂ) (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, A * f x * B ∂μ = A * (∫ x, f x ∂μ) * B := by
  let L0 : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => A * X * B
      map_add' := fun X Y => by simp [mul_add, add_mul]
      map_smul' := fun c X => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix m m ℂ →L[ℂ] Matrix m m ℂ := LinearMap.toContinuousLinearMap L0
  exact L.integral_comp_comm hf

lemma entry {X : Type*} [MeasurableSpace X] {μ : Measure X} {m n : Type*} [Fintype m] [Fintype n]
    (f : X → Matrix m n ℂ) (hf : Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  let L : Matrix m n ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => (n → ℂ)) i)
  have := L.integral_comp_comm hf
  exact this.symm

lemma int_trace {X : Type*} [MeasurableSpace X] {μ : Measure X} {m : Type*} [Fintype m]
    (f : X → Matrix m m ℂ) (hf : Integrable f μ) :
    ∫ x, (f x).trace ∂μ = (∫ x, f x ∂μ).trace := by
  let L : Matrix m m ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap m ℂ ℂ)
  exact L.integral_comp_comm hf

def M1 {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ∫ V : G d, V.val * X * V.valᴴ ∂(QAlgorithms.Schur.unitaryHaar d)

lemma M1_cont {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : Continuous fun V : G d => V.val * X * V.valᴴ := by
  have hU : Continuous (fun U : G d => (U : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  exact (hU.matrix_mul continuous_const).matrix_mul hU.matrix_conjTranspose

lemma M1_int {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) :
    Integrable (fun V : G d => V.val * X * V.valᴴ) (QAlgorithms.Schur.unitaryHaar d) :=
  (M1_cont X).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma unit_left {d : ℕ} (W : G d) : W.valᴴ * W.val = 1 := by
  have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this

lemma unit_right {d : ℕ} (W : G d) : W.val * W.valᴴ = 1 := by
  have := W.2; rw [Matrix.mem_unitaryGroup_iff] at this; exact this

lemma M1_inv {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (W : G d) : W.valᴴ * M1 X * W.val = M1 X := by
  unfold M1
  rw [← int_conj _ _ _ (M1_int X)]
  have h := integral_mul_left_eq_self (μ := QAlgorithms.Schur.unitaryHaar d)
    (fun V : G d => V.val * X * V.valᴴ) W⁻¹
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun V => ?_)
  simp only
  have : ((W⁻¹ * V : G d) : Matrix (Fin d) (Fin d) ℂ) = W.valᴴ * V.val := by
    rw [Submonoid.coe_mul, Matrix.UnitaryGroup.inv_val]; rfl
  rw [this, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

lemma M1_comm {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (W : G d) : M1 X * W.val = W.val * M1 X := by
  have h := M1_inv X W
  calc M1 X * W.val = W.val * (W.valᴴ * M1 X * W.val) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_right, Matrix.one_mul]
    _ = W.val * M1 X := by rw [h]

def Dg {d : ℕ} (i : Fin d) : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal fun k => if k = i then -1 else 1

lemma Dg_unit {d : ℕ} (i : Fin d) : Dg i ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold Dg
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1; funext k
  by_cases h : k = i <;> simp [h]

def Pm {d : ℕ} (σ : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) ℂ := fun a b => if a = σ b then 1 else 0

lemma Pm_unit {d : ℕ} (σ : Equiv.Perm (Fin d)) : Pm σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext a b
  simp only [Pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have : ∀ k : Fin d, ((if a = σ k then (1:ℂ) else 0) * star (if b = σ k then (1:ℂ) else 0)) =
      if k = σ.symm a then (if a = b then 1 else 0) else 0 := by
    intro k
    by_cases h1 : k = σ.symm a
    · subst h1; by_cases hab : a = b <;> simp [hab, Ne.symm]
    · have : a ≠ σ k := by intro h; apply h1; rw [h]; simp
      simp [this, h1]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma M1_offdiag {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) (hij : i ≠ j) : M1 X i j = 0 := by
  have h := congrFun (congrFun (M1_comm X ⟨Dg i, Dg_unit i⟩) i) j
  simp only [Dg, Matrix.mul_diagonal, Matrix.diagonal_mul, Ne.symm hij, if_false, if_true, mul_one] at h
  linear_combination h / 2

lemma M1_diag {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) : M1 X i i = M1 X j j := by
  have h := congrFun (congrFun (M1_comm X ⟨Pm (Equiv.swap i j), Pm_unit _⟩) i) j
  simp only [Matrix.mul_apply, Pm] at h
  simp [Equiv.swap_apply_def] at h
  rw [Finset.sum_eq_single j] at h
  · by_cases hij : i = j
    · subst hij; rfl
    · simpa [hij, Ne.symm hij] using h
  · intro k _ hk
    by_cases h1 : k = i
    · subst h1; simp; intro h'; exact absurd h' hk
    · by_cases h2 : k = j
      · exact absurd h2 hk
      · simp [h1, h2, Ne.symm h1]
  · simp

lemma M1_trace {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ) : (M1 X).trace = X.trace := by
  unfold M1
  rw [← int_trace _ (M1_int X)]
  have : ∀ V : G d, (V.val * X * V.valᴴ).trace = X.trace := fun V => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, unit_left, Matrix.one_mul]
  simp only [this, integral_const, probReal_univ, one_smul]

lemma M1_formula {d : ℕ} (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    M1 X i j = if i = j then X.trace / d else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ← M1_trace X, Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_congr rfl fun k _ => M1_diag X k i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  · rw [if_neg hij, M1_offdiag X i j hij]

lemma int_trsq {d : ℕ} (hd : 0 < d) :
    ∫ V : G d, V.val.trace * conj V.val.trace ∂(QAlgorithms.Schur.unitaryHaar d) = 1 := by
  have e : ∀ V : G d, V.val.trace * conj V.val.trace =
      ∑ i, ∑ k, (V.val * (Matrix.single i k (1:ℂ) : Matrix (Fin d) (Fin d) ℂ) * V.valᴴ) i k := by
    intro V
    have hs : ∀ (A B : Matrix (Fin d) (Fin d) ℂ) (a b k l : Fin d),
        (A * (Matrix.single a b (1:ℂ) : Matrix (Fin d) (Fin d) ℂ) * B) k l = A k a * B b l := by
      intro A B a b k l
      simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul]
      simp [ite_and]
    simp only [hs, Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, map_sum, Finset.sum_mul_sum]
    rfl
  simp only [e]
  have hint : ∀ i k : Fin d, Integrable (fun V : G d =>
      (V.val * (Matrix.single i k (1:ℂ) : Matrix (Fin d) (Fin d) ℂ) * V.valᴴ) i k)
      (QAlgorithms.Schur.unitaryHaar d) := fun i k =>
    ((M1_cont _).matrix_elem i k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
  simp only [fun i => integral_finsetSum _ fun k (_ : k ∈ Finset.univ) => hint i k]
  have : ∀ i k : Fin d, ∫ V : G d, (V.val * (Matrix.single i k (1:ℂ) : Matrix (Fin d) (Fin d) ℂ) * V.valᴴ) i k
      ∂(QAlgorithms.Schur.unitaryHaar d) = if i = k then (1:ℂ) / d else 0 := by
    intro i k
    rw [← entry _ (M1_int _), ← M1, M1_formula hd]
    by_cases h : i = k
    · subst h; simp [Matrix.trace, Matrix.single_apply]
    · simp [h]
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

end X7P27

-- part A

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

lemma X7P27_sectorDim_nonneg {d : ℕ} (hd : 2 ≤ d) (s : Bool) : 0 ≤ sectorDim d s := by
  have : (2:ℝ) ≤ d := by exact_mod_cast hd
  unfold sectorDim; cases s <;> simp
  · have : (0:ℝ) ≤ d - 1 := by linarith
    have : (0:ℝ) ≤ d * (d + -1) := by nlinarith
    linarith
  · positivity

lemma X7P27_part1 (d : ℕ) (hd : 2 ≤ d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    decoheredFamily d U = decoheredFormula d U := by
  funext ρ
  have key : ∀ i j : Bool,
      (fun a b => (onFirst (conjSuperop U.val) (dephaseMemory d (optimalPre d ρ))) (a,i) (b,j) :
        Matrix (Fin d) (Fin d) ℂ) =
      if i = j then U.val * traceRight (sectorProjector d i * ρ * sectorProjector d i) * U.valᴴ else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      ext a b
      simp [onFirst, conjSuperop, dephaseMemory, optimalPre]
    · simp only [hij, if_false]
      ext a b
      simp only [onFirst, conjSuperop, dephaseMemory, hij, if_false]
      rw [show (fun (_ _ : Fin d) => (0:ℂ)) = (0 : Matrix (Fin d) (Fin d) ℂ) from rfl]
      simp
  simp only [decoheredFamily, decoheredFormula, Function.comp, optimalPost]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [key i i, if_pos rfl, Real.sqrt_mul_self (X7P27_sectorDim_nonneg hd i)]
  · intro j _ hji
    rw [key i j, if_neg (Ne.symm hji)]
    simp
  · simp

end QAlgorithms.Papers.Independent.Claimed50.P27

-- part C

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

lemma X7P27_single_entry {m n p q : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]
    (A : Matrix m n ℂ) (B : Matrix p q ℂ) (a : n) (b : p) (k : m) (l : q) :
    (A * Matrix.single a b (1:ℂ) * B) k l = A k a * B b l := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul]
  simp [ite_and]

lemma X7P27_choi_trace {I : Type*} [Fintype I] [DecidableEq I] (Φ : Superop I I) (W : Matrix I I ℂ) :
    (channelChoi Φ * channelChoi (conjSuperop W)).trace =
      ∑ a, ∑ b, (Wᴴ * Φ (Matrix.single a b 1) * W) a b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp only [channelChoi, conjSuperop, X7P27_single_entry]
  simp only [Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.conjTranspose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun p _ => ?_
  ring

end QAlgorithms.Papers.Independent.Claimed50.P27

-- part D

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

lemma X7P27_swap_mul {d : ℕ} {n : Type*} (M : Matrix (Fin d × Fin d) n ℂ) (a : Fin d × Fin d) (b : n) :
    ((swapOp (ι := Fin d)) * M) a b = M (a.2, a.1) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (a.2, a.1)]
  · simp [swapOp]
  · intro c _ hc
    have : ¬ (a = (c.2, c.1)) := by
      intro h; apply hc; rw [h]
    simp [swapOp, this]
  · simp

lemma X7P27_mul_swap {d : ℕ} {n : Type*} [Fintype n] (M : Matrix n (Fin d × Fin d) ℂ) (a : n) (b : Fin d × Fin d) :
    (M * (swapOp (ι := Fin d))) a b = M a (b.2, b.1) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (b.2, b.1)]
  · simp [swapOp]
  · intro c _ hc
    have : ¬ (c = (b.2, b.1)) := hc
    simp [swapOp, this]
  · simp

lemma X7P27_swap_sq (d : ℕ) : (swapOp (ι := Fin d)) * swapOp = 1 := by
  ext a b
  rw [X7P27_swap_mul]
  simp only [swapOp, Matrix.of_apply, Matrix.one_apply]
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp [Prod.ext_iff, and_comm]

lemma X7P27_swap_kron {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ) :
    (swapOp (ι := Fin d)) * Matrix.kronecker V V = Matrix.kronecker V V * swapOp := by
  ext a b
  rw [X7P27_swap_mul, X7P27_mul_swap]
  simp [Matrix.kronecker, Matrix.kroneckerMap]
  ring

lemma X7P27_eps_sq (s : Bool) : (if s then (1:ℂ) else -1) * (if s then 1 else -1) = 1 := by
  cases s <;> simp

lemma X7P27_P_idem (d : ℕ) (s : Bool) : sectorProjector d s * sectorProjector d s = sectorProjector d s := by
  unfold sectorProjector
  set e : ℂ := if s then 1 else -1
  have he : e * e = 1 := X7P27_eps_sq s
  have hF := X7P27_swap_sq d
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    smul_mul_smul_comm, hF, smul_add, smul_smul, he]
  rw [show (1 / 2 : ℂ) * (1 / 2) = 1/4 by norm_num]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (1 / 4 : ℂ) * (1 : Matrix (PairReg d) (PairReg d) ℂ) a b * he

lemma X7P27_P_comm {d : ℕ} (s : Bool) (V : Matrix (Fin d) (Fin d) ℂ) :
    sectorProjector d s * Matrix.kronecker V V = Matrix.kronecker V V * sectorProjector d s := by
  unfold sectorProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    X7P27_swap_kron]

lemma X7P27_tr1 (d : ℕ) (s : Bool) (x y : Fin d) :
    X7P27.tr1 (sectorProjector d s) x y = (((d : ℂ) + if s then 1 else -1) / 2) * (if x = y then 1 else 0) := by
  unfold X7P27.tr1 sectorProjector
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, swapOp, Matrix.of_apply, smul_eq_mul,
    Prod.ext_iff, Matrix.smul_apply]
  by_cases h : x = y
  · subst h; simp
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have : ∀ m : Fin d, (m = x ∧ x = m) ↔ m = x := fun m => ⟨fun h => h.1, fun h => ⟨h, h.symm⟩⟩
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  · simp [h]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩; exact h (h2.trans h1)

end QAlgorithms.Papers.Independent.Claimed50.P27

-- part E

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27
open X7P27 (front3)

attribute [local instance] Classical.decEq Classical.propDecidable

lemma X7P27_conj (d : ℕ) (U : (Matrix.unitaryGroup (Fin d) ℂ)) (X : Matrix (PairReg d) (PairReg d) ℂ) :
    (Matrix.kronecker U.val U.val)ᴴ * decoheredFormula d U X * Matrix.kronecker U.val U.val =
      ∑ i : Bool, (((d : ℝ) / sectorDim d i : ℝ) : ℂ) •
        (sectorProjector d i * Matrix.kronecker (traceRight (sectorProjector d i * X * sectorProjector d i))
          (1 : Matrix (Fin d) (Fin d) ℂ) * sectorProjector d i) := by
  have hU : U.valᴴ * U.val = 1 := by
    have := U.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  unfold decoheredFormula
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [show (Matrix.kronecker U.val U.val)ᴴ = Matrix.kronecker U.valᴴ U.valᴴ from
    Matrix.conjTranspose_kronecker _ _]
  have hk : ∀ A B C D : Matrix (Fin d) (Fin d) ℂ,
      Matrix.kronecker A B * Matrix.kronecker C D = Matrix.kronecker (A * C) (B * D) :=
    fun A B C D => (Matrix.mul_kronecker_mul A C B D).symm
  set P := sectorProjector d i
  set A := traceRight (P * X * P)
  have h1 : Matrix.kronecker U.valᴴ U.valᴴ * P = P * Matrix.kronecker U.valᴴ U.valᴴ :=
    (X7P27_P_comm i _).symm
  have h2 : P * Matrix.kronecker U.val U.val = Matrix.kronecker U.val U.val * P := X7P27_P_comm i _
  calc Matrix.kronecker U.valᴴ U.valᴴ * (P * Matrix.kronecker (U.val * A * U.valᴴ) 1 * P) *
        Matrix.kronecker U.val U.val
      = P * (Matrix.kronecker U.valᴴ U.valᴴ * Matrix.kronecker (U.val * A * U.valᴴ) 1 *
          Matrix.kronecker U.val U.val) * P := by
        simp only [← Matrix.mul_assoc, h1]
        simp only [Matrix.mul_assoc, h2]
    _ = P * Matrix.kronecker A 1 * P := by
        rw [hk, hk]
        have e1 : U.valᴴ * (U.val * A * U.valᴴ) * U.val = A := by
          simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
          rw [Matrix.mul_assoc, hU, Matrix.mul_one]
        have e2 : U.valᴴ * (1 : Matrix (Fin d) (Fin d) ℂ) * U.val = 1 := by rw [Matrix.mul_one, hU]
        rw [e1, e2]

lemma X7P27_sum_tr1 (d : ℕ) (s : Bool) :
    ∑ x, ∑ y, X7P27.tr1 (sectorProjector d s) x y * X7P27.tr1 (sectorProjector d s) y x =
      (d : ℂ) * (((d : ℂ) + if s then 1 else -1) / 2) ^ 2 := by
  simp only [X7P27_tr1, mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  have : ∀ x y : Fin d, (if y = x then (if x = y then ((d:ℂ) + if s then 1 else -1) / 2 * (((d:ℂ) + if s then 1 else -1) / 2) else 0) else 0)
      = if x = y then (((d:ℂ) + if s then 1 else -1) / 2) ^ 2 else 0 := by
    intro x y
    by_cases h : x = y
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

lemma X7P27_dec_sum (d : ℕ) (hd : 2 ≤ d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    (channelChoi (decoheredFamily d U) * channelChoi (targetChannel U)).trace = (d : ℂ) ^ 2 := by
  unfold targetChannel
  rw [X7P27_choi_trace]
  simp only [X7P27_part1 d hd U, X7P27_conj, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm, front3]
  have hg : ∀ c : Bool, ∑ a : PairReg d, ∑ b : PairReg d, (sectorProjector d c *
      (traceRight (sectorProjector d c * (Matrix.single b a (1:ℂ) : Matrix (PairReg d) (PairReg d) ℂ) *
        sectorProjector d c)).kronecker (1 : Matrix (Fin d) (Fin d) ℂ) *
        sectorProjector d c) b a = (d : ℂ) * (((d : ℂ) + if c then 1 else -1) / 2) ^ 2 := by
    intro c
    rw [Finset.sum_comm, ← X7P27_sum_tr1]
    convert X7P27.gen (sectorProjector d c) (X7P27_P_idem d c) using 1
    rfl
  simp only [← Finset.mul_sum, hg, Fintype.sum_bool, if_true]
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have h0 : (d:ℂ) ≠ 0 := by
    have : (d:ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have h1 : (d:ℂ) + 1 ≠ 0 := by
    have : (d:ℝ) + 1 ≠ 0 := by linarith
    exact_mod_cast this
  have h2 : (d:ℂ) - 1 ≠ 0 := by
    have : (d:ℝ) - 1 ≠ 0 := by linarith
    exact_mod_cast this
  unfold sectorDim
  simp only [if_true, Bool.false_eq_true, if_false]
  push_cast
  field_simp
  ring

end QAlgorithms.Papers.Independent.Claimed50.P27

-- part G

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

lemma X7P27_kron_cont {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    Continuous fun V : X7P27.G d => Matrix.kronecker U V.val := by
  have hU : Continuous (fun V : X7P27.G d => (V : Matrix (Fin d) (Fin d) ℂ)) := continuous_subtype_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_const.mul (hU.matrix_elem i.2 j.2)

lemma X7P27_rand_sum (d : ℕ) (hd : 2 ≤ d) (U : (Matrix.unitaryGroup (Fin d) ℂ)) :
    (channelChoi (randomFamily d U) * channelChoi (targetChannel U)).trace = (d : ℂ) ^ 2 := by
  have hd0 : 0 < d := by omega
  unfold targetChannel
  rw [X7P27_choi_trace]
  set W := Matrix.kronecker U.val U.val
  have hc : ∀ ρ : Matrix (PairReg d) (PairReg d) ℂ, Continuous fun V : X7P27.G d =>
      Wᴴ * conjSuperop (Matrix.kronecker U.val V.val) ρ * W := by
    intro ρ
    unfold conjSuperop
    exact (continuous_const.matrix_mul (((X7P27_kron_cont U.val).matrix_mul continuous_const).matrix_mul
      (X7P27_kron_cont U.val).matrix_conjTranspose)).matrix_mul continuous_const
  have hi : ∀ ρ : Matrix (PairReg d) (PairReg d) ℂ, Integrable (fun V : X7P27.G d =>
      conjSuperop (Matrix.kronecker U.val V.val) ρ) (Schur.unitaryHaar d) := by
    intro ρ
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    unfold conjSuperop
    exact ((X7P27_kron_cont U.val).matrix_mul continuous_const).matrix_mul
      (X7P27_kron_cont U.val).matrix_conjTranspose
  have h1 : ∀ a b : PairReg d, (Wᴴ * randomFamily d U (Matrix.single a b 1) * W) a b =
      ∫ V : X7P27.G d, (Wᴴ * conjSuperop (Matrix.kronecker U.val V.val) (Matrix.single a b 1) * W) a b
        ∂(Schur.unitaryHaar d) := by
    intro a b
    unfold randomFamily
    rw [← X7P27.int_conj _ _ _ (hi _), X7P27.entry _ ((hc _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [h1]
  have hie : ∀ a b : PairReg d, Integrable (fun V : X7P27.G d =>
      (Wᴴ * conjSuperop (Matrix.kronecker U.val V.val) (Matrix.single a b 1) * W) a b) (Schur.unitaryHaar d) :=
    fun a b => (((hc _).matrix_elem a b)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [fun a => (integral_finsetSum _ fun b (_ : b ∈ Finset.univ) => hie a b).symm]
  rw [← integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hie a b]
  have hk : ∀ A B C D : Matrix (Fin d) (Fin d) ℂ,
      Matrix.kronecker A B * Matrix.kronecker C D = Matrix.kronecker (A * C) (B * D) :=
    fun A B C D => (Matrix.mul_kronecker_mul A C B D).symm
  have hpt : ∀ V : X7P27.G d, ∑ i, ∑ k, (Wᴴ * conjSuperop (Matrix.kronecker U.val V.val)
      (Matrix.single i k 1) * W) i k = (d : ℂ) ^ 2 *
        ((U⁻¹ * V : X7P27.G d).val.trace * conj (U⁻¹ * V : X7P27.G d).val.trace) := by
    intro V
    have hZ : ((U⁻¹ * V : X7P27.G d) : Matrix (Fin d) (Fin d) ℂ) = U.valᴴ * V.val := by
      rw [Submonoid.coe_mul, Matrix.UnitaryGroup.inv_val]; rfl
    rw [hZ]
    set Y := Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) (U.valᴴ * V.val)
    have hY : Wᴴ * Matrix.kronecker U.val V.val = Y := by
      simp only [W, Y]
      rw [show (Matrix.kronecker U.val U.val)ᴴ = Matrix.kronecker U.valᴴ U.valᴴ from
        Matrix.conjTranspose_kronecker _ _, hk, X7P27.unit_left]
    have he : ∀ i k, (Wᴴ * conjSuperop (Matrix.kronecker U.val V.val) (Matrix.single i k 1) * W) i k =
        Y i i * conj (Y k k) := by
      intro i k
      have : Wᴴ * conjSuperop (Matrix.kronecker U.val V.val) (Matrix.single i k 1) * W =
          Y * Matrix.single i k 1 * Yᴴ := by
        unfold conjSuperop
        rw [← hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        simp only [Matrix.mul_assoc]
      rw [this, X7P27_single_entry, Matrix.conjTranspose_apply]
      rfl
    simp only [he]
    rw [← Finset.sum_mul_sum]
    have htr : ∑ i, Y i i = (d : ℂ) * (U.valᴴ * V.val).trace := by
      have := Matrix.trace_kronecker (1 : Matrix (Fin d) (Fin d) ℂ) (U.valᴴ * V.val)
      simp only [Matrix.trace_one, Fintype.card_fin] at this
      exact this
    rw [← map_sum, htr]
    simp only [map_mul, map_natCast]
    ring
  simp only [hpt]
  rw [integral_const_mul]
  rw [integral_mul_left_eq_self (μ := Schur.unitaryHaar d)
    (fun V : X7P27.G d => V.val.trace * conj V.val.trace) U⁻¹]
  rw [X7P27.int_trsq hd0, mul_one]

end QAlgorithms.Papers.Independent.Claimed50.P27

-- part H

noncomputable section

open MeasureTheory QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Claimed50.P27

attribute [local instance] Classical.decEq Classical.propDecidable

lemma X7P27_score {d : ℕ} (hd : 2 ≤ d) (C : (Matrix.unitaryGroup (Fin d) ℂ) → Superop (PairReg d) (PairReg d))
    (hC : ∀ U, (channelChoi (C U) * channelChoi (targetChannel U)).trace = (d : ℂ) ^ 2) :
    familyScore C = 1 / (d : ℝ) ^ 2 := by
  unfold familyScore pointScore
  simp only [hC]
  have : ((d : ℂ) ^ 2).re = (d : ℝ) ^ 2 := by
    rw [show ((d : ℂ) ^ 2) = (((d : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  rw [this, integral_const, probReal_univ, one_smul]
  have hd' : (d : ℝ) ≠ 0 := by
    have : (2:ℝ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp

end QAlgorithms.Papers.Independent.Claimed50.P27

open QAlgorithms.Papers.Independent.Claimed50.P27 in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ U : (Matrix.unitaryGroup (Fin d) ℂ), decoheredFamily d U = decoheredFormula d U) ∧
    familyScore (decoheredFamily d) = 1 / (d : ℝ)^2 ∧
    familyScore (randomFamily d) = 1 / (d : ℝ)^2 :=
  ⟨X7P27_part1 d hd, X7P27_score hd _ (X7P27_dec_sum d hd), X7P27_score hd _ (X7P27_rand_sum d hd)⟩
