-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.invariant_nondegenerate_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:05:49.679918+00:00
-- url     : https://prove2.me/submissions/b4595269-183f-4830-96d2-d196e19e6841

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17
open QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_sign_sq {t : K} (h : IsSign t) : t * t = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem g74c_cva (rho : SpinRepresentation g S) (v : Fin d → K) :
    cliffordVectorAction rho v = rho.action (CliffordAlgebra.ι (cliffordQ g) v) := rfl

theorem g74c_even_comm (rho : SpinRepresentation g S) (A : Module.End K S) (τ : K)
    (hτ : IsSign τ) (hA : ∀ v, cliffordVectorAction rho v * A = τ • (A * cliffordVectorAction rho v))
    (a : CliffordAlgebra.even (cliffordQ g)) : rho.action a.val * A = A * rho.action a.val := by
  obtain ⟨x, hx⟩ := a
  change rho.action x * A = A * rho.action x
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r A
  | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, ← g74c_cva, ← g74c_cva]
    have h1 : cliffordVectorAction rho m₁ * (cliffordVectorAction rho m₂ * A) =
        A * (cliffordVectorAction rho m₁ * cliffordVectorAction rho m₂) := by
      rw [hA, mul_smul_comm, ← mul_assoc, hA, smul_mul_assoc, smul_smul, g74c_sign_sq hτ,
        one_smul, mul_assoc]
    rw [mul_assoc, mul_assoc, ih, ← mul_assoc (cliffordVectorAction rho m₂),
      ← mul_assoc (cliffordVectorAction rho m₁), h1]
    simp only [mul_assoc]

theorem g74c_form_gen (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) (u v : Fin d → K) (s t : S) :
    b (spinGenerator rho u v s) t = - b s (spinGenerator rho u v t) := by
  obtain ⟨hτ, -, hc, -⟩ := h
  have key : ∀ x y : Fin d → K, ∀ s t, b ((cliffordVectorAction rho x * cliffordVectorAction rho y) s) t
      = b s ((cliffordVectorAction rho y * cliffordVectorAction rho x) t) := by
    intro x y s t
    simp only [Module.End.mul_apply]
    rw [hc, hc, ← mul_assoc, g74c_sign_sq hτ, one_mul]
  simp only [spinGenerator, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub,
    LinearMap.smul_apply, LinearMap.sub_apply, key, smul_eq_mul]
  ring

theorem g74c_inv (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ σ : K)
    (h : FormSigns rho b τ σ) : b ∈ invariantForms rho := by
  intro u v s t
  rw [g74c_form_gen rho b τ σ h]; ring

theorem g74c_isSign_mul {a b : K} (ha : IsSign a) (hb : IsSign b) : IsSign (a * b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [IsSign]

end
section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_polar (x y : Fin d → K) :
    QuadraticMap.polar (cliffordQ g) x y = -(g.toBilin' x y + g.toBilin' y x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  simp [Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply', Matrix.neg_mulVec]
  ring

theorem g74c_rel (rho : SpinRepresentation g S) (x y : Fin d → K) :
    cliffordVectorAction rho x * cliffordVectorAction rho y =
      (QuadraticMap.polar (cliffordQ g) x y) • 1 - cliffordVectorAction rho y * cliffordVectorAction rho x := by
  have h := congrArg rho.action (CliffordAlgebra.ι_mul_ι_add_swap (Q := cliffordQ g) x y)
  rw [map_add, map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one] at h
  rw [← h, g74c_cva, g74c_cva]; abel

theorem g74c_comm_calc {A : Type*} [Ring A] [Algebra K A] (X Y Z : A) (a b c : K)
    (hXY : Y * X = a • 1 - X * Y) (hYZ : Y * Z = b • 1 - Z * Y) (hXZ : X * Z = c • 1 - Z * X) :
    ((1/4 : K) • (X * Y - Y * X)) * Z - Z * ((1/4 : K) • (X * Y - Y * X)) =
      (-(c/2)) • Y + (b/2) • X := by
  have h3 : X * Y * Z = b • X - c • Y + Z * X * Y := by
    rw [mul_assoc, hYZ, mul_sub, mul_smul_comm, mul_one, ← mul_assoc, hXZ, sub_mul,
      smul_mul_assoc, one_mul, mul_assoc]; abel
  rw [hXY]
  simp only [smul_sub, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h3,
    ← mul_assoc]
  module

end
theorem g74c_L1 {A : Type*} [Ring A] (x : A) (l : List A) (h : ∀ y ∈ l, x * y = -(y * x)) :
    x * l.prod = (-1 : A) ^ l.length * (l.prod * x) := by
  induction l with
  | nil => simp
  | cons y r ih =>
    simp only [List.prod_cons, List.length_cons]
    have hy := h y (by simp)
    have hr := ih (fun z hz => h z (by simp [hz]))
    rw [← mul_assoc, hy, neg_mul, mul_assoc, hr, pow_succ, ← mul_assoc y,
      ← ((Commute.neg_one_left y).pow_left r.length).eq]
    simp only [mul_assoc, neg_mul, mul_neg, mul_one, one_mul]

theorem g74c_L2 {A : Type*} [Ring A] : ∀ (n : ℕ) (f : Fin n → A),
    (∀ i j, i ≠ j → f i * f j = -(f j * f i)) →
    ∀ j, (List.ofFn f).prod * f j = (-1 : A) ^ (n - 1) * (f j * (List.ofFn f).prod)
  | 0, _, _, j => j.elim0
  | k + 1, f, hf, j => by
    rw [List.ofFn_succ, List.prod_cons]
    have h1 : f 0 * (List.ofFn fun i => f i.succ).prod =
        (-1 : A) ^ k * ((List.ofFn fun i => f i.succ).prod * f 0) := by
      have := g74c_L1 (f 0) (List.ofFn fun i => f i.succ) (by
        intro y hy
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hf _ _ (Fin.succ_ne_zero i).symm)
      simpa using this
    have hc : ∀ (m : ℕ) (z : A), (-1 : A) ^ m * z = z * (-1 : A) ^ m := fun m z =>
      ((Commute.neg_one_left z).pow_left m).eq
    refine Fin.cases ?_ (fun j' => ?_) j
    · have h2 : (List.ofFn fun i => f i.succ).prod * f 0 =
          (-1 : A) ^ k * (f 0 * (List.ofFn fun i => f i.succ).prod) := by
        rw [h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
      simp only [Nat.add_sub_cancel]
      rw [mul_assoc, h2, ← mul_assoc, ← hc, mul_assoc]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := j'.pos; omega⟩
      have ih := g74c_L2 (k' + 1) (fun i => f i.succ) (fun i j hij => hf _ _ (by simpa using hij)) j'
      simp only [Nat.add_sub_cancel] at ih ⊢
      rw [mul_assoc, ih, ← mul_assoc, ← hc, mul_assoc, ← mul_assoc (f 0), hf 0 j'.succ
        (Fin.succ_ne_zero j').symm, pow_succ]
      simp only [mul_assoc, neg_mul, mul_neg, mul_one, neg_inj, Fin.cases_succ]

def g74c_T : ℕ → ℕ
  | 0 => 0
  | n + 1 => g74c_T n + n

theorem g74c_L3 {A : Type*} [Ring A] [Algebra ℝ A] : ∀ (n : ℕ) (f : Fin n → A) (c : Fin n → ℝ),
    (∀ i j, i ≠ j → f i * f j = -(f j * f i)) → (∀ i, f i * f i = algebraMap ℝ A (c i)) →
    (List.ofFn f).prod * (List.ofFn f).prod = algebraMap ℝ A ((-1) ^ g74c_T n * ∏ i, c i)
  | 0, _, _, _, _ => by simp [g74c_T]
  | k + 1, f, c, hf, hc => by
    rw [List.ofFn_succ, List.prod_cons]
    have h1 : f 0 * (List.ofFn fun i => f i.succ).prod =
        (-1 : A) ^ k * ((List.ofFn fun i => f i.succ).prod * f 0) := by
      have := g74c_L1 (f 0) (List.ofFn fun i => f i.succ) (by
        intro y hy
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hf _ _ (Fin.succ_ne_zero i).symm)
      simpa using this
    have h2 : (List.ofFn fun i => f i.succ).prod * f 0 =
        (-1 : A) ^ k * (f 0 * (List.ofFn fun i => f i.succ).prod) := by
      rw [h1, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    have ih := g74c_L3 k (fun i => f i.succ) (fun i => c i.succ)
      (fun i j hij => hf _ _ (by simpa using hij)) (fun i => hc _)
    have hm : (-1 : A) ^ k = algebraMap ℝ A ((-1) ^ k) := by simp
    rw [mul_assoc, ← mul_assoc _ (f 0), h2, hm]
    simp only [mul_assoc]
    rw [← mul_assoc (f 0), ← Algebra.commutes]
    simp only [mul_assoc]
    rw [← mul_assoc (f 0) (f 0), hc, ih,
      ← map_mul, ← map_mul, Fin.prod_univ_succ, g74c_T, pow_add]
    congr 1; ring

theorem g74c_T4 (n : ℕ) : g74c_T (n + 4) = g74c_T n + (4 * n + 6) := by
  simp only [g74c_T]; ring

theorem g74c_Tpar : ∀ n : ℕ, (-1 : ℝ) ^ g74c_T n = if n % 4 = 0 ∨ n % 4 = 1 then 1 else -1
  | 0 => by simp [g74c_T]
  | 1 => by simp [g74c_T]
  | 2 => by norm_num [g74c_T]
  | 3 => by norm_num [g74c_T]
  | n + 4 => by
    rw [g74c_T4, pow_add, g74c_Tpar n, show 4 * n + 6 = 2 * (2 * n + 3) by ring, pow_mul]
    simp [Nat.add_mod_right]

theorem g74c_T2 : ∀ m : ℕ, Even (g74c_T (m + m) + m)
  | 0 => by simp [g74c_T]
  | m + 1 => by
    have := g74c_T2 m
    rw [show m + 1 + (m + 1) = (m + m) + 1 + 1 by ring]
    simp only [g74c_T]
    obtain ⟨r, hr⟩ := this
    exact ⟨r + 2 * m + 1, by omega⟩

theorem g74c_Q {d : ℕ} (g : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    cliffordQ g x = -(g.toBilin' x x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  simp [LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply']

theorem g74c_polarR {d : ℕ} (g : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    QuadraticMap.polar (cliffordQ g) x y = -(g.toBilin' x y + g.toBilin' y x) := by
  unfold cliffordQ Matrix.toQuadraticForm'
  rw [LinearMap.BilinMap.polar_toQuadraticMap]
  simp [Matrix.toBilin'_apply', Matrix.toLinearMap₂'_apply']
  ring

theorem g74c_anti (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ (Fin (p + q) → ℝ))
    (he : PseudoOrthonormal p q e) (i j : Fin (p + q)) (hij : i ≠ j) :
    CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e i) *
      CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e j) =
    -(CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e j) *
      CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) (e i)) := by
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := cliffordQ (signatureMatrix p q)) (e i) (e j)
  rw [g74c_polarR, he, he] at h
  simp only [signatureMatrix, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij.symm,
    add_zero, neg_zero, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem g74c_vol_comm (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ (Fin (p + q) → ℝ))
    (he : PseudoOrthonormal p q e) (x : Fin (p + q) → ℝ) :
    volumeElement p q e * CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) x =
      (-1 : RealCl p q) ^ (p + q - 1) *
        (CliffordAlgebra.ι (cliffordQ (signatureMatrix p q)) x * volumeElement p q e) := by
  conv_lhs => rw [← e.sum_repr x]
  conv_rhs => rw [← e.sum_repr x]
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact g74c_L2 _ _ (g74c_anti p q e he) j

theorem g74c_vol_sq (p q : ℕ) (e : Module.Basis (Fin (p + q)) ℝ (Fin (p + q) → ℝ))
    (he : PseudoOrthonormal p q e) :
    volumeElement p q e ^ 2 = algebraMap ℝ (RealCl p q)
      ((-1) ^ g74c_T (p + q) * ∏ i : Fin (p + q), -(signatureMatrix p q i i)) := by
  rw [sq]
  refine g74c_L3 _ _ _ (g74c_anti p q e he) (fun i => ?_)
  rw [CliffordAlgebra.ι_sq_scalar, g74c_Q, he]

section
variable {A : Type*} [Ring A] [Algebra ℝ A]

def g74c_Pf {n : ℕ} (γ : Fin n → A) (f : Fin n → Bool) : A :=
  (List.ofFn fun i => if f i then γ i else 1).prod

theorem g74c_Pf_succ {k : ℕ} (γ : Fin (k + 1) → A) (f : Fin (k + 1) → Bool) :
    g74c_Pf γ f = (if f 0 then γ 0 else 1) * g74c_Pf (fun i => γ i.succ) (fun i => f i.succ) := by
  simp [g74c_Pf, List.ofFn_succ]

theorem g74c_M : ∀ {k : ℕ} (γ : Fin k → A) (x : A), (∀ i, x * γ i = -(γ i * x)) →
    ∀ g : Fin k → Bool, ∃ ε : ℝ, IsSign ε ∧ g74c_Pf γ g * x = ε • (x * g74c_Pf γ g)
  | 0, γ, x, _, g => ⟨1, Or.inl rfl, by simp [g74c_Pf]⟩
  | k + 1, γ, x, hx, g => by
    obtain ⟨ε, hε, h⟩ := g74c_M (fun i => γ i.succ) x (fun i => hx _) (fun i => g i.succ)
    rw [g74c_Pf_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc]
    by_cases hg : g 0 = true
    · refine ⟨-ε, by rcases hε with rfl | rfl <;> simp [IsSign], ?_⟩
      simp only [hg, if_true]
      have : γ 0 * x = -(x * γ 0) := by rw [hx]; simp
      rw [this, neg_mul, smul_neg, neg_smul, mul_assoc]
    · refine ⟨ε, hε, ?_⟩
      simp only [hg, if_false, Bool.false_eq_true]
      simp [mul_assoc]

theorem g74c_K : ∀ {n : ℕ} (γ : Fin n → A) (κ : Fin n → ℝ),
    (∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i)) → (∀ i, γ i * γ i = algebraMap ℝ A (κ i)) →
    (∀ i, IsSign (κ i)) → ∀ (f : Fin n → Bool) (j : Fin n),
    ∃ ε : ℝ, IsSign ε ∧ g74c_Pf γ f * γ j = ε • g74c_Pf γ (Function.update f j (!f j))
  | 0, _, _, _, _, _, _, j => j.elim0
  | k + 1, γ, κ, hanti, hsq, hκ, f, j => by
    refine Fin.cases ?_ (fun j' => ?_) j
    · obtain ⟨ε, hε, h⟩ := g74c_M (fun i => γ i.succ) (γ 0)
        (fun i => hanti _ _ (Fin.succ_ne_zero i).symm) (fun i => f i.succ)
      rw [g74c_Pf_succ, mul_assoc, h, g74c_Pf_succ (f := Function.update f 0 (!f 0))]
      have htail : (fun i : Fin k => Function.update f 0 (!f 0) i.succ) = fun i => f i.succ := by
        funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
      rw [htail, Function.update_self, mul_smul_comm, ← mul_assoc]
      by_cases hf : f 0 = true
      · refine ⟨ε * κ 0, g74c_isSign_mul hε (hκ 0), ?_⟩
        simp only [hf, if_true, Bool.not_true, Bool.false_eq_true, if_false, hsq,
          Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
      · refine ⟨ε, hε, ?_⟩
        simp only [hf, Bool.false_eq_true, if_false, Bool.not_false, if_true, one_mul]
    · obtain ⟨ε, hε, h⟩ := g74c_K (fun i => γ i.succ) (fun i => κ i.succ)
        (fun i j hij => hanti _ _ (by simpa using hij)) (fun i => hsq _) (fun i => hκ _)
        (fun i => f i.succ) j'
      refine ⟨ε, hε, ?_⟩
      rw [g74c_Pf_succ, mul_assoc, h, g74c_Pf_succ (f := Function.update f j'.succ (!f j'.succ)),
        Function.update_of_ne (Fin.succ_ne_zero j').symm, mul_smul_comm]
      congr 3
      funext i
      by_cases hi : i = j'
      · subst hi; simp
      · rw [Function.update_of_ne hi, Function.update_of_ne (by simpa using hi)]

end

section
variable {S : Type*} [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]

theorem g74c_pos_form : ∃ b0 : LinearMap.BilinForm ℝ S, ∀ s : S, s ≠ 0 → 0 < b0 s s := by
  let B := Module.finBasis ℝ S
  refine ⟨LinearMap.mk₂ ℝ (fun s t => ∑ i, B.repr s i * B.repr t i) ?_ ?_ ?_ ?_, ?_⟩
  · intro s1 s2 t; simp [add_mul, Finset.sum_add_distrib]
  · intro c s t; simp [Finset.mul_sum, mul_assoc]
  · intro s t1 t2; simp [mul_add, Finset.sum_add_distrib]
  · intro c s t; simp [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  · intro s hs
    simp only [LinearMap.mk₂_apply]
    obtain ⟨i, hi⟩ : ∃ i, B.repr s i ≠ 0 := by
      by_contra h; push_neg at h
      exact hs (B.repr.injective (Finsupp.ext fun i => by simp [h i]))
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

end

section
set_option linter.unusedSectionVars false
variable {K : Type*} [Field K] [CharZero K] {d : ℕ}
variable {g : Matrix (Fin d) (Fin d) K}
variable {S : Type*} [AddCommGroup S] [Module K S]

theorem g74c_form_gen' (rho : SpinRepresentation g S) (b : LinearMap.BilinForm K S) (τ : K)
    (hτ : IsSign τ) (hc : ∀ v s t, b (cliffordVectorAction rho v s) t =
      τ * b s (cliffordVectorAction rho v t)) : b ∈ invariantForms rho := by
  have key : ∀ x y : Fin d → K, ∀ s t, b ((cliffordVectorAction rho x * cliffordVectorAction rho y) s) t
      = b s ((cliffordVectorAction rho y * cliffordVectorAction rho x) t) := by
    intro x y s t
    simp only [Module.End.mul_apply]
    rw [hc, hc, ← mul_assoc, g74c_sign_sq hτ, one_mul]
  intro u v s t
  simp only [spinGenerator, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub,
    LinearMap.smul_apply, LinearMap.sub_apply, key, smul_eq_mul]
  ring

end

/-- Lemma 1.5, PDF pp. 13--14: existence is a conclusion, not a self-duality hypothesis. -/
theorem solution (p q : ℕ) (hd : 0 < p + q)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S) :
    ∃ b : LinearMap.BilinForm ℝ S, b ∈ invariantForms rho ∧ b.Nondegenerate := by
  set γ : Fin (p + q) → Module.End ℝ S := fun i => cliffordVectorAction rho (Pi.single i 1) with hγ
  set κ : Fin (p + q) → ℝ := fun i => -(signatureMatrix p q i i) with hκdef
  have hκ : ∀ i, IsSign (κ i) := by
    intro i; simp only [hκdef, signatureMatrix, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [IsSign]
  have hsq : ∀ i, γ i * γ i = algebraMap ℝ _ (κ i) := by
    intro i
    have h2 := congrArg rho.action
      (CliffordAlgebra.ι_sq_scalar (cliffordQ (signatureMatrix p q)) (Pi.single i 1))
    rw [map_mul, AlgHom.commutes, g74c_Q, Matrix.toBilin'_single] at h2
    exact h2
  have hsqv : ∀ i x, γ i (γ i x) = κ i • x := by
    intro i x
    have := congrArg (fun F : Module.End ℝ S => F x) (hsq i)
    simpa [Algebra.algebraMap_eq_smul_one] using this
  have hanti : ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i) := by
    intro i j hij
    rw [hγ]
    simp only
    rw [g74c_rel rho, g74c_polar, Matrix.toBilin'_single, Matrix.toBilin'_single]
    simp [signatureMatrix, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij.symm]
  obtain ⟨b0, hb0⟩ := g74c_pos_form (S := S)
  have hb0nn : ∀ x, 0 ≤ b0 x x := by
    intro x; by_cases hx : x = 0
    · simp [hx]
    · exact (hb0 x hx).le
  set b1 : LinearMap.BilinForm ℝ S :=
    ∑ f : Fin (p + q) → Bool, b0.compl₁₂ (g74c_Pf γ f) (g74c_Pf γ f) with hb1def
  have hb1 : ∀ s t, b1 s t = ∑ f, b0 (g74c_Pf γ f s) (g74c_Pf γ f t) := by
    intro s t; simp [hb1def, LinearMap.sum_apply, LinearMap.compl₁₂_apply]
  have hb1inv : ∀ j s t, b1 (γ j s) (γ j t) = b1 s t := by
    intro j s t
    rw [hb1, hb1]
    have key : ∀ f, b0 (g74c_Pf γ f (γ j s)) (g74c_Pf γ f (γ j t)) =
        b0 (g74c_Pf γ (Function.update f j (!f j)) s)
          (g74c_Pf γ (Function.update f j (!f j)) t) := by
      intro f
      obtain ⟨ε, hε, h⟩ := g74c_K γ κ hanti hsq hκ f j
      have e1 : ∀ x, g74c_Pf γ f (γ j x) = ε • g74c_Pf γ (Function.update f j (!f j)) x := by
        intro x; rw [← Module.End.mul_apply, h, LinearMap.smul_apply]
      rw [e1, e1]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, g74c_sign_sq hε, one_mul]
    rw [Finset.sum_congr rfl (fun f _ => key f)]
    have hinv : Function.Involutive (fun f : Fin (p + q) → Bool => Function.update f j (!f j)) := by
      intro f; funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Function.update_of_ne hi]
    exact Equiv.sum_comp hinv.toPerm (fun f => b0 (g74c_Pf γ f s) (g74c_Pf γ f t))
  have hb1pos : ∀ s, s ≠ 0 → 0 < b1 s s := by
    intro s hs
    rw [hb1]
    have h1 : g74c_Pf γ (fun _ => false) = 1 := by simp [g74c_Pf]
    have := Finset.single_le_sum (f := fun f => b0 (g74c_Pf γ f s) (g74c_Pf γ f s))
      (fun f _ => hb0nn _) (Finset.mem_univ (fun _ => false))
    simp only [h1, Module.End.one_apply] at this
    exact lt_of_lt_of_le (hb0 s hs) this
  have hb1rel : ∀ j s t, b1 (γ j s) t = κ j * b1 s (γ j t) := by
    intro j s t
    have := hb1inv j s (γ j t)
    rw [hsqv, map_smul, smul_eq_mul] at this
    rw [← this, ← mul_assoc, g74c_sign_sq (hκ j), one_mul]
  set Pp : Module.End ℝ S := (List.ofFn fun i : Fin p => γ (Fin.castAdd q i)).prod with hPp
  have hconv : ∀ (m : ℕ) (X : Module.End ℝ S), ((-1 : ℝ) ^ m) • X = (-1 : Module.End ℝ S) ^ m * X := by
    intro m X
    rcases Nat.even_or_odd m with h | h <;> simp [h.neg_one_pow]
  have hPrel : ∀ j, γ j * Pp = (κ j * (-1) ^ p) • (Pp * γ j) := by
    intro j
    by_cases hj : j.val < p
    · have hjj : j = Fin.castAdd q ⟨j.val, hj⟩ := Fin.ext rfl
      have hL := g74c_L2 p (fun i : Fin p => γ (Fin.castAdd q i))
        (fun i j hij => hanti _ _ (fun h => hij (Fin.castAdd_injective _ _ h))) ⟨j.val, hj⟩
      rw [← hjj, ← hPp] at hL
      have hk : κ j = -1 := by simp [hκdef, signatureMatrix, hj]
      rw [hL, hk]
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [show (-1 : ℝ) * (-1) ^ (p' + 1) = (-1) ^ p' by ring, Nat.add_sub_cancel, hconv,
        ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    · have hL := g74c_L1 (γ j) (List.ofFn fun i : Fin p => γ (Fin.castAdd q i)) (by
        intro y hy
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
        exact hanti _ _ (fun h => hj (by rw [h]; exact i.isLt)))
      rw [← hPp, List.length_ofFn] at hL
      have hk : κ j = 1 := by simp [hκdef, signatureMatrix, hj]
      rw [hL, hk, one_mul, hconv]
  set b2 : LinearMap.BilinForm ℝ S := b1.compl₂ Pp with hb2def
  have hb2 : ∀ s t, b2 s t = b1 s (Pp t) := fun s t => rfl
  have hb2rel : ∀ j s t, b2 (γ j s) t = (-1) ^ p * b2 s (γ j t) := by
    intro j s t
    rw [hb2, hb2, hb1rel, ← Module.End.mul_apply, hPrel, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Module.End.mul_apply, ← mul_assoc, ← mul_assoc, g74c_sign_sq (hκ j), one_mul]
  have hτ : IsSign ((-1 : ℝ) ^ p) := by
    rcases Nat.even_or_odd p with h | h <;> simp [h.neg_one_pow, IsSign]
  have hc : ∀ v s t, b2 (cliffordVectorAction rho v s) t =
      (-1) ^ p * b2 s (cliffordVectorAction rho v t) := by
    intro v s t
    have hv : v = ∑ i, v i • (Pi.single i 1 : Fin (p + q) → ℝ) := by
      ext k; simp [Pi.single_apply]
    rw [hv]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hb2rel i s t
    simp only [hγ] at this
    rw [this]; ring
  refine ⟨b2, g74c_form_gen' rho b2 _ hτ hc, ?_⟩
  obtain ⟨hPanti, hPsq⟩ : (∀ i j : Fin p, i ≠ j → γ (Fin.castAdd q i) * γ (Fin.castAdd q j) =
      -(γ (Fin.castAdd q j) * γ (Fin.castAdd q i))) ∧
      (∀ i : Fin p, γ (Fin.castAdd q i) * γ (Fin.castAdd q i) =
        algebraMap ℝ _ (κ (Fin.castAdd q i))) :=
    ⟨fun i j hij => hanti _ _ (fun h => hij (Fin.castAdd_injective _ _ h)), fun i => hsq _⟩
  have hPP := g74c_L3 p (fun i => γ (Fin.castAdd q i)) (fun i => κ (Fin.castAdd q i)) hPanti hPsq
  rw [← hPp] at hPP
  set lam : ℝ := (-1) ^ g74c_T p * ∏ i : Fin p, κ (Fin.castAdd q i) with hlam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    rcases hκ (Fin.castAdd q i) with h | h <;> rw [h] <;> norm_num
  have hPPv : ∀ x, Pp (Pp x) = lam • x := by
    intro x
    have := congrArg (fun F : Module.End ℝ S => F x) hPP
    simpa [Algebra.algebraMap_eq_smul_one] using this
  constructor
  · intro s hs
    by_contra hne
    have := hs (Pp s)
    rw [hb2, hPPv, map_smul, smul_eq_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hlam0 h
    · exact (hb1pos s hne).ne' h
  · intro t ht
    by_contra hne
    have h1 := ht (Pp t)
    rw [hb2] at h1
    have hPt : Pp t ≠ 0 := by
      intro h0
      have := hPPv t
      rw [h0, map_zero] at this
      exact hne ((smul_eq_zero.mp this.symm).resolve_left hlam0)
    exact (hb1pos _ hPt).ne' h1
