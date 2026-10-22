-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.definite_pin_form_admissible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:52:22.475432+00:00
-- url     : https://prove2.me/submissions/1056b968-ee4e-4165-bb5c-a6c24f37f6ec

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
variable {S : Type*} [AddCommGroup S] [Module ℝ S]

@[instance_reducible]
noncomputable def g74c_core (b : LinearMap.BilinForm ℝ S) (hsym : b.IsSymm)
    (hpos : ∀ s : S, s ≠ 0 → 0 < b s s) : InnerProductSpace.Core ℝ S where
  inner x y := b x y
  conj_inner_symm x y := by
    simp only [conj_trivial]; exact LinearMap.BilinForm.isSymm_def.mp hsym y x
  re_inner_nonneg x := by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h; exact (hpos x h).ne' hx

theorem g74c_spec [FiniteDimensional ℝ S] [Nontrivial S] (b : LinearMap.BilinForm ℝ S)
    (hsym : b.IsSymm) (hpos : ∀ s : S, s ≠ 0 → 0 < b s s) :
    (∀ E : Module.End ℝ S, ∃ F : Module.End ℝ S, ∀ x y, b (E x) y = b x (F y)) ∧
    (∀ H : Module.End ℝ S, (∀ x y, b (H x) y = b x (H y)) →
      ∃ μ : ℝ, ∃ v : S, v ≠ 0 ∧ H v = μ • v) := by
  letI : NormedAddCommGroup S :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ S _ _ _ (g74c_core b hsym hpos)
  letI : InnerProductSpace ℝ S := InnerProductSpace.ofCore (g74c_core b hsym hpos).toCore
  constructor
  · intro E
    refine ⟨LinearMap.adjoint E, fun x y => ?_⟩
    exact (LinearMap.adjoint_inner_right E x y).symm
  · intro H hH
    have hS : H.IsSymmetric := fun x y => hH x y
    obtain ⟨v, hv⟩ := (hS.hasEigenvalue_iSup_of_finiteDimensional).exists_hasEigenvector
    exact ⟨_, v, hv.2, hv.apply_eq_smul⟩

end

theorem g74c_bil_diag (p q : ℕ) (v : Fin (p + q) → ℝ) :
    (signatureMatrix p q).toBilin' v v = ∑ i, (if i.val < p then 1 else -1) * (v i * v i) := by
  simp only [signatureMatrix, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem g74c_sumsq_pos {n : ℕ} (v : Fin n → ℝ) (hv : v ≠ 0) : 0 < ∑ i, v i * v i := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

/-- Lemma 3.7, PDF p. 24: the definite Pin-invariant positive scalar product has all
three asserted invariants, with isotropy asserted only for a genuine splitting. -/
theorem solution (p q : ℕ) (hd : 0 < p + q)
    (hdefinite : p = 0 ∨ q = 0)
    (S : Type*) [AddCommGroup S] [Module ℝ S] [FiniteDimensional ℝ S]
    (rho : SpinRepresentation (signatureMatrix p q) S)
    (splitting : Option (SpinSplitting rho)) (hs : CompleteSplitting rho splitting)
    (b : LinearMap.BilinForm ℝ S) (hsymm : b.IsSymm)
    (hpositive : ∀ s : S, s ≠ 0 → 0 < b s s) (hpin : PinInvariant rho b) :
    FormAdmissible rho splitting b ∧
    FormSigns rho b (if q = 0 then -1 else 1) 1 ∧
    (∀ h : SpinSplitting rho, splitting = some h → FormIsotropy h.grading b 1) := by
  haveI : Nontrivial S := rho.irreducible.1
  have bsym : ∀ x y, b x y = b y x := LinearMap.BilinForm.isSymm_def.mp hsymm
  obtain ⟨hadj, heig⟩ := g74c_spec b hsymm hpositive
  have bext : ∀ w1 w2 : S, (∀ x, b x w1 = b x w2) → w1 = w2 := by
    intro w1 w2 h
    by_contra hne
    have := hpositive (w1 - w2) (sub_ne_zero.mpr hne)
    rw [map_sub (b (w1 - w2)), h (w1 - w2), sub_self] at this
    exact lt_irrefl _ this
  set τ : ℝ := if q = 0 then -1 else 1 with hτdef
  have hτs : IsSign τ := by by_cases hq : q = 0 <;> simp [hτdef, hq, IsSign]
  have hsq : ∀ (u : Fin (p + q) → ℝ) (t : S), cliffordVectorAction rho u (cliffordVectorAction rho u t)
      = cliffordQ (signatureMatrix p q) u • t := by
    intro u t
    have h2 := congrArg rho.action (CliffordAlgebra.ι_sq_scalar (cliffordQ (signatureMatrix p q)) u)
    rw [map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one] at h2
    have := congrArg (fun F : Module.End ℝ S => F t) h2
    simp only [Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
    exact this
  have hunit : ∀ u : Fin (p + q) → ℝ, ((signatureMatrix p q).toBilin' u u = 1 ∨
      (signatureMatrix p q).toBilin' u u = -1) → ∀ s t,
      b (cliffordVectorAction rho u s) t =
        -(signatureMatrix p q).toBilin' u u * b s (cliffordVectorAction rho u t) := by
    intro u hu s t
    have h1 := hpin u hu s (cliffordVectorAction rho u t)
    rw [hsq, g74c_Q, map_smul, smul_eq_mul] at h1
    rw [← h1]
    rcases hu with hu | hu <;> rw [hu] <;> ring
  have hc : ∀ v s t, b (cliffordVectorAction rho v s) t = τ * b s (cliffordVectorAction rho v t) := by
    intro v s t
    by_cases hv : v = 0
    · subst hv; simp
    set c := (signatureMatrix p q).toBilin' v v with hcdef
    have hcs : (q = 0 → 0 < c) ∧ (q ≠ 0 → c < 0) := by
      rw [hcdef, g74c_bil_diag]
      constructor
      · intro hq
        have : ∀ i : Fin (p + q), (if i.val < p then (1 : ℝ) else -1) * (v i * v i) = v i * v i :=
          fun i => by rw [if_pos (by omega), one_mul]
        simp only [this]; exact g74c_sumsq_pos v hv
      · intro hq
        have hp : p = 0 := by omega
        have : ∀ i : Fin (p + q), (if i.val < p then (1 : ℝ) else -1) * (v i * v i) = -(v i * v i) :=
          fun i => by rw [if_neg (by omega)]; ring
        simp only [this, Finset.sum_neg_distrib]; linarith [g74c_sumsq_pos v hv]
    have hc0 : c ≠ 0 := by
      by_cases hq : q = 0
      · exact (hcs.1 hq).ne'
      · exact (hcs.2 hq).ne
    set r := Real.sqrt |c| with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr (abs_pos.mpr hc0)
    have hrr : r * r = |c| := Real.mul_self_sqrt (abs_nonneg c)
    obtain ⟨u, hu⟩ : ∃ u : Fin (p + q) → ℝ, u = r⁻¹ • v := ⟨_, rfl⟩
    have hvu : v = r • u := by rw [hu, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have huu : (signatureMatrix p q).toBilin' u u = c / |c| := by
      rw [hu]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← hcdef, ← hrr]
      field_simp
    have hκ : (signatureMatrix p q).toBilin' u u = -τ := by
      rw [huu, hτdef]
      by_cases hq : q = 0
      · rw [if_pos hq, abs_of_pos (hcs.1 hq), div_self hc0]; ring
      · rw [if_neg hq, abs_of_neg (hcs.2 hq), div_neg, div_self hc0]
    have hU := hunit u (by rw [hκ]; rcases hτs with h | h <;> rw [h] <;> simp) s t
    rw [hκ, neg_neg] at hU
    rw [hvu]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hU]
    ring
  have hFS : FormSigns rho b τ 1 := ⟨hτs, Or.inl rfl, hc, fun s t => by rw [one_mul]; exact bsym t s⟩
  have hc' : ∀ v x y, b x (cliffordVectorAction rho v y) = τ * b (cliffordVectorAction rho v x) y := by
    intro v x y
    rw [hc, ← mul_assoc, g74c_sign_sq hτs, one_mul]
  have hiso : ∀ h : SpinSplitting rho, FormIsotropy h.grading b 1 := by
    intro h
    set E := h.grading with hE
    have hodd : ∀ v x, E (cliffordVectorAction rho v x) = -(cliffordVectorAction rho v (E x)) := by
      intro v x
      have := congrArg (fun F : Module.End ℝ S => F x) (h.odd v)
      simpa using this
    have hEE : ∀ x, E (E x) = x := by
      intro x
      have := congrArg (fun F : Module.End ℝ S => F x) h.square
      simpa using this
    obtain ⟨F, hF⟩ := hadj E
    have hF' : ∀ x y, b (F x) y = b x (E y) := by
      intro x y; rw [bsym, ← hF, bsym]
    have hFanti : ∀ v x, cliffordVectorAction rho v (F x) = -(F (cliffordVectorAction rho v x)) := by
      intro v x
      apply bext
      intro y
      rw [hc', ← hF, hodd, map_neg, LinearMap.neg_apply, hc, hF, map_neg]
      linear_combination (-(b y (F (cliffordVectorAction rho v x)))) * g74c_sign_sq hτs
    set H : Module.End ℝ S := F * E with hH
    have hHs : ∀ x y, b (H x) y = b x (H y) := by
      intro x y
      simp only [hH, Module.End.mul_apply]
      rw [hF', hF]
    have hHc : ∀ v, cliffordVectorAction rho v * H = H * cliffordVectorAction rho v := by
      intro v; ext x
      simp only [hH, Module.End.mul_apply]
      rw [hFanti, hodd, map_neg]
    have hHall : ∀ a, rho.action a * H = H * rho.action a := by
      intro a
      induction a using CliffordAlgebra.induction with
      | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r H
      | ι w => exact hHc w
      | mul a1 a2 h1 h2 => rw [map_mul, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
      | add a1 a2 h1 h2 => rw [map_add, add_mul, mul_add, h1, h2]
    obtain ⟨μ, w, hw0, hw⟩ := heig H hHs
    have hstab : SpinStable (Set.range rho.action) (LinearMap.ker (H - μ • 1)) := by
      rintro _ ⟨a, rfl⟩ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have := congrArg (fun F : Module.End ℝ S => F x) (hHall a)
      simp only [Module.End.mul_apply] at this
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢
      rw [← this, sub_eq_zero.mp hx, map_smul, sub_self]
    have hwk : w ∈ LinearMap.ker (H - μ • 1) := by
      simp [hw]
    rcases rho.irreducible.2 _ hstab with h0 | h0
    · rw [h0] at hwk; exact absurd hwk hw0
    have hHμ : ∀ x, H x = μ • x := by
      intro x
      have : x ∈ LinearMap.ker (H - μ • 1) := by rw [h0]; trivial
      simpa [sub_eq_zero] using this
    have hFμ : ∀ x, F x = μ • E x := by
      intro x
      have := hHμ (E x)
      simp only [hH, Module.End.mul_apply, hEE] at this
      exact this
    have hμpos : 0 < μ := by
      have h1 := hHs w w
      have hEw : E w ≠ 0 := fun h0' => hw0 (by rw [← hEE w, h0', map_zero])
      have h2 : b (H w) w = b (E w) (E w) := by
        simp only [hH, Module.End.mul_apply]; rw [hF']
      rw [hHμ, map_smul, LinearMap.smul_apply, smul_eq_mul] at h2
      have := hpositive _ hEw
      have := hpositive _ hw0
      nlinarith
    have hFF : ∀ x, F (F x) = x := by
      intro x; apply bext; intro y
      rw [← hF, ← hF, hEE]
    have hμ1 : μ = 1 := by
      have := hFF w
      rw [hFμ (F w), hFμ w, map_smul, hEE, smul_smul] at this
      have h2 : (μ * μ - 1) • w = 0 := by rw [sub_smul, this, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h3 | h3
      · nlinarith
      · exact absurd h3 hw0
    refine ⟨Or.inl rfl, fun s t => ?_⟩
    rw [hF, hFμ, hμ1, one_smul, one_mul]
  refine ⟨⟨τ, 1, hFS, ?_⟩, hFS, fun h _ => hiso h⟩
  cases splitting with
  | none => trivial
  | some h => exact ⟨1, hiso h⟩
