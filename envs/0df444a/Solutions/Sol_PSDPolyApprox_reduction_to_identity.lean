-- Prove2me | solution 1 for PSDPolyApprox.reduction_to_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:18:26.545664+00:00
-- url     : https://prove2.me/submissions/b122b157-894d-4d23-868e-cf989a321436

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_PSDPolyApprox_shiftedDensity

open ExtensionComplexity.TSP
open scoped Pointwise Matrix

namespace Aux_R6R


open Matrix

lemma mv {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ) (i : m) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

lemma comp_eq_iff {E F : Type*} (e : F ≃ E) (u v w : E → ℝ) :
    u ∘ e + v ∘ e = w ∘ e ↔ u + v = w := by
  constructor
  · intro h
    funext i
    have := congrFun h (e.symm i)
    simpa using this
  · intro h
    rw [← h]
    rfl

lemma comp_le_iff {E F : Type*} (e : F ≃ E) (u v w : E → ℝ) :
    u ∘ e + v ∘ e ≤ w ∘ e ↔ u + v ≤ w := by
  constructor
  · intro h
    refine Pi.le_def.mpr fun i => ?_
    have := Pi.le_def.mp h (e.symm i)
    simpa using this
  · intro h
    refine Pi.le_def.mpr fun i => ?_
    have := Pi.le_def.mp h (e i)
    simpa using this

lemma toEF {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) {K E R : Type*} [Fintype K] [Fintype E]
    [Fintype R] (r : ℕ) (eR : R ≃ Fin r)
    (A : Matrix E ι ℝ) (B : Matrix E K ℝ) (a : E → ℝ) (C : Matrix R ι ℝ) (D : Matrix R K ℝ)
    (d : R → ℝ)
    (hP : ∀ x, x ∈ P ↔ ∃ y : K → ℝ, A *ᵥ x + B *ᵥ y = a ∧ C *ᵥ x + D *ᵥ y ≤ d) :
    IsEFOfSize P r := by
  classical
  let eK := Fintype.equivFin K
  let eE := Fintype.equivFin E
  refine ⟨Fintype.card K, Fintype.card E, A.submatrix eE.symm (Equiv.refl ι),
    B.submatrix eE.symm eK.symm, a ∘ eE.symm, C.submatrix eR.symm (Equiv.refl ι),
    D.submatrix eR.symm eK.symm, d ∘ eR.symm, ?_⟩
  intro x
  have key : ∀ y' : Fin (Fintype.card K) → ℝ,
      (A.submatrix eE.symm (Equiv.refl ι) *ᵥ x + B.submatrix eE.symm eK.symm *ᵥ y' = a ∘ eE.symm ↔
        A *ᵥ x + B *ᵥ (y' ∘ eK) = a) ∧
      (C.submatrix eR.symm (Equiv.refl ι) *ᵥ x + D.submatrix eR.symm eK.symm *ᵥ y' ≤ d ∘ eR.symm ↔
        C *ᵥ x + D *ᵥ (y' ∘ eK) ≤ d) := by
    intro y'
    simp only [Matrix.submatrix_mulVec_equiv]
    simp only [Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, Function.comp_id]
    exact ⟨comp_eq_iff eE.symm _ _ _, comp_le_iff eR.symm _ _ _⟩
  rw [hP x]
  constructor
  · rintro ⟨y, h1, h2⟩
    have hy : (y ∘ eK.symm) ∘ eK = y := by funext i; simp
    refine ⟨y ∘ eK.symm, ?_, ?_⟩
    · rw [(key _).1, hy]; exact h1
    · rw [(key _).2, hy]; exact h2
  · rintro ⟨y', h1, h2⟩
    exact ⟨y' ∘ eK, (key y').1.mp h1, (key y').2.mp h2⟩

/-! ### Extended formulation of a polytope -/

def polyA (ι : Type*) [DecidableEq ι] : Matrix (Option ι) ι ℝ :=
  Matrix.of fun o j => Option.elim o 0 (fun i => if i = j then 1 else 0)

def polyB {ι : Type*} (V : Finset (ι → ℝ)) : Matrix (Option ι) V ℝ :=
  Matrix.of fun o v => Option.elim o 1 (fun i => -((v : ι → ℝ) i))

def polya (ι : Type*) : Option ι → ℝ := fun o => Option.elim o 1 (fun _ => 0)

lemma polyEF {ι : Type*} [Fintype ι] (P : Set (ι → ℝ)) (h : IsPolytope P) :
    ∃ r, IsEFOfSize P r := by
  classical
  obtain ⟨V, rfl⟩ := h
  refine ⟨Fintype.card V, toEF _ (Fintype.card V) (Fintype.equivFin V) (polyA ι) (polyB V)
    (polya ι) (0 : Matrix V ι ℝ) (-1 : Matrix V V ℝ) 0 ?_⟩
  intro x
  have hull : x ∈ convexHull ℝ (V : Set (ι → ℝ)) ↔ ∃ y : V → ℝ, (∀ v, 0 ≤ y v) ∧
      ∑ v, y v = 1 ∧ ∀ i, ∑ v, y v * (v : ι → ℝ) i = x i := by
    constructor
    · intro hx
      obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
      refine ⟨fun v => w v, fun v => hw0 v v.2, ?_, ?_⟩
      · rw [Finset.sum_coe_sort V w]; exact hw1
      · intro i
        rw [← hwx, Finset.sum_apply, ← Finset.sum_coe_sort V]
        simp only [Pi.smul_apply, smul_eq_mul]
    · rintro ⟨y, hy0, hy1, hyx⟩
      have hx : ∑ v, y v • (v : ι → ℝ) = x := by
        funext i
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hyx i
      exact mem_convexHull_of_exists_fintype y (fun v : V => (v : ι → ℝ)) hy0 hy1
        (fun v => Finset.mem_coe.mpr v.2) hx
  rw [hull]
  refine exists_congr fun y => ?_
  have r0 : (polyA ι *ᵥ x + polyB V *ᵥ y) none = ∑ v, y v := by
    rw [Pi.add_apply, mv, mv]
    simp [polyA, polyB]
  have r1 : ∀ i, (polyA ι *ᵥ x + polyB V *ᵥ y) (some i) = x i - ∑ v, y v * (v : ι → ℝ) i := by
    intro i
    rw [Pi.add_apply, mv, mv]
    have e1 : ∑ j, polyA ι (some i) j * x j = x i := by simp [polyA]
    have e2 : ∑ v, polyB V (some i) v * y v = -∑ v, y v * (v : ι → ℝ) i := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      simp only [polyB, Matrix.of_apply, Option.elim_some]
      ring
    rw [e1, e2]
    ring
  have hle : (0 : Matrix V ι ℝ) *ᵥ x + (-1 : Matrix V V ℝ) *ᵥ y ≤ 0 ↔ ∀ v, 0 ≤ y v := by
    rw [Matrix.zero_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec, zero_add, neg_nonpos]
    exact Pi.le_def
  have ha0 : polya ι none = 1 := rfl
  have ha1 : ∀ i, polya ι (some i) = 0 := fun i => rfl
  simp only [hle, funext_iff, Option.forall, r0, r1, ha0, ha1, sub_eq_zero]
  constructor
  · rintro ⟨h3, h1, h2⟩
    exact ⟨⟨h1, fun i => (h2 i).symm⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, h1, fun i => (h2 i).symm⟩

/-! ### Minkowski sum -/

def bigA {ι S₁ S₂ : Type*} (A₂ : Matrix S₂ ι ℝ) : Matrix (S₁ ⊕ S₂) ι ℝ :=
  Matrix.of fun s i => Sum.elim (fun _ => 0) (fun s₂ => A₂ s₂ i) s

def bigB {ι S₁ S₂ T₁ T₂ : Type*} (A₁ : Matrix S₁ ι ℝ) (B₁ : Matrix S₁ T₁ ℝ)
    (A₂ : Matrix S₂ ι ℝ) (B₂ : Matrix S₂ T₂ ℝ) : Matrix (S₁ ⊕ S₂) (ι ⊕ (T₁ ⊕ T₂)) ℝ :=
  Matrix.of fun s k => Sum.elim
    (fun s₁ => Sum.elim (fun i => A₁ s₁ i) (Sum.elim (fun j => B₁ s₁ j) (fun _ => 0)) k)
    (fun s₂ => Sum.elim (fun i => -A₂ s₂ i) (Sum.elim (fun _ => 0) (fun j => B₂ s₂ j)) k) s

lemma rows {ι S₁ S₂ T₁ T₂ : Type*} [Fintype ι] [Fintype T₁] [Fintype T₂]
    (A₁ : Matrix S₁ ι ℝ) (B₁ : Matrix S₁ T₁ ℝ)
    (A₂ : Matrix S₂ ι ℝ) (B₂ : Matrix S₂ T₂ ℝ) (x : ι → ℝ) (y : ι ⊕ (T₁ ⊕ T₂) → ℝ) :
    bigA (S₁ := S₁) A₂ *ᵥ x + bigB A₁ B₁ A₂ B₂ *ᵥ y =
      Sum.elim (A₁ *ᵥ (fun i => y (Sum.inl i)) + B₁ *ᵥ (fun j => y (Sum.inr (Sum.inl j))))
        (A₂ *ᵥ (x - fun i => y (Sum.inl i)) + B₂ *ᵥ (fun j => y (Sum.inr (Sum.inr j)))) := by
  funext s
  cases s with
  | inl s =>
    simp only [Pi.add_apply, mv, bigA, bigB, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, zero_add] <;> ring
  | inr s =>
    simp only [Pi.add_apply, Pi.sub_apply, mv, bigA, bigB, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul,
      Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib] <;> ring

lemma elim_eq_iff {S₁ S₂ : Type*} (u₁ g₁ : S₁ → ℝ) (u₂ g₂ : S₂ → ℝ) :
    Sum.elim u₁ u₂ = Sum.elim g₁ g₂ ↔ u₁ = g₁ ∧ u₂ = g₂ := by
  constructor
  · intro h
    exact ⟨funext fun s => congrFun h (Sum.inl s), funext fun s => congrFun h (Sum.inr s)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma elim_le_iff {S₁ S₂ : Type*} (u₁ g₁ : S₁ → ℝ) (u₂ g₂ : S₂ → ℝ) :
    Sum.elim u₁ u₂ ≤ Sum.elim g₁ g₂ ↔ u₁ ≤ g₁ ∧ u₂ ≤ g₂ := by
  constructor
  · intro h
    exact ⟨Pi.le_def.mpr fun s => Pi.le_def.mp h (Sum.inl s),
      Pi.le_def.mpr fun s => Pi.le_def.mp h (Sum.inr s)⟩
  · rintro ⟨h1, h2⟩
    refine Pi.le_def.mpr fun s => ?_
    cases s with
    | inl s => exact Pi.le_def.mp h1 s
    | inr s => exact Pi.le_def.mp h2 s

lemma sumEF {ι : Type*} [Fintype ι] (P₁ P₂ : Set (ι → ℝ)) (r₁ r₂ : ℕ)
    (h1 : IsEFOfSize P₁ r₁) (h2 : IsEFOfSize P₂ r₂) : IsEFOfSize (P₁ + P₂) (r₁ + r₂) := by
  classical
  obtain ⟨k₁, p₁, A₁, B₁, a₁, C₁, D₁, d₁, hP₁⟩ := h1
  obtain ⟨k₂, p₂, A₂, B₂, a₂, C₂, D₂, d₂, hP₂⟩ := h2
  refine toEF (P₁ + P₂) (r₁ + r₂) finSumFinEquiv (bigA (S₁ := Fin p₁) A₂) (bigB A₁ B₁ A₂ B₂)
    (Sum.elim a₁ a₂) (bigA (S₁ := Fin r₁) C₂) (bigB C₁ D₁ C₂ D₂) (Sum.elim d₁ d₂) ?_
  intro x
  rw [Set.mem_add]
  constructor
  · rintro ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    obtain ⟨y₁, e₁, l₁⟩ := (hP₁ x₁).mp hx₁
    obtain ⟨y₂, e₂, l₂⟩ := (hP₂ x₂).mp hx₂
    refine ⟨Sum.elim x₁ (Sum.elim y₁ y₂), ?_, ?_⟩
    · rw [rows, elim_eq_iff]
      have hx : (x₁ + x₂ - fun i => Sum.elim x₁ (Sum.elim y₁ y₂) (Sum.inl i)) = x₂ := by
        funext i; simp
      rw [hx]
      exact ⟨e₁, e₂⟩
    · rw [rows, elim_le_iff]
      have hx : (x₁ + x₂ - fun i => Sum.elim x₁ (Sum.elim y₁ y₂) (Sum.inl i)) = x₂ := by
        funext i; simp
      rw [hx]
      exact ⟨l₁, l₂⟩
  · rintro ⟨y, he, hl⟩
    rw [rows, elim_eq_iff] at he
    rw [rows, elim_le_iff] at hl
    refine ⟨fun i => y (Sum.inl i), (hP₁ _).mpr ⟨_, he.1, hl.1⟩,
      x - fun i => y (Sum.inl i), (hP₂ _).mpr ⟨_, he.2, hl.2⟩, ?_⟩
    funext i
    simp


/-! ### Linear images, zero, finite sums -/

def iA (κ : Type*) [DecidableEq κ] (p : ℕ) : Matrix (κ ⊕ Fin p) κ ℝ :=
  Matrix.of fun s i => Sum.elim (fun i' => if i' = i then (1 : ℝ) else 0) (fun _ => 0) s

def iB {κ ι : Type*} {p k : ℕ} (L : Matrix κ ι ℝ) (Ae : Matrix (Fin p) ι ℝ)
    (Fq : Matrix (Fin p) (Fin k) ℝ) : Matrix (κ ⊕ Fin p) (ι ⊕ Fin k) ℝ :=
  Matrix.of fun s t => Sum.elim (fun i' => Sum.elim (fun j => -L i' j) (fun _ => (0 : ℝ)) t)
    (fun q => Sum.elim (fun j => Ae q j) (fun l => Fq q l) t) s

def iD {ι : Type*} {r k : ℕ} (El : Matrix (Fin r) ι ℝ) (Fl : Matrix (Fin r) (Fin k) ℝ) :
    Matrix (Fin r) (ι ⊕ Fin k) ℝ :=
  Matrix.of fun q t => Sum.elim (fun j => El q j) (fun l => Fl q l) t

lemma rowsI {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] {p k : ℕ}
    (L : Matrix κ ι ℝ) (Ae : Matrix (Fin p) ι ℝ) (Fq : Matrix (Fin p) (Fin k) ℝ)
    (x : κ → ℝ) (w : ι ⊕ Fin k → ℝ) :
    iA κ p *ᵥ x + iB L Ae Fq *ᵥ w =
      Sum.elim (x - L *ᵥ (w ∘ Sum.inl)) (Ae *ᵥ (w ∘ Sum.inl) + Fq *ᵥ (w ∘ Sum.inr)) := by
  funext s
  cases s with
  | inl i =>
    simp only [Pi.add_apply, Pi.sub_apply, mv, iA, iB, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Function.comp_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_const_zero, add_zero] <;> ring
  | inr q =>
    simp only [Pi.add_apply, mv, iA, iB, Matrix.of_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Function.comp_apply, zero_mul, Finset.sum_const_zero,
      zero_add] <;> ring

lemma rowsD {κ ι : Type*} [Fintype κ] [Fintype ι] {r k : ℕ}
    (El : Matrix (Fin r) ι ℝ) (Fl : Matrix (Fin r) (Fin k) ℝ) (x : κ → ℝ) (w : ι ⊕ Fin k → ℝ) :
    (0 : Matrix (Fin r) κ ℝ) *ᵥ x + iD El Fl *ᵥ w = El *ᵥ (w ∘ Sum.inl) + Fl *ᵥ (w ∘ Sum.inr) := by
  funext q
  simp only [Pi.add_apply, mv, iD, Matrix.of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add]

lemma imgEF {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (P : Set (ι → ℝ)) (r : ℕ)
    (L : Matrix κ ι ℝ) (h : IsEFOfSize P r) : IsEFOfSize ((fun v => L *ᵥ v) '' P) r := by
  classical
  obtain ⟨k, p, Ae, Fq, gq, El, Fl, gl, hP⟩ := h
  refine toEF _ r (Equiv.refl _) (iA κ p) (iB L Ae Fq) (Sum.elim 0 gq)
    (0 : Matrix (Fin r) κ ℝ) (iD El Fl) gl ?_
  intro x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨y, h1, h2⟩ := (hP z).mp hz
    refine ⟨Sum.elim z y, ?_, ?_⟩
    · rw [rowsI, elim_eq_iff, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_self]
      exact ⟨rfl, h1⟩
    · rw [rowsD, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact h2
  · rintro ⟨w, h1, h2⟩
    rw [rowsI, elim_eq_iff] at h1
    rw [rowsD] at h2
    exact ⟨w ∘ Sum.inl, (hP _).mpr ⟨w ∘ Sum.inr, h1.2, h2⟩, (sub_eq_zero.mp h1.1).symm⟩

lemma zeroEF (κ : Type*) [Fintype κ] [DecidableEq κ] : IsEFOfSize ({0} : Set (κ → ℝ)) 0 := by
  refine toEF ({0} : Set (κ → ℝ)) 0 (Equiv.refl (Fin 0)) (1 : Matrix κ κ ℝ)
    (0 : Matrix κ (Fin 0) ℝ) 0 (0 : Matrix (Fin 0) κ ℝ) (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 ?_
  intro x
  constructor
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨0, ?_, ?_⟩
    · rw [hx, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    · simp
  · rintro ⟨y, h1, -⟩
    rw [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero] at h1
    exact Set.mem_singleton_iff.mpr h1

lemma sumsEF {ι0 κ : Type*} [Fintype κ] [DecidableEq κ] (S : ι0 → Set (κ → ℝ)) (r : ℕ)
    (h : ∀ i, IsEFOfSize (S i) r) (s : Finset ι0) :
    IsEFOfSize (∑ i ∈ s, S i) (s.card * r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.card_empty, zero_mul, ← Set.singleton_zero]
    exact zeroEF κ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have := sumEF _ _ _ _ (h a) ih
    rwa [show r + s.card * r = (s.card + 1) * r by ring] at this

lemma polySum {ι0 κ : Type*} [Fintype κ] (S : ι0 → Set (κ → ℝ))
    (h : ∀ i, IsPolytope (S i)) (s : Finset ι0) : IsPolytope (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, ← Set.singleton_zero]
    exact ⟨{0}, by rw [Finset.coe_singleton, convexHull_singleton]⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨V, hV⟩ := h a
    obtain ⟨W, hW⟩ := ih
    refine ⟨V + W, ?_⟩
    rw [hV, hW, Finset.coe_add, convexHull_add]

/-! ### Congruence maps -/

def cong {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n × Fin n → ℝ) : Fin n × Fin n → ℝ :=
  Matrix.vec (M * Matrix.of (fun a b => v (b, a)) * Mᵀ)

lemma cong_lin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : IsLinearMap ℝ (cong M) := by
  constructor
  · intro v w
    have e : Matrix.of (fun a b => (v + w) (b, a))
        = Matrix.of (fun a b => v (b, a)) + Matrix.of (fun a b => w (b, a)) := by
      ext a b; simp
    unfold cong
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.vec_add]
  · intro c v
    have e : Matrix.of (fun a b => (c • v) (b, a)) = c • Matrix.of (fun a b => v (b, a)) := by
      ext a b; simp
    unfold cong
    rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.vec_smul]

lemma cong_vec {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℝ) :
    cong M (Matrix.vec Y) = Matrix.vec (M * Y * Mᵀ) := rfl

lemma cong_mat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ, ∀ v, cong M v = L *ᵥ v :=
  ⟨LinearMap.toMatrix' (IsLinearMap.mk' _ (cong_lin M)), fun v => by
    rw [LinearMap.toMatrix'_mulVec, IsLinearMap.mk'_apply]⟩

def Orth {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop := M * Mᵀ = 1 ∧ Mᵀ * M = 1

lemma orth_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (hA : Orth A) (hB : Orth B) :
    Orth (A * B) := by
  constructor
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB.1, Matrix.one_mul, hA.1]
  · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA.2, Matrix.one_mul, hB.2]

lemma orth_pow {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : Orth A) (j : ℕ) : Orth (A ^ j) := by
  induction j with
  | zero => rw [pow_zero]; exact ⟨by simp, by simp⟩
  | succ j ih => rw [pow_succ]; exact orth_mul ih hA

lemma orth_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Orth (σ.permMatrix ℝ) := by
  constructor
  · rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]
  · rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]

lemma pm_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    (σ.permMatrix ℝ) ^ j = (σ ^ j).permMatrix ℝ := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]
  | succ j ih => rw [pow_succ', ih, pow_succ, Matrix.permMatrix_mul]

lemma conj_diag {n : ℕ} (τ : Equiv.Perm (Fin n)) (d : Fin n → ℝ) :
    τ.permMatrix ℝ * Matrix.diagonal d * (τ.permMatrix ℝ)ᵀ = Matrix.diagonal (d ∘ τ) := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Matrix.diagonal_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (τ a)]
  · by_cases hab : a = b
    · subst hab
      simp
    · have : τ b ≠ τ a := fun h => hab (τ.injective h).symm
      simp [hab, this]
  · intro c _ hc
    simp [Ne.symm hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

open Fin.NatCast in
lemma rot_pow (m j : ℕ) (a : Fin (m + 1)) :
    ((finRotate (m + 1)) ^ j) a = a + (j : Fin (m + 1)) := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih, finRotate_succ_apply, Nat.cast_succ]
    abel

open Fin.NatCast in
lemma avg_rot (m : ℕ) (d : Fin (m + 1) → ℝ) (a : Fin (m + 1)) :
    ∑ i : Fin (m + 1), d (((finRotate (m + 1)) ^ ((i : ℕ) + 1)) a) = ∑ c, d c := by
  refine Fintype.sum_equiv (Equiv.addRight (a + 1)) _ _ (fun i => ?_)
  rw [rot_pow]
  show d (a + (((i : ℕ) + 1 : ℕ) : Fin (m + 1))) = d (i + (a + 1))
  rw [Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self]
  congr 1
  abel

end Aux_R6R

open Aux_R6R in
set_option maxHeartbeats 1600000 in
theorem solution (n : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (htr : A.trace = 1)
    (P : Set (Fin n × Fin n → ℝ)) (hP : IsPolytope P)
    (hin : (1 - ε) • PSDPolyApprox.shiftedDensity n A ⊆ P)
    (hout : P ⊆ PSDPolyApprox.shiftedDensity n A)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hdiag : (U * A * Uᵀ).IsDiag) :
    let Q : Set (Fin n × Fin n → ℝ) := (n : ℝ)⁻¹ • ∑ i : Fin n,
      (fun v : Fin n × Fin n → ℝ =>
        Matrix.vec (((finRotate n).permMatrix ℝ ^ ((i : ℕ) + 1) * U) *
          Matrix.of (fun a b => v (b, a)) *
          ((finRotate n).permMatrix ℝ ^ ((i : ℕ) + 1) * U)ᵀ)) '' P
    IsPolytope Q ∧
      (1 - ε) • PSDPolyApprox.shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ Q ∧
      Q ⊆ PSDPolyApprox.shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
      extensionComplexity Q ≤ n * extensionComplexity P := by
  classical
  intro Q
  have hn : n ≠ 0 := by
    rintro rfl
    simp [Matrix.trace] at htr
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hN : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
      Mi = fun i : Fin (m + 1) => (finRotate (m + 1)).permMatrix ℝ ^ ((i : ℕ) + 1) * U :=
    ⟨_, rfl⟩
  have hMi' : ∀ i, Mi i = (finRotate (m + 1)).permMatrix ℝ ^ ((i : ℕ) + 1) * U := by
    intro i
    rw [hMi]
  have hQ : Q = ((m + 1 : ℕ) : ℝ)⁻¹ • ∑ i : Fin (m + 1), cong (Mi i) '' P := by
    subst hMi
    rfl
  rw [hQ]
  have hUo : Orth U := ⟨(Matrix.mem_orthogonalGroup_iff (Fin (m + 1)) ℝ).mp hU,
    (Matrix.mem_orthogonalGroup_iff' (Fin (m + 1)) ℝ).mp hU⟩
  have hMo : ∀ i, Orth (Mi i) := fun i => by
    rw [hMi' i]
    exact orth_mul (orth_pow (orth_perm _) _) hUo
  have havg : ∑ i, Mi i * A * (Mi i)ᵀ = 1 := by
    obtain ⟨d, hd⟩ : ∃ d, U * A * Uᵀ = Matrix.diagonal d := ⟨_, hdiag.diagonal_diag.symm⟩
    have htrd : ∑ c, d c = 1 := by
      have h1 : (U * A * Uᵀ).trace = A.trace := by
        rw [Matrix.trace_mul_cycle, hUo.2, Matrix.one_mul]
      rw [hd, Matrix.trace_diagonal, htr] at h1
      exact h1
    have e : ∀ i : Fin (m + 1), Mi i * A * (Mi i)ᵀ
        = Matrix.diagonal (d ∘ ((finRotate (m + 1)) ^ ((i : ℕ) + 1))) := by
      intro i
      rw [hMi' i, Matrix.transpose_mul, pm_pow, ← conj_diag, ← hd]
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl (fun i _ => e i)]
    ext a b
    rw [Matrix.sum_apply]
    simp only [Matrix.diagonal_apply, Matrix.one_apply, Function.comp_apply]
    by_cases hab : a = b
    · subst hab
      simp only [eq_self_iff_true, if_true]
      rw [avg_rot m d a, htrd]
    · simp only [if_neg hab, Finset.sum_const_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨V, hV⟩ := hP
    have hpi : ∀ i, IsPolytope (cong (Mi i) '' P) := fun i =>
      ⟨V.image (cong (Mi i)), by
        rw [hV, Finset.coe_image, (cong_lin (Mi i)).image_convexHull]⟩
    obtain ⟨W, hW⟩ := polySum _ hpi Finset.univ
    exact ⟨((m + 1 : ℕ) : ℝ)⁻¹ • W, by rw [hW, Finset.coe_smul_finset, convexHull_smul]⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hw
    obtain ⟨Z, ⟨X, hX, rfl⟩, rfl⟩ := hy
    have hX' : X.PosSemidef ∧ X.trace = 1 := hX
    have hXi : ∀ i, (Mi i)ᵀ * X * Mi i ∈ PSDPolyApprox.densityMatrices (m + 1) := by
      intro i
      have h1 := hX'.1.conjTranspose_mul_mul_same (Mi i)
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
      have h2 : ((Mi i)ᵀ * X * Mi i).trace = 1 := by
        rw [Matrix.trace_mul_cycle, (hMo i).1, Matrix.one_mul, hX'.2]
      unfold PSDPolyApprox.densityMatrices
      rw [Set.mem_setOf_eq]
      exact ⟨h1, h2⟩
    have hcX : ∀ i, Mi i * ((Mi i)ᵀ * X * Mi i) * (Mi i)ᵀ = X := by
      intro i
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (hMo i).1, Matrix.one_mul, Matrix.mul_assoc,
        (hMo i).1, Matrix.mul_one]
    refine Set.mem_smul_set.mpr ⟨∑ i, cong (Mi i) ((1 - ε) • Matrix.vec ((Mi i)ᵀ * X * Mi i - A)),
      ?_, ?_⟩
    · rw [Set.mem_fintype_sum]
      refine ⟨fun i => cong (Mi i) ((1 - ε) • Matrix.vec ((Mi i)ᵀ * X * Mi i - A)),
        fun i => Set.mem_image_of_mem _ (hin (Set.smul_mem_smul_set
          (Set.mem_image_of_mem Matrix.vec (Set.mem_image_of_mem (fun Y => Y - A) (hXi i))))), rfl⟩
    · have e1 : ∀ i, cong (Mi i) ((1 - ε) • Matrix.vec ((Mi i)ᵀ * X * Mi i - A))
          = Matrix.vec ((1 - ε) • (X - Mi i * A * (Mi i)ᵀ)) := by
        intro i
        rw [← Matrix.vec_smul, cong_vec, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
          Matrix.sub_mul, hcX]
      simp only [e1]
      rw [← Matrix.vec_sum, ← Matrix.vec_smul, ← Matrix.vec_smul]
      congr 1
      rw [← Finset.smul_sum, Finset.sum_sub_distrib, havg, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_comm]
      congr 1
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hN, one_smul]
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hw
    obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_sum _ _).mp hy
    have hY : ∀ i, ∃ Y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
        (Y.PosSemidef ∧ Y.trace = 1) ∧
          g i = Matrix.vec (Mi i * Y * (Mi i)ᵀ - Mi i * A * (Mi i)ᵀ) := by
      intro i
      obtain ⟨p, hp, hpg⟩ := hg i
      obtain ⟨Z, ⟨Y, hY, hZ⟩, hp'⟩ := hout hp
      refine ⟨Y, hY, ?_⟩
      rw [← hpg, ← hp', ← hZ, cong_vec]
      show Matrix.vec (Mi i * (Y - A) * (Mi i)ᵀ) = _
      rw [Matrix.mul_sub, Matrix.sub_mul]
    choose Y hYD hYg using hY
    have hXD : ((m + 1 : ℕ) : ℝ)⁻¹ • ∑ i, Mi i * Y i * (Mi i)ᵀ
        ∈ PSDPolyApprox.densityMatrices (m + 1) := by
      have h1 : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))), (Mi i * Y i * (Mi i)ᵀ).PosSemidef := by
        intro i _
        have := (hYD i).1.mul_mul_conjTranspose_same (Mi i)
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
      have h2 : ∀ i, (Mi i * Y i * (Mi i)ᵀ).trace = 1 := by
        intro i
        rw [Matrix.trace_mul_cycle, (hMo i).2, Matrix.one_mul, (hYD i).2]
      unfold PSDPolyApprox.densityMatrices
      rw [Set.mem_setOf_eq]
      refine ⟨(Matrix.posSemidef_sum _ h1).smul (by positivity), ?_⟩
      rw [Matrix.trace_smul, Matrix.trace_sum]
      simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hN
    unfold PSDPolyApprox.shiftedDensity
    rw [Set.mem_image]
    refine ⟨((m + 1 : ℕ) : ℝ)⁻¹ • ∑ i, Mi i * Y i * (Mi i)ᵀ
      - ((m + 1 : ℕ) : ℝ)⁻¹ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
      Set.mem_image_of_mem (fun X => X - ((m + 1 : ℕ) : ℝ)⁻¹ • (1 : Matrix _ _ ℝ)) hXD, ?_⟩
    rw [Finset.sum_congr rfl (fun i _ => hYg i), ← Matrix.vec_sum, ← Matrix.vec_smul]
    congr 1
    rw [Finset.sum_sub_distrib, havg, smul_sub]
  · obtain ⟨r0, hr0⟩ := polyEF P hP
    have m0 : IsEFOfSize P (extensionComplexity P) :=
      Nat.sInf_mem (s := {r : ℕ | IsEFOfSize P r}) ⟨r0, hr0⟩
    have h1 : ∀ i, IsEFOfSize (cong (Mi i) '' P) (extensionComplexity P) := by
      intro i
      obtain ⟨L, hL⟩ := cong_mat (Mi i)
      have : cong (Mi i) '' P = (fun v => L *ᵥ v) '' P := by
        congr 1
        funext v
        exact hL v
      rw [this]
      exact imgEF P _ L m0
    have h2 := sumsEF _ _ h1 Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : IsEFOfSize (((m + 1 : ℕ) : ℝ)⁻¹ • ∑ i : Fin (m + 1), cong (Mi i) '' P)
        ((m + 1) * extensionComplexity P) := by
      rw [← Set.image_smul]
      have : (fun x : Fin (m + 1) × Fin (m + 1) → ℝ => ((m + 1 : ℕ) : ℝ)⁻¹ • x)
          = (fun v => (((m + 1 : ℕ) : ℝ)⁻¹ • (1 : Matrix (Fin (m + 1) × Fin (m + 1))
            (Fin (m + 1) × Fin (m + 1)) ℝ)) *ᵥ v) := by
        funext v
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      rw [this]
      exact imgEF _ _ _ h2
    exact Nat.sInf_le h3
