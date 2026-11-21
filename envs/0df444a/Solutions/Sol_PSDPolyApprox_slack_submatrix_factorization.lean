-- Prove2me | solution 1 for PSDPolyApprox.slack_submatrix_factorization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:32:25.306514+00:00
-- url     : https://prove2.me/submissions/2c42fb7f-604b-4c73-a17b-ed366fadb25b

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_PSDPolyApprox_shiftedDensity
import Definitions.Def_PSDPolyApprox_slackSubmatrix

open ExtensionComplexity.TSP
open scoped Pointwise Matrix

namespace Aux_R6S


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


section Cone

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [Fintype W]

def LI (g : ι → (W → ℝ)) (T : Finset ι) : Prop :=
  ∀ f : ι → ℝ, ∑ i ∈ T, f i • g i = 0 → ∀ i ∈ T, f i = 0

theorem carath (g : ι → (W → ℝ)) : ∀ (K : ℕ) (lam : ι → ℝ), (∀ i, 0 ≤ lam i) →
    (Finset.univ.filter (fun i => lam i ≠ 0)).card ≤ K →
    ∃ T : Finset ι, LI g T ∧ ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧
      ∑ i, μ i • g i = ∑ i, lam i • g i := by
  intro K
  induction K with
  | zero =>
    intro lam hlam hcard
    refine ⟨∅, fun f _ i hi => absurd hi (Finset.notMem_empty i), lam, hlam, ?_, rfl⟩
    intro i _
    by_contra h
    have hi : i ∈ Finset.univ.filter (fun i => lam i ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  | succ K ih =>
    intro lam hlam hcard
    obtain ⟨S, hS⟩ : ∃ S : Finset ι, S = Finset.univ.filter (fun i => lam i ≠ 0) := ⟨_, rfl⟩
    have memS : ∀ i, i ∈ S ↔ lam i ≠ 0 := by intro i; rw [hS]; simp
    rw [← hS] at hcard
    by_cases hLI : LI g S
    · refine ⟨S, hLI, lam, hlam, fun i hi => ?_, rfl⟩
      by_contra h
      exact hi ((memS i).mpr h)
    · unfold LI at hLI
      push_neg at hLI
      obtain ⟨f, hf, i₀, hi₀S, hfi₀⟩ := hLI
      have hc : ∑ i, (if i ∈ S then f i else 0) • g i = 0 := by
        calc ∑ i, (if i ∈ S then f i else 0) • g i
            = ∑ i ∈ S, (if i ∈ S then f i else 0) • g i :=
              Eq.symm (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by simp [hi]))
          _ = ∑ i ∈ S, f i • g i := Finset.sum_congr rfl (fun i hi => by simp [hi])
          _ = 0 := hf
      obtain ⟨d, hd0, hdS, hdi₀⟩ : ∃ d : ι → ℝ, ∑ i, d i • g i = 0 ∧
          (∀ i, i ∉ S → d i = 0) ∧ 0 < d i₀ := by
        rcases lt_or_gt_of_ne hfi₀ with hneg | hpos
        · refine ⟨fun i => -(if i ∈ S then f i else 0), ?_, ?_, ?_⟩
          · simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; linarith
        · refine ⟨fun i => if i ∈ S then f i else 0, hc, ?_, ?_⟩
          · intro i hi; simp [hi]
          · simp only [if_pos hi₀S]; exact hpos
      have hdpos : ∀ i, 0 < d i → i ∈ S := by
        intro i hi
        by_contra h
        rw [hdS i h] at hi
        exact lt_irrefl _ hi
      obtain ⟨P, hP⟩ : ∃ P : Finset ι, P = Finset.univ.filter (fun i => 0 < d i) := ⟨_, rfl⟩
      have memP : ∀ i, i ∈ P ↔ 0 < d i := by intro i; rw [hP]; simp
      have hPne : P.Nonempty := ⟨i₀, (memP i₀).mpr hdi₀⟩
      obtain ⟨i₁, hi₁P, hmin⟩ := Finset.exists_min_image P (fun i => lam i / d i) hPne
      have hd1 : 0 < d i₁ := (memP i₁).mp hi₁P
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = lam i₁ / d i₁ := ⟨_, rfl⟩
      have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (hlam i₁) hd1.le
      have hlam' : ∀ i, 0 ≤ lam i - t * d i := by
        intro i
        by_cases hdi : 0 < d i
        · have h1 : t ≤ lam i / d i := by rw [ht]; exact hmin i ((memP i).mpr hdi)
          rw [le_div_iff₀ hdi] at h1
          linarith
        · push_neg at hdi
          nlinarith [hlam i, ht0, hdi]
      have hzero : lam i₁ - t * d i₁ = 0 := by
        rw [ht, div_mul_cancel₀ _ hd1.ne', sub_self]
      have hsupp : Finset.univ.filter (fun i => lam i - t * d i ≠ 0) ⊆ S.erase i₁ := by
        intro i hi
        rw [Finset.mem_filter] at hi
        rw [Finset.mem_erase]
        refine ⟨fun h => hi.2 (by rw [h]; exact hzero), ?_⟩
        by_contra hiS
        apply hi.2
        rw [hdS i hiS]
        have : lam i = 0 := by
          by_contra h'
          exact hiS ((memS i).mpr h')
        rw [this]
        ring
      have hcard' : (Finset.univ.filter (fun i => lam i - t * d i ≠ 0)).card ≤ K := by
        have h1 := Finset.card_le_card hsupp
        have h2 := Finset.card_erase_of_mem (hdpos i₁ hd1)
        omega
      obtain ⟨T, hT, μ, hμ0, hμT, hμsum⟩ := ih (fun i => lam i - t * d i) hlam' hcard'
      refine ⟨T, hT, μ, hμ0, hμT, ?_⟩
      have hsplit : ∑ i, (lam i - t * d i) • g i = ∑ i, lam i • g i - t • ∑ i, d i • g i := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_smul, mul_smul]
      rw [hμsum, hsplit, hd0, smul_zero, sub_zero]

def coneOf (g : ι → (W → ℝ)) : Set (W → ℝ) :=
  {x | ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x}

theorem mem_coneOf (g : ι → (W → ℝ)) (x : W → ℝ) :
    x ∈ coneOf g ↔ ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i • g i = x := Iff.rfl

def coneT (g : ι → (W → ℝ)) (T : Finset ι) : Set (W → ℝ) :=
  {x | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x}

theorem mem_coneT (g : ι → (W → ℝ)) (T : Finset ι) (x : W → ℝ) :
    x ∈ coneT g T ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i, i ∉ T → μ i = 0) ∧ ∑ i, μ i • g i = x := Iff.rfl

theorem sum_ext_T (g : ι → (W → ℝ)) (T : Finset ι) (μ : T → ℝ) :
    ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = ∑ i : T, μ i • g i := by
  have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
      ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
    Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
  rw [← h1, ← Finset.sum_coe_sort T]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.2]

theorem sum_restrict_T (g : ι → (W → ℝ)) (T : Finset ι) (μ : ι → ℝ)
    (hμT : ∀ i, i ∉ T → μ i = 0) :
    ∑ i : T, μ i • g i = ∑ i, μ i • g i := by
  have h1 : ∑ i : T, μ i • g i = ∑ i ∈ T, μ i • g i := Finset.sum_coe_sort T (fun i => μ i • g i)
  rw [h1]
  exact Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [hμT i hi, zero_smul])

theorem coneT_closed (g : ι → (W → ℝ)) (T : Finset ι) (hT : LI g T) :
    IsClosed (coneT g T) := by
  let L : (T → ℝ) →ₗ[ℝ] (W → ℝ) := Fintype.linearCombination ℝ (fun i : T => g i)
  have hL : ∀ μ : T → ℝ, L μ = ∑ i : T, μ i • g i := fun μ => rfl
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro μ hμ
    rw [hL] at hμ
    have h1 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i = 0 := by
      have h3 : ∑ i ∈ T, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i =
          ∑ i, (if h : i ∈ T then μ ⟨i, h⟩ else 0) • g i :=
        Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => by rw [dif_neg hi, zero_smul])
      rw [h3, sum_ext_T]
      exact hμ
    have h2 := hT _ h1
    funext i
    have := h2 i i.2
    rw [dif_pos i.2] at this
    exact this
  have hA : IsClosed {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))
  have heq : coneT g T = L '' {μ : T → ℝ | ∀ i, 0 ≤ μ i} := by
    ext x
    rw [mem_coneT]
    constructor
    · rintro ⟨μ, hμ0, hμT, rfl⟩
      refine ⟨fun i => μ i, fun i => hμ0 i, ?_⟩
      rw [hL]
      exact sum_restrict_T g T μ hμT
    · rintro ⟨μ, hμ0, rfl⟩
      refine ⟨fun i => if h : i ∈ T then μ ⟨i, h⟩ else 0, ?_, ?_, ?_⟩
      · intro i
        show 0 ≤ (if h : i ∈ T then μ ⟨i, h⟩ else 0)
        by_cases h : i ∈ T
        · rw [dif_pos h]; exact hμ0 _
        · rw [dif_neg h]
      · intro i hi
        show (if h : i ∈ T then μ ⟨i, h⟩ else 0) = 0
        rw [dif_neg hi]
      · rw [hL]
        exact sum_ext_T g T μ
  rw [heq]
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosedMap _ hA

theorem cone_closed (g : ι → (W → ℝ)) : IsClosed (coneOf g) := by
  have heq : coneOf g = ⋃ (T : Finset ι), ⋃ (_ : LI g T), coneT g T := by
    ext x
    rw [mem_coneOf, Set.mem_iUnion₂]
    constructor
    · rintro ⟨lam, hlam, rfl⟩
      obtain ⟨T, hT, μ, hμ0, hμT, hμ⟩ :=
        carath g (Finset.univ.filter (fun i => lam i ≠ 0)).card lam hlam le_rfl
      exact ⟨T, hT, (mem_coneT g T _).mpr ⟨μ, hμ0, hμT, hμ⟩⟩
    · rintro ⟨T, _, hx⟩
      obtain ⟨μ, hμ0, _, hμ⟩ := (mem_coneT g T x).mp hx
      exact ⟨μ, hμ0, hμ⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun T => isClosed_iUnion_of_finite (fun hT => coneT_closed g T hT))

end Cone


/-! ### Affine Farkas lemma -/

section Farkas

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coneOf_convex {ι W : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] (g : ι → (W → ℝ)) :
    Convex ℝ (coneOf g) := by
  intro x hx y hy a b ha hb _
  obtain ⟨l1, hl1, rfl⟩ := (mem_coneOf g x).mp hx
  obtain ⟨l2, hl2, rfl⟩ := (mem_coneOf g y).mp hy
  refine (mem_coneOf g _).mpr ⟨fun i => a * l1 i + b * l2 i,
    fun i => add_nonneg (mul_nonneg ha (hl1 i)) (mul_nonneg hb (hl2 i)), ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_smul, mul_smul, mul_smul]

/-- generators of the homogenised cone. -/
def g1 {p : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (j : Fin p) : Option V → ℝ :=
  fun o => Option.elim o (h j) (G j)

def g3 {r : ℕ} (K : Fin r → V → ℝ) (e : Fin r → ℝ) (l : Fin r) : Option V → ℝ :=
  fun o => Option.elim o (e l) (K l)

def g4 : Option V → ℝ := fun o => Option.elim o 1 (fun _ => 0)

def gens {p r : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (K : Fin r → V → ℝ) (e : Fin r → ℝ) :
    ((Fin p ⊕ Fin p) ⊕ (Fin r ⊕ Unit)) → (Option V → ℝ) :=
  Sum.elim (Sum.elim (g1 G h) (fun j => -(g1 G h j))) (Sum.elim (g3 K e) (fun _ => g4))

lemma farkas {p r : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (K : Fin r → V → ℝ)
    (e : Fin r → ℝ) (a : V → ℝ) (β : ℝ)
    (hne : ∃ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) ∧ (∀ l, ∑ v, K l v * z v ≤ e l))
    (hval : ∀ z : V → ℝ, (∀ j, ∑ v, G j v * z v = h j) → (∀ l, ∑ v, K l v * z v ≤ e l) →
      ∑ v, a v * z v ≤ β) :
    ∃ (μ : Fin p → ℝ) (lam : Fin r → ℝ), (∀ l, 0 ≤ lam l) ∧
      (∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v) ∧
      ∑ j, μ j * h j + ∑ l, lam l * e l ≤ β := by
  classical
  have hmem : (fun o => Option.elim o β a) ∈ coneOf (gens G h K e) := by
    by_contra hnot
    obtain ⟨f, u, hfu, hut⟩ :=
      geometric_hahn_banach_closed_point (coneOf_convex _) (cone_closed _) hnot
    have h0mem : (0 : Option V → ℝ) ∈ coneOf (gens G h K e) :=
      (mem_coneOf _ 0).mpr ⟨0, fun _ => le_rfl, by simp⟩
    have hu : 0 < u := by
      have := hfu 0 h0mem
      simpa using this
    have hg : ∀ i, f (gens G h K e i) ≤ 0 := by
      intro i
      by_contra hneg
      push_neg at hneg
      have hm : (u / f (gens G h K e i)) • gens G h K e i ∈ coneOf (gens G h K e) := by
        refine (mem_coneOf _ _).mpr ⟨fun j => if j = i then u / f (gens G h K e i) else 0,
          fun j => ?_, ?_⟩
        · show 0 ≤ (if j = i then u / f (gens G h K e i) else 0)
          by_cases hj : j = i
          · rw [if_pos hj]; exact le_of_lt (div_pos hu hneg)
          · rw [if_neg hj]
        · simp [ite_smul]
      have := hfu _ hm
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne'] at this
      exact lt_irrefl _ this
    have hfx : ∀ w : Option V → ℝ, f w = ∑ o, w o * f (fun j => if o = j then (1 : ℝ) else 0) := by
      intro w
      conv_lhs => rw [pi_eq_sum_univ w]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [map_smul, smul_eq_mul]
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = f (fun j => if (none : Option V) = j then (1 : ℝ) else 0) :=
      ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : V → ℝ, y = fun v => f (fun j => if (some v : Option V) = j then (1 : ℝ) else 0) :=
      ⟨_, rfl⟩
    have hf' : ∀ w : Option V → ℝ, f w = w none * t + ∑ v, w (some v) * y v := by
      intro w
      rw [hfx, Fintype.sum_option, ht, hy]
    have hunit := hg (Sum.inr (Sum.inr ()))
    simp only [gens, Sum.elim_inr, hf', g4, Option.elim_none, Option.elim_some, one_mul,
      zero_mul, Finset.sum_const_zero, add_zero] at hunit
    have heq : ∀ j, h j * t + ∑ v, G j v * y v = 0 := by
      intro j
      have h1 := hg (Sum.inl (Sum.inl j))
      have h2 := hg (Sum.inl (Sum.inr j))
      simp only [gens, Sum.elim_inl, Sum.elim_inr, map_neg, hf', g1, Option.elim_none,
        Option.elim_some,
        Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at h1 h2
      linarith
    have hineq : ∀ l, e l * t + ∑ v, K l v * y v ≤ 0 := by
      intro l
      have h1 := hg (Sum.inr (Sum.inl l))
      simp only [gens, Sum.elim_inr, Sum.elim_inl, hf', g3, Option.elim_none,
        Option.elim_some] at h1
      exact h1
    have htop : u < β * t + ∑ v, a v * y v := by
      have := hut
      simp only [hf', Option.elim_none, Option.elim_some] at this
      exact this
    rcases lt_or_eq_of_le hunit with htn | htz
    · have htp : 0 < -t := by linarith
      have hz : ∑ v, a v * (y v / -t) ≤ β := hval (fun v => y v / (-t)) (fun j => by
          show ∑ v, G j v * (y v / -t) = h j
          have := heq j
          rw [show ∑ v, G j v * (y v / -t) = (∑ v, G j v * y v) / (-t) by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring)]
          rw [div_eq_iff htp.ne']
          linarith)
        (fun l => by
          show ∑ v, K l v * (y v / -t) ≤ e l
          have := hineq l
          rw [show ∑ v, K l v * (y v / -t) = (∑ v, K l v * y v) / (-t) by
            rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring)]
          rw [div_le_iff₀ htp]
          linarith)
      rw [show ∑ v, a v * (y v / -t) = (∑ v, a v * y v) / (-t) by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun v _ => by ring),
        div_le_iff₀ htp] at hz
      nlinarith
    · rw [htz] at heq hineq htop
      simp only [mul_zero, zero_add] at heq hineq htop
      obtain ⟨z0, hz0e, hz0l⟩ := hne
      have hv0 := hval z0 hz0e hz0l
      have hay : 0 < ∑ v, a v * y v := by linarith
      obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (β - ∑ v, a v * z0 v + 1) / ∑ v, a v * y v := ⟨_, rfl⟩
      have hs0 : 0 ≤ s := by
        rw [hs]
        apply div_nonneg _ hay.le
        linarith
      have hsplit : ∀ c : V → ℝ, ∑ v, c v * (z0 v + s * y v)
          = ∑ v, c v * z0 v + s * ∑ v, c v * y v := by
        intro c
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun v _ => by ring)
      have hz : ∑ v, a v * (z0 v + s * y v) ≤ β := hval (fun v => z0 v + s * y v)
        (fun j => by
          show ∑ v, G j v * (z0 v + s * y v) = h j
          rw [hsplit, hz0e j, heq j, mul_zero, add_zero])
        (fun l => by
          show ∑ v, K l v * (z0 v + s * y v) ≤ e l
          rw [hsplit]
          have := hineq l
          have := hz0l l
          nlinarith)
      rw [hsplit] at hz
      have hsa : s * ∑ v, a v * y v = β - ∑ v, a v * z0 v + 1 := by
        rw [hs, div_mul_cancel₀ _ hay.ne']
      linarith
  obtain ⟨lam, hlam, hsum⟩ := (mem_coneOf _ _).mp hmem
  refine ⟨fun j => lam (Sum.inl (Sum.inl j)) - lam (Sum.inl (Sum.inr j)),
    fun l => lam (Sum.inr (Sum.inl l)), fun l => hlam _, ?_, ?_⟩
  · intro v
    have := congrFun hsum (some v)
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, gens, Sum.elim_inl,
      Sum.elim_inr, g1, g3, g4, Pi.neg_apply, Option.elim_some, Fintype.sum_unique,
      mul_zero, add_zero] at this
    rw [← this]
    simp only [sub_mul, Finset.sum_sub_distrib, mul_neg, Finset.sum_neg_distrib]
    ring
  · have := congrFun hsum none
    rw [Finset.sum_apply] at this
    simp only [Pi.smul_apply, smul_eq_mul, Fintype.sum_sum_type, gens, Sum.elim_inl,
      Sum.elim_inr, g1, g3, g4, Pi.neg_apply, Option.elim_none, Fintype.sum_unique,
      mul_one] at this
    have hl4 := hlam (Sum.inr (Sum.inr default))
    have e1 : ∑ j, (lam (Sum.inl (Sum.inl j)) - lam (Sum.inl (Sum.inr j))) * h j
        = ∑ j, lam (Sum.inl (Sum.inl j)) * h j + ∑ j, lam (Sum.inl (Sum.inr j)) * -h j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [e1]
    linarith

/-- the slack identity coming from a Farkas certificate. -/
lemma farkas_slack {p r : ℕ} (G : Fin p → V → ℝ) (h : Fin p → ℝ) (K : Fin r → V → ℝ)
    (e : Fin r → ℝ) (a : V → ℝ) (μ : Fin p → ℝ) (lam : Fin r → ℝ)
    (ha : ∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v)
    (z : V → ℝ) (hz : ∀ j, ∑ v, G j v * z v = h j) :
    ∑ v, a v * z v = ∑ j, μ j * h j + ∑ l, lam l * ∑ v, K l v * z v := by
  simp only [ha, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hz j, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => by ring)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => by ring)

end Farkas


/-! ### Density-matrix computations -/

lemma cdot (n : ℕ) (hnR : (n : ℝ) ≠ 0) (Z : Matrix (Fin n) (Fin n) ℝ) (htr : Z.trace = 1)
    (y : Fin n → ℝ) (hy : ∀ i, y i * y i = 1) :
    ∑ ij : Fin n × Fin n, ((if ij.1 = ij.2 then (1 : ℝ) else 0) - y ij.1 * y ij.2)
        * Matrix.vec (Z - (n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ij
      = 1 - ∑ i, ∑ j, y i * Z i j * y j := by
  rw [Fintype.sum_prod_type]
  simp only [Matrix.vec, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have e : ∀ a b : Fin n, ((if a = b then (1 : ℝ) else 0) - y a * y b)
      * (Z b a - (n : ℝ)⁻¹ * (if b = a then (1 : ℝ) else 0))
      = (if a = b then Z a a else 0) - (if a = b then (n : ℝ)⁻¹ else 0) - y a * Z b a * y b
        + (if a = b then (n : ℝ)⁻¹ * (y a * y a) else 0) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp only [if_true, eq_self_iff_true]
      ring
    · simp only [if_neg h, if_neg (Ne.symm h)]
      ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, hy, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have htr' : ∑ a, Z a a = 1 := htr
  have hq : ∑ a, ∑ b, y a * Z b a * y b = ∑ i, ∑ j, y i * Z i j * y j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  rw [htr', hq, mul_inv_cancel₀ hnR]
  ring

lemma qnn (n : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef) (y : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * Z i j * y j := by
  have h := hZ.dotProduct_mulVec_nonneg y
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum] at h
  refine le_of_le_of_eq h ?_
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma unit_sq (u : ℤˣ) : ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
  have h : (u : ℤ) * (u : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  exact_mod_cast h

/-- the rank-one density `xxᵀ/n`. -/
noncomputable def Zx (n : ℕ) (x : Fin n → ℤˣ) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ)⁻¹ • Matrix.vecMulVec (fun i => ((x i : ℤ) : ℝ)) (fun i => ((x i : ℤ) : ℝ))

lemma Zx_psd (n : ℕ) (x : Fin n → ℤˣ) : (Zx n x).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (fun i => ((x i : ℤ) : ℝ))
  rw [star_trivial] at h
  exact h.smul (by positivity)

lemma Zx_trace (n : ℕ) (hnR : (n : ℝ) ≠ 0) (x : Fin n → ℤˣ) : (Zx n x).trace = 1 := by
  unfold Zx
  rw [Matrix.trace_smul]
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, unit_sq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact inv_mul_cancel₀ hnR

lemma Zx_quad (n : ℕ) (x y : Fin n → ℤˣ) :
    ∑ i, ∑ j, ((y i : ℤ) : ℝ) * Zx n x i j * ((y j : ℤ) : ℝ)
      = (n : ℝ)⁻¹ * (∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2 := by
  unfold Zx
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma liftA_dot {n k : ℕ} (c : Fin n × Fin n → ℝ) (z : (Fin n × Fin n) ⊕ Fin k → ℝ) :
    ∑ v, (Sum.elim c (fun _ => (0 : ℝ)) v) * z v = ∑ x, c x * (z ∘ Sum.inl) x := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero,
    Function.comp_apply]

end Aux_R6S

open Aux_R6S in
set_option maxHeartbeats 1600000 in
theorem solution (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Q : Set (Fin n × Fin n → ℝ)) (hQ : IsPolytope Q)
    (hin : (1 - ε) • PSDPolyApprox.shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ⊆ Q)
    (hout : Q ⊆ PSDPolyApprox.shiftedDensity n ((n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    HasNonnegFactorization (PSDPolyApprox.slackSubmatrix ε n) (extensionComplexity Q) := by
  classical
  have hn0 : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have h1ε : 0 < 1 - ε := by linarith
  obtain ⟨r0, hr0⟩ := polyEF Q hQ
  have hEFr : IsEFOfSize Q (extensionComplexity Q) :=
    Nat.sInf_mem (s := {r : ℕ | IsEFOfSize Q r}) ⟨r0, hr0⟩
  generalize extensionComplexity Q = r at hEFr ⊢
  obtain ⟨k, p, Ee, Fe, ge, El, Fl, gl, hEF⟩ := hEFr
  obtain ⟨G, hG⟩ : ∃ G : Fin p → ((Fin n × Fin n) ⊕ Fin k) → ℝ,
      G = fun j => Sum.elim (fun x => Ee j x) (fun w => Fe j w) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Fin r → ((Fin n × Fin n) ⊕ Fin k) → ℝ,
      K = fun l => Sum.elim (fun x => El l x) (fun w => Fl l w) := ⟨_, rfl⟩
  have hGz : ∀ (z : (Fin n × Fin n) ⊕ Fin k → ℝ) j,
      ∑ v, G j v * z v = (Ee *ᵥ (z ∘ Sum.inl) + Fe *ᵥ (z ∘ Sum.inr)) j := by
    intro z j
    rw [hG, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct,
      Function.comp_apply]
  have hKz : ∀ (z : (Fin n × Fin n) ⊕ Fin k → ℝ) l,
      ∑ v, K l v * z v = (El *ᵥ (z ∘ Sum.inl) + Fl *ᵥ (z ∘ Sum.inr)) l := by
    intro z l
    rw [hK, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct,
      Function.comp_apply]
  have hLQ : ∀ z : (Fin n × Fin n) ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) →
      (∀ l, ∑ v, K l v * z v ≤ gl l) → z ∘ Sum.inl ∈ Q := by
    intro z h1 h2
    refine (hEF _).mpr ⟨z ∘ Sum.inr, funext fun j => ?_, fun l => ?_⟩
    · rw [← hGz]; exact h1 j
    · rw [← hKz]; exact h2 l
  have hQL : ∀ x ∈ Q, ∃ z : (Fin n × Fin n) ⊕ Fin k → ℝ, ((∀ j, ∑ v, G j v * z v = ge j) ∧
      (∀ l, ∑ v, K l v * z v ≤ gl l)) ∧ z ∘ Sum.inl = x := by
    intro x hx
    obtain ⟨w, h1, h2⟩ := (hEF x).mp hx
    refine ⟨Sum.elim x w, ⟨fun j => ?_, fun l => ?_⟩, Sum.elim_comp_inl x w⟩
    · rw [hGz, Sum.elim_comp_inl, Sum.elim_comp_inr, h1]
    · rw [hKz, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact h2 l
  have hdens : ∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef → Z.trace = 1 →
      (1 - ε) • Matrix.vec (Z - (n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ∈ Q := by
    intro Z h1 h2
    have hZ : Z ∈ PSDPolyApprox.densityMatrices n := by
      unfold PSDPolyApprox.densityMatrices
      rw [Set.mem_setOf_eq]
      exact ⟨h1, h2⟩
    exact hin (Set.smul_mem_smul_set (Set.mem_image_of_mem Matrix.vec
      (Set.mem_image_of_mem (fun X => X - (n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) hZ)))
  have hQin : ∀ x ∈ Q, ∃ Z : Matrix (Fin n) (Fin n) ℝ, (Z.PosSemidef ∧ Z.trace = 1) ∧
      x = Matrix.vec (Z - (n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    intro x hx
    obtain ⟨W, ⟨Z, hZ, hZW⟩, hWx⟩ := hout hx
    refine ⟨Z, hZ, ?_⟩
    rw [← hWx, ← hZW]
  -- rows
  obtain ⟨pt, hpt⟩ : ∃ pt : (Fin n → ℤˣ) → (Fin n × Fin n → ℝ),
      pt = fun x => (1 - ε) • Matrix.vec (Zx n x - (n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    ⟨_, rfl⟩
  have hptQ : ∀ x, pt x ∈ Q := by
    intro x
    rw [hpt]
    exact hdens _ (Zx_psd n x) (Zx_trace n hnR x)
  -- columns: the valid inequalities
  obtain ⟨cy, hcy⟩ : ∃ cy : (Fin n → ℤˣ) → (Fin n × Fin n → ℝ),
      cy = fun y ij => (if ij.1 = ij.2 then (1 : ℝ) else 0)
        - ((y ij.1 : ℤ) : ℝ) * ((y ij.2 : ℤ) : ℝ) := ⟨_, rfl⟩
  have hcyval : ∀ y, ∀ x ∈ Q, ∑ ij, cy y ij * x ij ≤ 1 := by
    intro y x hx
    obtain ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩ := hQin x hx
    simp only [hcy]
    rw [cdot n hnR Z hZ2 (fun i => ((y i : ℤ) : ℝ)) (fun i => unit_sq (y i))]
    have := qnn n Z hZ1 (fun i => ((y i : ℤ) : ℝ))
    linarith
  have hcypt : ∀ x y, ∑ ij, cy y ij * pt x ij
      = (1 - ε) * (1 - (n : ℝ)⁻¹ * (∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) ^ 2) := by
    intro x y
    have e : ∑ ij, cy y ij * pt x ij = (1 - ε) * ∑ ij, cy y ij *
        Matrix.vec (Zx n x - (n : ℝ)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ)) ij := by
      rw [hpt, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ij _ => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    simp only [hcy]
    rw [cdot n hnR _ (Zx_trace n hnR x) (fun i => ((y i : ℤ) : ℝ)) (fun i => unit_sq (y i)),
      Zx_quad]
  -- nonemptiness of the lifted system
  obtain ⟨x1⟩ : Nonempty (Fin n → ℤˣ) := inferInstance
  obtain ⟨z1, hz1L, _⟩ := hQL _ (hptQ x1)
  have hne : ∃ z : (Fin n × Fin n) ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) ∧
      (∀ l, ∑ v, K l v * z v ≤ gl l) := ⟨z1, hz1L⟩
  -- Farkas certificates for the columns
  have hcolF : ∀ y : Fin n → ℤˣ, ∃ (μ : Fin p → ℝ) (lam : Fin r → ℝ), (∀ l, 0 ≤ lam l) ∧
      (∀ v, Sum.elim (cy y) (fun _ => (0 : ℝ)) v = ∑ j, μ j * G j v + ∑ l, lam l * K l v) ∧
      ∑ j, μ j * ge j + ∑ l, lam l * gl l ≤ 1 := by
    intro y
    refine farkas G ge K gl (Sum.elim (cy y) (fun _ => (0 : ℝ))) 1 hne ?_
    intro z h1 h2
    rw [liftA_dot]
    exact hcyval y _ (hLQ z h1 h2)
  choose μY lamY hlamY haY hβY using hcolF
  -- the constant: a coordinate functional, maximised and minimised on Q
  obtain ⟨V0, hV0⟩ := hQ
  obtain ⟨c0, hc0⟩ : ∃ c0 : Fin n × Fin n, c0 = (⟨0, hn0⟩, ⟨1, by omega⟩) := ⟨_, rfl⟩
  have hlin : IsLinearMap ℝ (fun x : Fin n × Fin n → ℝ => x c0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hV0ne : V0.Nonempty := by
    rcases V0.eq_empty_or_nonempty with h | h
    · have := hptQ x1
      rw [hV0, h, Finset.coe_empty, convexHull_empty] at this
      exact absurd this (Set.notMem_empty _)
    · exact h
  obtain ⟨vmax, hvmaxV, hvmax⟩ := Finset.exists_max_image V0 (fun x => x c0) hV0ne
  obtain ⟨vmin, hvminV, hvmin⟩ := Finset.exists_min_image V0 (fun x => x c0) hV0ne
  have hmaxQ : ∀ x ∈ Q, x c0 ≤ vmax c0 := by
    intro x hx
    rw [hV0] at hx
    exact convexHull_min (fun v hv => show v ∈ {w : Fin n × Fin n → ℝ | w c0 ≤ vmax c0} from
      hvmax v hv) (convex_halfSpace_le hlin _) hx
  have hminQ : ∀ x ∈ Q, vmin c0 ≤ x c0 := by
    intro x hx
    rw [hV0] at hx
    exact convexHull_min (fun v hv => show v ∈ {w : Fin n × Fin n → ℝ | vmin c0 ≤ w c0} from
      hvmin v hv) (convex_halfSpace_ge hlin _) hx
  have hvmaxQ : vmax ∈ Q := by rw [hV0]; exact subset_convexHull ℝ _ hvmaxV
  have hvminQ : vmin ∈ Q := by rw [hV0]; exact subset_convexHull ℝ _ hvminV
  -- two cube points with different coordinate c0
  obtain ⟨xa, hxa⟩ : ∃ xa : Fin n → ℤˣ, xa = fun _ => 1 := ⟨_, rfl⟩
  obtain ⟨xb, hxb⟩ : ∃ xb : Fin n → ℤˣ, xb = Function.update (fun _ => 1) ⟨1, by omega⟩ (-1) :=
    ⟨_, rfl⟩
  have hpta : pt xa c0 = (1 - ε) * (n : ℝ)⁻¹ := by
    rw [hpt, hc0, hxa]
    simp [Zx, Matrix.vecMulVec_apply, Matrix.one_apply] <;> ring
  have hptb : pt xb c0 = -((1 - ε) * (n : ℝ)⁻¹) := by
    rw [hpt, hc0, hxb]
    simp [Zx, Matrix.vecMulVec_apply, Matrix.one_apply, Function.update_apply, Fin.ext_iff] <;> ring
  have hD : 0 < vmax c0 - vmin c0 := by
    have h1 := hmaxQ _ (hptQ xa)
    have h2 := hminQ _ (hptQ xb)
    rw [hpta] at h1
    rw [hptb] at h2
    have : 0 < (1 - ε) * (n : ℝ)⁻¹ := by positivity
    linarith
  -- Farkas for the max and the min
  obtain ⟨μ1, lam1, hlam1, ha1, hβ1⟩ := farkas G ge K gl
    (Sum.elim (fun x => if x = c0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ))) (vmax c0) hne
    (fun z h1 h2 => by
      rw [liftA_dot]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hmaxQ _ (hLQ z h1 h2))
  obtain ⟨μ2, lam2, hlam2, ha2, hβ2⟩ := farkas G ge K gl
    (Sum.elim (fun x => if x = c0 then (-1 : ℝ) else 0) (fun _ => (0 : ℝ))) (-vmin c0) hne
    (fun z h1 h2 => by
      rw [liftA_dot]
      simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have := hminQ _ (hLQ z h1 h2)
      simp only [Function.comp_apply] at this ⊢
      linarith)
  -- slack identities
  have hsl : ∀ (a : (Fin n × Fin n) ⊕ Fin k → ℝ) (μ : Fin p → ℝ) (lam : Fin r → ℝ),
      (∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * K l v) →
      ∀ z : (Fin n × Fin n) ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) →
      ∑ v, a v * z v = ∑ j, μ j * ge j + ∑ l, lam l * gl l
        - ∑ l, lam l * (gl l - ∑ v, K l v * z v) := by
    intro a μ lam ha z hz
    rw [farkas_slack G ge K gl a μ lam ha z hz]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hslnn : ∀ (lam : Fin r → ℝ), (∀ l, 0 ≤ lam l) →
      ∀ z : (Fin n × Fin n) ⊕ Fin k → ℝ, (∀ l, ∑ v, K l v * z v ≤ gl l) →
      0 ≤ ∑ l, lam l * (gl l - ∑ v, K l v * z v) := by
    intro lam hlam z hz
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hlam l) (by linarith [hz l]))
  have hdot1 : ∀ z : (Fin n × Fin n) ⊕ Fin k → ℝ,
      ∑ v, Sum.elim (fun x => if x = c0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ)) v * z v
        = z (Sum.inl c0) := by
    intro z
    rw [liftA_dot]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Function.comp_apply]
  have hdot2 : ∀ z : (Fin n × Fin n) ⊕ Fin k → ℝ,
      ∑ v, Sum.elim (fun x => if x = c0 then (-1 : ℝ) else 0) (fun _ => (0 : ℝ)) v * z v
        = -z (Sum.inl c0) := by
    intro z
    rw [liftA_dot]
    simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Function.comp_apply]
  obtain ⟨zmax, hzmaxL, hzmaxp⟩ := hQL _ hvmaxQ
  obtain ⟨zmin, hzminL, hzminp⟩ := hQL _ hvminQ
  have hδ1 : ∑ j, μ1 j * ge j + ∑ l, lam1 l * gl l = vmax c0 := by
    have e := hsl _ μ1 lam1 ha1 zmax hzmaxL.1
    rw [hdot1] at e
    have hz : zmax (Sum.inl c0) = vmax c0 := congrFun hzmaxp c0
    have := hslnn lam1 hlam1 zmax hzmaxL.2
    linarith
  have hδ2 : ∑ j, μ2 j * ge j + ∑ l, lam2 l * gl l = -vmin c0 := by
    have e := hsl _ μ2 lam2 ha2 zmin hzminL.1
    rw [hdot2] at e
    have hz : zmin (Sum.inl c0) = vmin c0 := congrFun hzminp c0
    have := hslnn lam2 hlam2 zmin hzminL.2
    linarith
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = vmax c0 - vmin c0 := ⟨_, rfl⟩
  have hα : ∀ z : (Fin n × Fin n) ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) →
      ∑ l, ((lam1 l + lam2 l) / D) * (gl l - ∑ v, K l v * z v) = 1 := by
    intro z hz
    have e1 := hsl _ μ1 lam1 ha1 z hz
    have e2 := hsl _ μ2 lam2 ha2 z hz
    rw [hdot1, hδ1] at e1
    rw [hdot2, hδ2] at e2
    have hsum : ∑ l, ((lam1 l + lam2 l) / D) * (gl l - ∑ v, K l v * z v)
        = (∑ l, lam1 l * (gl l - ∑ v, K l v * z v) + ∑ l, lam2 l * (gl l - ∑ v, K l v * z v)) / D := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [hsum, div_eq_one_iff_eq (by rw [hDdef]; exact hD.ne')]
    rw [hDdef]
    linarith
  -- rows: lifts
  have hrow : ∀ x : Fin n → ℤˣ, ∃ z : (Fin n × Fin n) ⊕ Fin k → ℝ,
      ((∀ j, ∑ v, G j v * z v = ge j) ∧ (∀ l, ∑ v, K l v * z v ≤ gl l)) ∧ z ∘ Sum.inl = pt x :=
    fun x => hQL _ (hptQ x)
  choose zX hzXL hzXp using hrow
  -- the factorization
  refine ⟨fun x l => gl l - ∑ v, K l v * zX x v,
    fun l y => lamY y l + (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') *
      ((lam1 l + lam2 l) / D), ?_, ?_, ?_⟩
  · intro x l
    have := (hzXL x).2 l
    show 0 ≤ gl l - ∑ v, K l v * zX x v
    linarith
  · intro l y
    show 0 ≤ lamY y l + (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') *
      ((lam1 l + lam2 l) / D)
    have hDp : 0 < D := by rw [hDdef]; exact hD
    have h1 := hβY y
    have h2 : 0 ≤ (lam1 l + lam2 l) / D := div_nonneg (add_nonneg (hlam1 l) (hlam2 l)) hDp.le
    have h3 := hlamY y l
    have h4 : 0 ≤ 1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l' := by linarith
    exact add_nonneg h3 (mul_nonneg h4 h2)
  · ext x y
    show (1 - ε) * PSDPolyApprox.qy n y x + ε = ∑ l, (gl l - ∑ v, K l v * zX x v) * (lamY y l +
        (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') * ((lam1 l + lam2 l) / D))
    unfold PSDPolyApprox.qy
    have hcol := hsl _ (μY y) (lamY y) (haY y) (zX x) (hzXL x).1
    rw [liftA_dot, hzXp, hcypt] at hcol
    have hal := hα (zX x) (hzXL x).1
    have e : ∑ l, (gl l - ∑ v, K l v * zX x v) * (lamY y l +
        (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') * ((lam1 l + lam2 l) / D))
        = ∑ l, lamY y l * (gl l - ∑ v, K l v * zX x v)
          + (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') *
            ∑ l, ((lam1 l + lam2 l) / D) * (gl l - ∑ v, K l v * zX x v) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [e, hal]
    linarith
