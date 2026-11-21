-- Prove2me | solution 1 for PSDPolyApprox.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T04:46:43.437137+00:00
-- url     : https://prove2.me/submissions/934db6df-f778-40ef-8b37-dd354973154b

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_PSDPolyApprox_pairSlackMatrix

open ExtensionComplexity.TSP
open scoped Matrix

namespace Aux_PSD4

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

/-! ### Auxiliary facts for the generalized Yannakakis theorem -/

lemma liftA_dot' {ι : Type*} [Fintype ι] {k : ℕ} (c : ι → ℝ) (z : ι ⊕ Fin k → ℝ) :
    ∑ v, (Sum.elim c (fun _ => (0 : ℝ)) v) * z v = ∑ x, c x * (z ∘ Sum.inl) x := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero,
    Function.comp_apply]

lemma single_mem {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Set (ι → ℝ))
    (h : (0 : ι → ℝ) ∈ interior S) :
    ∃ δ > 0, ∀ (i : ι) (t : ℝ), |t| < δ → Pi.single i t ∈ S := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h
  obtain ⟨δ, hδ, hball⟩ := h
  refine ⟨δ, hδ, fun i t ht => hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Pi.norm_single, Real.norm_eq_abs]
  exact ht

lemma polar_convex {ι : Type*} [Fintype ι] (L : Set (ι → ℝ)) :
    Convex ℝ (PSDPolyApprox.polar L) := by
  intro y1 hy1 y2 hy2 a b ha hb hab
  show ∀ x ∈ L, x ⬝ᵥ (a • y1 + b • y2) ≤ 1
  intro x hx
  have h1 : x ⬝ᵥ y1 ≤ 1 := hy1 x hx
  have h2 : x ⬝ᵥ y2 ≤ 1 := hy2 x hx
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have h3 : a * (x ⬝ᵥ y1) ≤ a * 1 := mul_le_mul_of_nonneg_left h1 ha
  have h4 : b * (x ⬝ᵥ y2) ≤ b * 1 := mul_le_mul_of_nonneg_left h2 hb
  linarith

lemma polar_closed {ι : Type*} [Fintype ι] (L : Set (ι → ℝ)) :
    IsClosed (PSDPolyApprox.polar L) := by
  have e : PSDPolyApprox.polar L = ⋂ x ∈ L, {y : ι → ℝ | x ⬝ᵥ y ≤ 1} := by
    ext y
    simp only [PSDPolyApprox.polar, Set.mem_setOf_eq, Set.mem_iInter]
  rw [e]
  refine isClosed_biInter (fun x _ => isClosed_le ?_ continuous_const)
  show Continuous fun y : ι → ℝ => ∑ i, x i * y i
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))

lemma two_div_mul {δ : ℝ} (hδ : 0 < δ) (a : ℝ) : 2 / δ * (δ / 2 * a) = a := by
  rw [← mul_assoc, div_mul_div_comm, mul_comm (2 : ℝ) δ,
    div_self (show δ * 2 ≠ 0 by positivity), one_mul]

lemma polar_bdd {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Set (ι → ℝ)) (δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ (i : ι) (t : ℝ), |t| < δ → Pi.single i t ∈ L) :
    ∀ y ∈ PSDPolyApprox.polar L, ∀ i, y i ∈ Set.Icc (-(2 / δ)) (2 / δ) := by
  intro y hy i
  have hp : |δ / 2| < δ := by
    rw [abs_of_pos (show (0 : ℝ) < δ / 2 by linarith)]
    linarith
  have hn : |-(δ / 2)| < δ := by
    rw [abs_neg]
    exact hp
  have h1 : Pi.single i (δ / 2) ⬝ᵥ y ≤ 1 := hy _ (hs i (δ / 2) hp)
  have h2 : Pi.single i (-(δ / 2)) ⬝ᵥ y ≤ 1 := hy _ (hs i (-(δ / 2)) hn)
  rw [single_dotProduct] at h1 h2
  have hc : (0 : ℝ) ≤ 2 / δ := by positivity
  have hup : y i ≤ 2 / δ := by
    calc y i = 2 / δ * (δ / 2 * y i) := (two_div_mul hδ (y i)).symm
      _ ≤ 2 / δ * 1 := mul_le_mul_of_nonneg_left h1 hc
      _ = 2 / δ := mul_one _
  have hlo : -(y i) ≤ 2 / δ := by
    have e : -(δ / 2) * y i = δ / 2 * (-(y i)) := by ring
    rw [e] at h2
    calc -(y i) = 2 / δ * (δ / 2 * (-(y i))) := (two_div_mul hδ (-(y i))).symm
      _ ≤ 2 / δ * 1 := mul_le_mul_of_nonneg_left h2 hc
      _ = 2 / δ := mul_one _
  exact ⟨by linarith, hup⟩

lemma compact_polar {ι : Type*} [Fintype ι] (L : Set (ι → ℝ))
    (hL0 : (0 : ι → ℝ) ∈ interior L) : IsCompact (PSDPolyApprox.polar L) := by
  classical
  obtain ⟨δ, hδ, hs⟩ := single_mem L hL0
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := -(2 / δ)) (b := 2 / δ)))
    (polar_closed L) ?_
  intro y hy
  rw [Set.mem_univ_pi]
  exact polar_bdd L δ hδ hs y hy

/-- the bipolar inclusion, through the extreme points of the polar. -/
lemma memL {ι : Type*} [Fintype ι] (L : Set (ι → ℝ)) (hLc : IsCompact L) (hLconv : Convex ℝ L)
    (hL0 : (0 : ι → ℝ) ∈ interior L) (x : ι → ℝ)
    (hx : ∀ y ∈ (PSDPolyApprox.polar L).extremePoints ℝ, x ⬝ᵥ y ≤ 1) : x ∈ L := by
  classical
  by_contra hxL
  obtain ⟨f, u, hfu, hut⟩ := geometric_hahn_banach_closed_point hLconv hLc.isClosed hxL
  have h0L : (0 : ι → ℝ) ∈ L := interior_subset hL0
  have hu : 0 < u := by
    have := hfu 0 h0L
    rwa [map_zero] at this
  obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, c = fun i => f (fun j => if i = j then (1 : ℝ) else 0) :=
    ⟨_, rfl⟩
  have hf : ∀ w : ι → ℝ, f w = w ⬝ᵥ c := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ w]
    rw [map_sum, hc]
    show ∑ i, f (w i • fun j => if i = j then (1 : ℝ) else 0) =
      ∑ i, w i * f (fun j => if i = j then (1 : ℝ) else 0)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
  have hy0 : u⁻¹ • c ∈ PSDPolyApprox.polar L := by
    show ∀ a ∈ L, a ⬝ᵥ (u⁻¹ • c) ≤ 1
    intro a ha
    rw [dotProduct_smul, smul_eq_mul, ← hf, inv_mul_le_iff₀ hu, mul_one]
    exact (hfu a ha).le
  have hxy0 : 1 < x ⬝ᵥ (u⁻¹ • c) := by
    rw [dotProduct_smul, smul_eq_mul, ← hf, lt_inv_mul_iff₀ hu, mul_one]
    exact hut
  have hlin : IsLinearMap ℝ (fun y : ι → ℝ => x ⬝ᵥ y) :=
    ⟨fun a b => dotProduct_add x a b, fun c a => dotProduct_smul c x a⟩
  have hH : PSDPolyApprox.polar L ⊆ {y : ι → ℝ | x ⬝ᵥ y ≤ 1} := by
    rw [← closure_convexHull_extremePoints (compact_polar L hL0) (polar_convex L)]
    refine closure_minimal (convexHull_min (fun y hy => hx y hy) (convex_halfSpace_le hlin 1)) ?_
    refine isClosed_le ?_ continuous_const
    show Continuous fun y : ι → ℝ => ∑ i, x i * y i
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))
  have h1 : x ⬝ᵥ (u⁻¹ • c) ≤ 1 := hH hy0
  linarith

/-- an extreme point of a polyhedron is determined by its zero pattern. -/
lemma ext_finite {V m : Type*} [Fintype V] (M : Matrix m V ℝ) (c : m → ℝ) (I : V → Prop)
    (Q : Set (V → ℝ)) (hQ : ∀ w, w ∈ Q ↔ (M *ᵥ w = c ∧ ∀ v, I v → 0 ≤ w v)) :
    (Q.extremePoints ℝ).Finite := by
  classical
  refine Set.Finite.of_finite_image
    (f := fun w : V → ℝ => Finset.univ.filter (fun v => I v ∧ w v = 0)) (Set.toFinite _) ?_
  intro w1 hw1 w2 hw2 hJ
  have hJ' : ∀ v, I v → w1 v = 0 → w2 v = 0 := by
    intro v hv h0
    have e : Finset.univ.filter (fun v => I v ∧ w1 v = 0) =
        Finset.univ.filter (fun v => I v ∧ w2 v = 0) := hJ
    have hmem : v ∈ Finset.univ.filter (fun v => I v ∧ w2 v = 0) := by
      rw [← e]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, h0⟩
    exact (Finset.mem_filter.mp hmem).2.2
  have hQ1 := (hQ w1).mp (extremePoints_subset hw1)
  have hQ2 := (hQ w2).mp (extremePoints_subset hw2)
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ ∀ v, I v → 0 < w1 v → s * (|w2 v| + 1) ≤ w1 v := by
    by_cases hne : (Finset.univ.filter (fun v => I v ∧ 0 < w1 v)).Nonempty
    · obtain ⟨v0, hv0, hmin⟩ :=
        Finset.exists_min_image _ (fun v => w1 v / (|w2 v| + 1)) hne
      have hv0' : I v0 ∧ 0 < w1 v0 := (Finset.mem_filter.mp hv0).2
      refine ⟨w1 v0 / (|w2 v0| + 1), div_pos hv0'.2 (by positivity), fun v hv hpos => ?_⟩
      have h : w1 v0 / (|w2 v0| + 1) ≤ w1 v / (|w2 v| + 1) :=
        hmin v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hpos⟩)
      rwa [le_div_iff₀ (show (0 : ℝ) < |w2 v| + 1 by positivity)] at h
    · exact ⟨1, one_pos, fun v hv hpos =>
        (hne ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hpos⟩⟩).elim⟩
  have hx1 : w1 - s • (w2 - w1) ∈ Q := by
    rw [hQ]
    refine ⟨?_, fun v hv => ?_⟩
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_sub, hQ1.1, hQ2.1, sub_self,
        smul_zero, sub_zero]
    · show 0 ≤ w1 v - s * (w2 v - w1 v)
      rcases (hQ1.2 v hv).lt_or_eq with hpos | hzero
      · have h1 := hs v hv hpos
        have h2 : s * w2 v ≤ s * |w2 v| := mul_le_mul_of_nonneg_left (le_abs_self _) hs0.le
        have h3 : 0 ≤ s * w1 v := mul_nonneg hs0.le hpos.le
        linarith
      · have h1 : w1 v = 0 := hzero.symm
        have h2 := hJ' v hv h1
        rw [h1, h2]
        linarith
  have hseg : w1 ∈ openSegment ℝ (w1 - s • (w2 - w1)) w2 := by
    refine ⟨1 / (1 + s), s / (1 + s), by positivity, by positivity, ?_, ?_⟩
    · rw [← add_div, div_eq_one_iff_eq (show (1 : ℝ) + s ≠ 0 by positivity)]
    · funext v
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        div_eq_iff (show (1 : ℝ) + s ≠ 0 by positivity)]
      ring
  have h := (mem_extremePoints_iff_left.mp hw1).2 _ hx1 w2 (extremePoints_subset hw2) hseg
  have hd : s • (w2 - w1) = 0 := sub_eq_self.mp h
  rcases smul_eq_zero.mp hd with h0 | h0
  · exact absurd h0 hs0.ne'
  · exact (sub_eq_zero.mp h0).symm

/-- finitely many linear equations cut out the same affine sets as an arbitrary family. -/
lemma finite_eqns {V m : Type*} [Fintype V] [DecidableEq V] (M : Matrix m V ℝ) :
    ∃ (p : ℕ) (Mq : Matrix (Fin p) V ℝ), ∀ w w' : V → ℝ,
      Mq *ᵥ w = Mq *ᵥ w' ↔ M *ᵥ w = M *ᵥ w' := by
  refine ⟨Module.finrank ℝ ((V → ℝ) ⧸ LinearMap.ker (Matrix.toLin' M)),
    LinearMap.toMatrix' ((Module.finBasis ℝ ((V → ℝ) ⧸ LinearMap.ker (Matrix.toLin' M))).equivFun.toLinearMap
      ∘ₗ (LinearMap.ker (Matrix.toLin' M)).mkQ), fun w w' => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  have key : ((LinearMap.ker (Matrix.toLin' M)).mkQ w = (LinearMap.ker (Matrix.toLin' M)).mkQ w') ↔
      M *ᵥ w = M *ᵥ w' := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker,
      map_sub, Matrix.toLin'_apply, Matrix.toLin'_apply, sub_eq_zero]
  exact (Module.finBasis ℝ ((V → ℝ) ⧸ LinearMap.ker (Matrix.toLin' M))).equivFun.injective.eq_iff.trans
    key

/-- the equality system of the lifted polyhedron. -/
noncomputable def Mmat {ι E : Type*} {r : ℕ} (Y : E → ι → ℝ) (U : Fin r → E → ℝ)
    (Z : Fin r → Prop) [DecidablePred Z] : Matrix (E ⊕ Fin r) (ι ⊕ Fin r) ℝ :=
  Matrix.fromBlocks (Matrix.of fun y i => Y y i) (Matrix.of fun y l => U l y) 0
    (Matrix.diagonal fun l => if Z l then 1 else 0)

lemma Mmat_inl {ι E : Type*} [Fintype ι] {r : ℕ} (Y : E → ι → ℝ) (U : Fin r → E → ℝ)
    (Z : Fin r → Prop) [DecidablePred Z] (w : ι ⊕ Fin r → ℝ) (y : E) :
    (Mmat Y U Z *ᵥ w) (Sum.inl y) = ∑ i, Y y i * w (Sum.inl i) + ∑ l, U l y * w (Sum.inr l) :=
  (congrFun (Matrix.fromBlocks_mulVec (Matrix.of fun y i => Y y i) (Matrix.of fun y l => U l y)
    (0 : Matrix (Fin r) ι ℝ) (Matrix.diagonal fun l => if Z l then (1 : ℝ) else 0) w)
    (Sum.inl y)).trans rfl

lemma Mmat_inr {ι E : Type*} [Fintype ι] {r : ℕ} (Y : E → ι → ℝ) (U : Fin r → E → ℝ)
    (Z : Fin r → Prop) [DecidablePred Z] (w : ι ⊕ Fin r → ℝ) (l : Fin r) :
    (Mmat Y U Z *ᵥ w) (Sum.inr l) = (if Z l then (1 : ℝ) else 0) * w (Sum.inr l) := by
  have h := congrFun (Matrix.fromBlocks_mulVec (Matrix.of fun y i => Y y i)
    (Matrix.of fun y l => U l y) (0 : Matrix (Fin r) ι ℝ)
    (Matrix.diagonal fun l => if Z l then (1 : ℝ) else 0) w) (Sum.inr l)
  have h2 : (Mmat Y U Z *ᵥ w) (Sum.inr l) =
      ((0 : Matrix (Fin r) ι ℝ) *ᵥ (w ∘ Sum.inl) +
        Matrix.diagonal (fun l => if Z l then (1 : ℝ) else 0) *ᵥ (w ∘ Sum.inr)) l := h
  rw [h2, Pi.add_apply, Matrix.zero_mulVec, Pi.zero_apply, zero_add, Matrix.mulVec_diagonal,
    Function.comp_apply]

/-! ### The direction `xc ≤ r ⟹ rank₊ ≤ r` -/

set_option maxHeartbeats 1600000 in
theorem fwd {ι : Type*} [Fintype ι] [Nonempty ι] (K L : Set (ι → ℝ))
    (h0 : (0 : ι → ℝ) ∈ interior K) (P : Set (ι → ℝ)) (hP : IsPolytope P) (hKP : K ⊆ P)
    (hPL : P ⊆ L) :
    HasNonnegFactorization (PSDPolyApprox.pairSlackMatrix K L) (extensionComplexity P) := by
  classical
  obtain ⟨r0, hr0⟩ := polyEF P hP
  have hEFr : IsEFOfSize P (extensionComplexity P) :=
    Nat.sInf_mem (s := {r : ℕ | IsEFOfSize P r}) ⟨r0, hr0⟩
  generalize extensionComplexity P = r at hEFr ⊢
  obtain ⟨k, p, Ee, Fe, ge, El, Fl, gl, hEF⟩ := hEFr
  obtain ⟨G, hG⟩ : ∃ G : Fin p → (ι ⊕ Fin k) → ℝ,
      G = fun j => Sum.elim (fun x => Ee j x) (fun w => Fe j w) := ⟨_, rfl⟩
  obtain ⟨Km, hKm⟩ : ∃ Km : Fin r → (ι ⊕ Fin k) → ℝ,
      Km = fun l => Sum.elim (fun x => El l x) (fun w => Fl l w) := ⟨_, rfl⟩
  have hGz : ∀ (z : ι ⊕ Fin k → ℝ) j,
      ∑ v, G j v * z v = (Ee *ᵥ (z ∘ Sum.inl) + Fe *ᵥ (z ∘ Sum.inr)) j := by
    intro z j
    rw [hG, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct,
      Function.comp_apply]
  have hKz : ∀ (z : ι ⊕ Fin k → ℝ) l,
      ∑ v, Km l v * z v = (El *ᵥ (z ∘ Sum.inl) + Fl *ᵥ (z ∘ Sum.inr)) l := by
    intro z l
    rw [hKm, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.mulVec, dotProduct,
      Function.comp_apply]
  have hLQ : ∀ z : ι ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) →
      (∀ l, ∑ v, Km l v * z v ≤ gl l) → z ∘ Sum.inl ∈ P := by
    intro z h1 h2
    refine (hEF _).mpr ⟨z ∘ Sum.inr, funext fun j => ?_, fun l => ?_⟩
    · rw [← hGz]; exact h1 j
    · rw [← hKz]; exact h2 l
  have hQL : ∀ x ∈ P, ∃ z : ι ⊕ Fin k → ℝ, ((∀ j, ∑ v, G j v * z v = ge j) ∧
      (∀ l, ∑ v, Km l v * z v ≤ gl l)) ∧ z ∘ Sum.inl = x := by
    intro x hx
    obtain ⟨w, h1, h2⟩ := (hEF x).mp hx
    refine ⟨Sum.elim x w, ⟨fun j => ?_, fun l => ?_⟩, Sum.elim_comp_inl x w⟩
    · rw [hGz, Sum.elim_comp_inl, Sum.elim_comp_inr, h1]
    · rw [hKz, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact h2 l
  -- valid inequalities from the polar
  have hval : ∀ y : ↥((PSDPolyApprox.polar L).extremePoints ℝ), ∀ x ∈ P,
      ∑ i, (y : ι → ℝ) i * x i ≤ 1 := by
    intro y x hx
    have hy : (y : ι → ℝ) ∈ PSDPolyApprox.polar L := extremePoints_subset y.2
    have h1 : x ⬝ᵥ (y : ι → ℝ) ≤ 1 := hy x (hPL hx)
    have e : x ⬝ᵥ (y : ι → ℝ) = ∑ i, (y : ι → ℝ) i * x i := (dotProduct_comm _ _).trans rfl
    rw [← e]
    exact h1
  -- nonemptiness of the lifted system
  have h0P : (0 : ι → ℝ) ∈ P := hKP (interior_subset h0)
  obtain ⟨z1, hz1L, _⟩ := hQL _ h0P
  have hne : ∃ z : ι ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) ∧
      (∀ l, ∑ v, Km l v * z v ≤ gl l) := ⟨z1, hz1L⟩
  -- Farkas certificates for the columns
  have hcolF : ∀ y : ↥((PSDPolyApprox.polar L).extremePoints ℝ),
      ∃ (μ : Fin p → ℝ) (lam : Fin r → ℝ), (∀ l, 0 ≤ lam l) ∧
      (∀ v, Sum.elim (y : ι → ℝ) (fun _ => (0 : ℝ)) v = ∑ j, μ j * G j v + ∑ l, lam l * Km l v) ∧
      ∑ j, μ j * ge j + ∑ l, lam l * gl l ≤ 1 := by
    intro y
    refine farkas G ge Km gl (Sum.elim (y : ι → ℝ) (fun _ => (0 : ℝ))) 1 hne ?_
    intro z h1 h2
    rw [liftA_dot']
    exact hval y _ (hLQ z h1 h2)
  choose μY lamY hlamY haY hβY using hcolF
  -- the constant: a coordinate functional, maximised and minimised on P
  obtain ⟨c0⟩ := (inferInstance : Nonempty ι)
  have hlin : IsLinearMap ℝ (fun x : ι → ℝ => x c0) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨V0, hV0⟩ := hP
  have hV0ne : V0.Nonempty := by
    rcases V0.eq_empty_or_nonempty with h | h
    · have := h0P
      rw [hV0, h, Finset.coe_empty, convexHull_empty] at this
      exact absurd this (Set.notMem_empty _)
    · exact h
  obtain ⟨vmax, hvmaxV, hvmax⟩ := Finset.exists_max_image V0 (fun x => x c0) hV0ne
  obtain ⟨vmin, hvminV, hvmin⟩ := Finset.exists_min_image V0 (fun x => x c0) hV0ne
  have hmaxQ : ∀ x ∈ P, x c0 ≤ vmax c0 := by
    intro x hx
    rw [hV0] at hx
    exact convexHull_min (fun v hv => show v ∈ {w : ι → ℝ | w c0 ≤ vmax c0} from
      hvmax v hv) (convex_halfSpace_le hlin _) hx
  have hminQ : ∀ x ∈ P, vmin c0 ≤ x c0 := by
    intro x hx
    rw [hV0] at hx
    exact convexHull_min (fun v hv => show v ∈ {w : ι → ℝ | vmin c0 ≤ w c0} from
      hvmin v hv) (convex_halfSpace_ge hlin _) hx
  have hvmaxQ : vmax ∈ P := by rw [hV0]; exact subset_convexHull ℝ _ hvmaxV
  have hvminQ : vmin ∈ P := by rw [hV0]; exact subset_convexHull ℝ _ hvminV
  -- two points of K with different coordinate c0
  obtain ⟨δ, hδ, hsK⟩ := single_mem K h0
  have hpa : |δ / 2| < δ := by
    rw [abs_of_pos (show (0 : ℝ) < δ / 2 by linarith)]
    linarith
  have hpb : |-(δ / 2)| < δ := by
    rw [abs_neg]
    exact hpa
  have hxa : Pi.single c0 (δ / 2) ∈ P := hKP (hsK c0 (δ / 2) hpa)
  have hxb : Pi.single c0 (-(δ / 2)) ∈ P := hKP (hsK c0 (-(δ / 2)) hpb)
  have hD : 0 < vmax c0 - vmin c0 := by
    have h1 := hmaxQ _ hxa
    have h2 := hminQ _ hxb
    rw [Pi.single_eq_same] at h1 h2
    linarith
  -- Farkas for the max and the min
  obtain ⟨μ1, lam1, hlam1, ha1, hβ1⟩ := farkas G ge Km gl
    (Sum.elim (fun x => if x = c0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ))) (vmax c0) hne
    (fun z h1 h2 => by
      rw [liftA_dot']
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hmaxQ _ (hLQ z h1 h2))
  obtain ⟨μ2, lam2, hlam2, ha2, hβ2⟩ := farkas G ge Km gl
    (Sum.elim (fun x => if x = c0 then (-1 : ℝ) else 0) (fun _ => (0 : ℝ))) (-vmin c0) hne
    (fun z h1 h2 => by
      rw [liftA_dot']
      simp only [ite_mul, neg_one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have := hminQ _ (hLQ z h1 h2)
      simp only [Function.comp_apply] at this ⊢
      linarith)
  -- slack identities
  have hsl : ∀ (a : ι ⊕ Fin k → ℝ) (μ : Fin p → ℝ) (lam : Fin r → ℝ),
      (∀ v, a v = ∑ j, μ j * G j v + ∑ l, lam l * Km l v) →
      ∀ z : ι ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) →
      ∑ v, a v * z v = ∑ j, μ j * ge j + ∑ l, lam l * gl l
        - ∑ l, lam l * (gl l - ∑ v, Km l v * z v) := by
    intro a μ lam ha z hz
    rw [farkas_slack G ge Km gl a μ lam ha z hz]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hslnn : ∀ (lam : Fin r → ℝ), (∀ l, 0 ≤ lam l) →
      ∀ z : ι ⊕ Fin k → ℝ, (∀ l, ∑ v, Km l v * z v ≤ gl l) →
      0 ≤ ∑ l, lam l * (gl l - ∑ v, Km l v * z v) := by
    intro lam hlam z hz
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hlam l) (by linarith [hz l]))
  have hdot1 : ∀ z : ι ⊕ Fin k → ℝ,
      ∑ v, Sum.elim (fun x => if x = c0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ)) v * z v
        = z (Sum.inl c0) := by
    intro z
    rw [liftA_dot']
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Function.comp_apply]
  have hdot2 : ∀ z : ι ⊕ Fin k → ℝ,
      ∑ v, Sum.elim (fun x => if x = c0 then (-1 : ℝ) else 0) (fun _ => (0 : ℝ)) v * z v
        = -z (Sum.inl c0) := by
    intro z
    rw [liftA_dot']
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
  have hα : ∀ z : ι ⊕ Fin k → ℝ, (∀ j, ∑ v, G j v * z v = ge j) →
      ∑ l, ((lam1 l + lam2 l) / D) * (gl l - ∑ v, Km l v * z v) = 1 := by
    intro z hz
    have e1 := hsl _ μ1 lam1 ha1 z hz
    have e2 := hsl _ μ2 lam2 ha2 z hz
    rw [hdot1, hδ1] at e1
    rw [hdot2, hδ2] at e2
    have hsum : ∑ l, ((lam1 l + lam2 l) / D) * (gl l - ∑ v, Km l v * z v)
        = (∑ l, lam1 l * (gl l - ∑ v, Km l v * z v) +
            ∑ l, lam2 l * (gl l - ∑ v, Km l v * z v)) / D := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [hsum, div_eq_one_iff_eq (by rw [hDdef]; exact hD.ne')]
    rw [hDdef]
    linarith
  -- rows: lifts of the extreme points of K
  have hrow : ∀ x : ↥(K.extremePoints ℝ), ∃ z : ι ⊕ Fin k → ℝ,
      ((∀ j, ∑ v, G j v * z v = ge j) ∧ (∀ l, ∑ v, Km l v * z v ≤ gl l)) ∧
        z ∘ Sum.inl = (x : ι → ℝ) :=
    fun x => hQL _ (hKP (extremePoints_subset x.2))
  choose zX hzXL hzXp using hrow
  -- the factorization
  refine ⟨fun x l => gl l - ∑ v, Km l v * zX x v,
    fun l y => lamY y l + (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') *
      ((lam1 l + lam2 l) / D), ?_, ?_, ?_⟩
  · intro x l
    have := (hzXL x).2 l
    show 0 ≤ gl l - ∑ v, Km l v * zX x v
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
    show 1 - (x : ι → ℝ) ⬝ᵥ (y : ι → ℝ) = ∑ l, (gl l - ∑ v, Km l v * zX x v) * (lamY y l +
        (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') * ((lam1 l + lam2 l) / D))
    have hcol := hsl _ (μY y) (lamY y) (haY y) (zX x) (hzXL x).1
    rw [liftA_dot', hzXp] at hcol
    have e0 : (x : ι → ℝ) ⬝ᵥ (y : ι → ℝ) = ∑ i, (y : ι → ℝ) i * (x : ι → ℝ) i :=
      (dotProduct_comm _ _).trans rfl
    have hal := hα (zX x) (hzXL x).1
    have e : ∑ l, (gl l - ∑ v, Km l v * zX x v) * (lamY y l +
        (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') * ((lam1 l + lam2 l) / D))
        = ∑ l, lamY y l * (gl l - ∑ v, Km l v * zX x v)
          + (1 - ∑ j, μY y j * ge j - ∑ l', lamY y l' * gl l') *
            ∑ l, ((lam1 l + lam2 l) / D) * (gl l - ∑ v, Km l v * zX x v) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l _ => by ring)
    rw [e, hal, e0]
    linarith

/-! ### The direction `rank₊ ≤ r ⟹ xc ≤ r` -/

set_option maxHeartbeats 1600000 in
theorem bwd {ι : Type*} [Fintype ι] (K L : Set (ι → ℝ)) (hKc : IsCompact K)
    (hKconv : Convex ℝ K) (hLc : IsCompact L) (hLconv : Convex ℝ L)
    (h0 : (0 : ι → ℝ) ∈ interior K) (hKL : K ⊆ L) (r' : ℕ)
    (T : Matrix ↥(K.extremePoints ℝ) (Fin r') ℝ)
    (U : Matrix (Fin r') ↥((PSDPolyApprox.polar L).extremePoints ℝ) ℝ)
    (hT : ∀ i l, 0 ≤ T i l) (hU : ∀ l j, 0 ≤ U l j)
    (hS : PSDPolyApprox.pairSlackMatrix K L = T * U) :
    ∃ P : Set (ι → ℝ), IsPolytope P ∧ K ⊆ P ∧ P ⊆ L ∧ IsEFOfSize P r' := by
  classical
  have hL0 : (0 : ι → ℝ) ∈ interior L := interior_mono hKL h0
  have hSxy : ∀ (x : ↥(K.extremePoints ℝ)) (y : ↥((PSDPolyApprox.polar L).extremePoints ℝ)),
      1 - (x : ι → ℝ) ⬝ᵥ (y : ι → ℝ) = ∑ l, T x l * U l y := by
    intro x y
    have h := congrFun (congrFun hS x) y
    exact h
  obtain ⟨Mm, hMm⟩ : ∃ Mm : Matrix (↥((PSDPolyApprox.polar L).extremePoints ℝ) ⊕ Fin r')
      (ι ⊕ Fin r') ℝ, Mm = Mmat (Subtype.val : ↥((PSDPolyApprox.polar L).extremePoints ℝ) → ι → ℝ)
        U (fun l => ∀ y, U l y = 0) := ⟨_, rfl⟩
  have hMinl : ∀ (w : ι ⊕ Fin r' → ℝ) (y : ↥((PSDPolyApprox.polar L).extremePoints ℝ)),
      (Mm *ᵥ w) (Sum.inl y) = ∑ i, (y : ι → ℝ) i * w (Sum.inl i) + ∑ l, U l y * w (Sum.inr l) := by
    intro w y
    rw [hMm]
    exact Mmat_inl _ _ _ w y
  have hMinr : ∀ (w : ι ⊕ Fin r' → ℝ) (l : Fin r'),
      (Mm *ᵥ w) (Sum.inr l) = (if (∀ y, U l y = 0) then (1 : ℝ) else 0) * w (Sum.inr l) := by
    intro w l
    rw [hMm]
    exact Mmat_inr _ _ _ w l
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set (ι ⊕ Fin r' → ℝ), Q = {w | Mm *ᵥ w =
      Sum.elim (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) ∧ ∀ l, 0 ≤ w (Sum.inr l)} := ⟨_, rfl⟩
  have hQiff : ∀ w, w ∈ Q ↔ ((∀ y : ↥((PSDPolyApprox.polar L).extremePoints ℝ),
      ∑ i, (y : ι → ℝ) i * w (Sum.inl i) + ∑ l, U l y * w (Sum.inr l) = 1) ∧
      (∀ l, (∀ y, U l y = 0) → w (Sum.inr l) = 0)) ∧ (∀ l, 0 ≤ w (Sum.inr l)) := by
    intro w
    rw [hQdef, Set.mem_setOf_eq]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro h
      refine ⟨fun y => ?_, fun l hl => ?_⟩
      · have h1 := congrFun h (Sum.inl y)
        rw [hMinl] at h1
        exact h1
      · have h1 := congrFun h (Sum.inr l)
        rw [hMinr, if_pos hl, one_mul] at h1
        exact h1
    · rintro ⟨h1, h2⟩
      funext o
      rcases o with y | l
      · rw [hMinl]
        exact h1 y
      · by_cases hl : ∀ y, U l y = 0
        · simp only [hMinr, if_pos hl, one_mul, Sum.elim_inr]
          exact h2 l hl
        · simp only [hMinr, if_neg hl, zero_mul, Sum.elim_inr]
  have hQ' : ∀ w, w ∈ Q ↔ (Mm *ᵥ w = Sum.elim (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) ∧
      ∀ v, (∃ l, v = Sum.inr l) → 0 ≤ w v) := by
    intro w
    rw [hQdef, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v ⟨l, hl⟩ => by rw [hl]; exact h2 l⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l => h2 _ ⟨l, rfl⟩⟩
  -- lifts of the extreme points of K
  have hlift : ∀ x : ↥(K.extremePoints ℝ),
      Sum.elim (x : ι → ℝ) (fun l => if (∀ y, U l y = 0) then 0 else T x l) ∈ Q := by
    intro x
    rw [hQiff]
    refine ⟨⟨fun y => ?_, fun l hl => ?_⟩, fun l => ?_⟩
    · simp only [Sum.elim_inl, Sum.elim_inr]
      have e1 : ∑ l, U l y * (if (∀ y, U l y = 0) then 0 else T x l) = ∑ l, T x l * U l y := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        by_cases hz : ∀ y, U l y = 0
        · simp only [if_pos hz, hz y, mul_zero]
        · rw [if_neg hz, mul_comm]
      have e2 : ∑ i, (y : ι → ℝ) i * (x : ι → ℝ) i = (x : ι → ℝ) ⬝ᵥ (y : ι → ℝ) :=
        ((dotProduct_comm _ _).trans rfl).symm
      rw [e1, e2, ← hSxy x y]
      ring
    · simp only [Sum.elim_inr, if_pos hl]
    · simp only [Sum.elim_inr]
      split_ifs with hz
      · exact le_rfl
      · exact hT x l
  -- the projection lands in L
  have hQL' : ∀ w ∈ Q, (LinearMap.funLeft ℝ ℝ (Sum.inl : ι → ι ⊕ Fin r')) w ∈ L := by
    intro w hw
    apply memL L hLc hLconv hL0
    intro y hy
    obtain ⟨⟨h1, -⟩, h3⟩ := (hQiff w).mp hw
    have hrow : ∑ i, y i * w (Sum.inl i) + ∑ l, U l ⟨y, hy⟩ * w (Sum.inr l) = 1 := h1 ⟨y, hy⟩
    have hnn : 0 ≤ ∑ l, U l ⟨y, hy⟩ * w (Sum.inr l) :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (hU l _) (h3 l))
    show ∑ i, w (Sum.inl i) * y i ≤ 1
    have e : ∑ i, w (Sum.inl i) * y i = ∑ i, y i * w (Sum.inl i) :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e]
    linarith
  -- Q is convex and compact
  have hQconv : Convex ℝ Q := by
    rw [hQdef]
    intro w1 hw1 w2 hw2 a b ha hb hab
    refine ⟨?_, fun l => ?_⟩
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hw1.1, hw2.1, ← add_smul,
        hab, one_smul]
    · show 0 ≤ a * w1 (Sum.inr l) + b * w2 (Sum.inr l)
      exact add_nonneg (mul_nonneg ha (hw1.2 l)) (mul_nonneg hb (hw2.2 l))
  have hQclosed : IsClosed Q := by
    have e : Q = {w : ι ⊕ Fin r' → ℝ | Mm *ᵥ w = Sum.elim (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))} ∩
        ⋂ l, {w : ι ⊕ Fin r' → ℝ | 0 ≤ w (Sum.inr l)} := by
      rw [hQdef]
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [e]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply _))
    exact Continuous.matrix_mulVec (A := fun _ => Mm) (B := fun w => w) continuous_const
      continuous_id
  obtain ⟨R, hR⟩ := hLc.isBounded.subset_closedBall 0
  have hLR : ∀ x ∈ L, ∀ i, |x i| ≤ R := by
    intro x hx i
    have h1 := hR hx
    rw [mem_closedBall_zero_iff] at h1
    have h2 := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h2
    linarith
  have hβex : ∀ v : ι ⊕ Fin r', ∃ b : ℝ, ∀ w ∈ Q, |w v| ≤ b := by
    intro v
    rcases v with i | l
    · exact ⟨R, fun w hw => hLR _ (hQL' w hw) i⟩
    · by_cases hz : ∀ y, U l y = 0
      · refine ⟨0, fun w hw => ?_⟩
        have h := ((hQiff w).mp hw).1.2 l hz
        rw [h, abs_zero]
      · push_neg at hz
        obtain ⟨y, hy⟩ := hz
        have hpos : 0 < U l y := lt_of_le_of_ne (hU l y) (Ne.symm hy)
        refine ⟨(1 + R * ∑ i, |(y : ι → ℝ) i|) / U l y, fun w hw => ?_⟩
        obtain ⟨⟨h1, -⟩, h3⟩ := (hQiff w).mp hw
        have hrow := h1 y
        have hsingle : U l y * w (Sum.inr l) ≤ ∑ m, U m y * w (Sum.inr m) :=
          Finset.single_le_sum (f := fun m => U m y * w (Sum.inr m))
            (fun m _ => mul_nonneg (hU m y) (h3 m)) (Finset.mem_univ l)
        have hlow : -(R * ∑ i, |(y : ι → ℝ) i|) ≤ ∑ i, (y : ι → ℝ) i * w (Sum.inl i) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hxi : |w (Sum.inl i)| ≤ R := hLR _ (hQL' w hw) i
          have h4 : |(y : ι → ℝ) i * w (Sum.inl i)| ≤ R * |(y : ι → ℝ) i| := by
            rw [abs_mul]
            calc |(y : ι → ℝ) i| * |w (Sum.inl i)| ≤ |(y : ι → ℝ) i| * R :=
                  mul_le_mul_of_nonneg_left hxi (abs_nonneg _)
              _ = R * |(y : ι → ℝ) i| := mul_comm _ _
          linarith [neg_abs_le ((y : ι → ℝ) i * w (Sum.inl i))]
        rw [abs_of_nonneg (h3 l), le_div_iff₀ hpos]
        linarith
  choose β hβ using hβex
  have hQsub : Q ⊆ Set.univ.pi (fun v => Set.Icc (-β v) (β v)) := by
    intro w hw
    rw [Set.mem_univ_pi]
    intro v
    exact abs_le.mp (hβ v w hw)
  have hQc : IsCompact Q :=
    (isCompact_univ_pi fun v => isCompact_Icc).of_isClosed_subset hQclosed hQsub
  -- Q is the convex hull of its finitely many extreme points
  have hfin := ext_finite Mm (Sum.elim (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)))
    (fun v => ∃ l, v = Sum.inr l) Q hQ'
  have hKM := closure_convexHull_extremePoints hQc hQconv
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at hKM
  obtain ⟨P, hPdef⟩ : ∃ P : Set (ι → ℝ),
      P = (LinearMap.funLeft ℝ ℝ (Sum.inl : ι → ι ⊕ Fin r')) '' Q := ⟨_, rfl⟩
  have hPfin := hfin.image (LinearMap.funLeft ℝ ℝ (Sum.inl : ι → ι ⊕ Fin r'))
  have hPhull : P = convexHull ℝ
      ((LinearMap.funLeft ℝ ℝ (Sum.inl : ι → ι ⊕ Fin r')) '' Q.extremePoints ℝ) := by
    rw [hPdef, ← LinearMap.image_convexHull, hKM]
  have hPpoly : IsPolytope P := ⟨hPfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact hPhull⟩
  have hPclosed : IsClosed P := by
    rw [hPhull]
    exact hPfin.isClosed_convexHull ℝ
  have hPconv : Convex ℝ P := by
    rw [hPdef]
    exact hQconv.linear_image _
  -- K ⊆ P ⊆ L
  have hEKP : K.extremePoints ℝ ⊆ P := by
    intro x hx
    rw [hPdef]
    exact ⟨_, hlift ⟨x, hx⟩, rfl⟩
  have hKP : K ⊆ P := by
    intro x hx
    rw [← closure_convexHull_extremePoints hKc hKconv] at hx
    exact closure_minimal (convexHull_min hEKP hPconv) hPclosed hx
  have hPL : P ⊆ L := by
    rw [hPdef]
    rintro x ⟨w, hw, rfl⟩
    exact hQL' w hw
  -- an extended formulation with r' inequalities
  obtain ⟨x0, hx0⟩ := hKc.extremePoints_nonempty ⟨0, interior_subset h0⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, w0 ∈ Q := ⟨_, hlift ⟨x0, hx0⟩⟩
  have hw0M : Mm *ᵥ w0 = Sum.elim (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) := by
    rw [hQdef] at hw0
    exact hw0.1
  obtain ⟨p, Mq, hMq⟩ := finite_eqns Mm
  have hsplit : ∀ (x : ι → ℝ) (z : Fin r' → ℝ),
      (Matrix.of fun j i => Mq j (Sum.inl i)) *ᵥ x + (Matrix.of fun j l => Mq j (Sum.inr l)) *ᵥ z
        = Mq *ᵥ Sum.elim x z := by
    intro x z
    funext j
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Matrix.of_apply]
  have hle : ∀ (x : ι → ℝ) (z : Fin r' → ℝ),
      (0 : Matrix (Fin r') ι ℝ) *ᵥ x + (-1 : Matrix (Fin r') (Fin r') ℝ) *ᵥ z ≤ 0 ↔
        ∀ l, 0 ≤ z l := by
    intro x z
    rw [Matrix.zero_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec, zero_add, neg_nonpos]
    exact Pi.le_def
  have hEF : IsEFOfSize P r' := by
    refine toEF P r' (Equiv.refl (Fin r')) (Matrix.of fun j i => Mq j (Sum.inl i))
      (Matrix.of fun j l => Mq j (Sum.inr l)) (Mq *ᵥ w0) (0 : Matrix (Fin r') ι ℝ)
      (-1 : Matrix (Fin r') (Fin r') ℝ) 0 ?_
    intro x
    rw [hPdef]
    constructor
    · rintro ⟨w, hw, hwx⟩
      rw [hQdef] at hw
      refine ⟨w ∘ Sum.inr, ?_, ?_⟩
      · rw [hsplit, ← hwx]
        have e : Sum.elim ((LinearMap.funLeft ℝ ℝ (Sum.inl : ι → ι ⊕ Fin r')) w)
            (w ∘ Sum.inr) = w := Sum.elim_comp_inl_inr w
        rw [e]
        exact (hMq w w0).mpr (hw.1.trans hw0M.symm)
      · rw [hle]
        intro l
        exact hw.2 l
    · rintro ⟨z, h1, h2⟩
      refine ⟨Sum.elim x z, ?_, ?_⟩
      · rw [hQdef]
        refine ⟨?_, fun l => (hle x z).mp h2 l⟩
        rw [hsplit] at h1
        exact ((hMq _ _).mp h1).trans hw0M
      · funext i
        rfl
  exact ⟨P, hPpoly, hKP, hPL, hEF⟩

end Aux_PSD4

open Aux_PSD4 in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (K L : Set (ι → ℝ))
    (hKc : IsCompact K) (hKconv : Convex ℝ K) (hLc : IsCompact L) (hLconv : Convex ℝ L)
    (h0 : (0 : ι → ℝ) ∈ interior K) (hKL : K ⊆ L) (r : ℕ) :
    (∃ P : Set (ι → ℝ), IsPolytope P ∧ K ⊆ P ∧ P ⊆ L ∧ extensionComplexity P ≤ r) ↔
      (∃ r' ≤ r, HasNonnegFactorization (PSDPolyApprox.pairSlackMatrix K L) r') := by
  constructor
  · rintro ⟨P, hP, hKP, hPL, hxc⟩
    exact ⟨extensionComplexity P, hxc, fwd K L h0 P hP hKP hPL⟩
  · rintro ⟨r', hr', T, U, hT, hU, hS⟩
    obtain ⟨P, h1, h2, h3, h4⟩ := bwd K L hKc hKconv hLc hLconv h0 hKL r' T U hT hU hS
    exact ⟨P, h1, h2, h3,
      le_trans (Nat.sInf_le (show r' ∈ {r : ℕ | IsEFOfSize P r} from h4)) hr'⟩
