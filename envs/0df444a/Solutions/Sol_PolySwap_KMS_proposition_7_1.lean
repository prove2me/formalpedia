-- Prove2me | solution 1 for PolySwap.KMS.proposition_7_1
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T06:27:19.739095+00:00
-- url     : https://prove2.me/submissions/453101a1-e201-4a5c-86b8-b7f626b74d5c

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Cone
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Classical Matrix

namespace PolySwap.KMS.Sol71

open PolySwap.KMS

variable {d : ℕ} {F : Type*} [Field F]

abbrev SLd (d : ℕ) (F : Type*) [Field F] := SpecialLinearGroup (Fin (d + 1)) F

/-- The off-diagonal support of `M` lies on pairs `(i, j)` with `i < j` and every colour of
`(i, j]` in `S`. -/
def Pat (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop :=
  ∀ i j : Fin (d + 1), i ≠ j → M i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

/-- Unit diagonal. -/
def Diag1 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Prop := ∀ i, M i i = 1

lemma Pat.mono {S S' : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hS : S ⊆ S') : Pat S' M := fun i j hij hne =>
  ⟨(h i j hij hne).1, fun c h1 h2 => hS ((h i j hij hne).2 c h1 h2)⟩

lemma Pat.lower {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    {i j : Fin (d + 1)} (hij : j < i) : M i j = 0 := by
  by_contra hne
  exact absurd (h i j (ne_of_gt hij) hne).1 (not_lt.2 hij.le)

lemma pat_mul {S : Set ℕ} {M N : Matrix (Fin (d + 1)) (Fin (d + 1)) F}
    (hM : Pat S M) (hN : Pat S N) (dM : Diag1 M) (dN : Diag1 N) :
    Pat S (M * N) ∧ Diag1 (M * N) := by
  refine ⟨fun i j hij hne => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply] at hne
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have h1 : M i k ≠ 0 := left_ne_zero_of_mul hk
    have h2 : N k j ≠ 0 := right_ne_zero_of_mul hk
    by_cases hik : i = k
    · subst hik; exact hN i j hij h2
    by_cases hkj : k = j
    · subst hkj; exact hM i k hik h1
    obtain ⟨a1, a2⟩ := hM i k hik h1
    obtain ⟨b1, b2⟩ := hN k j hkj h2
    refine ⟨a1.trans b1, fun c hc1 hc2 => ?_⟩
    by_cases hc : c ≤ (k : ℕ)
    · exact a2 c hc1 hc
    · exact b2 c (by omega) hc2
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [dM i, dN i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · simp [hM.lower h]
      · simp [hN.lower h]
    · simp

lemma pat_transvection {S : Set ℕ} (i j : Fin (d + 1)) (hij : i < j)
    (hS : ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) (c : F) :
    Pat S (transvection i j c) ∧ Diag1 (transvection i j c) := by
  refine ⟨fun a b hab hne => ?_, fun a => ?_⟩
  · simp only [transvection, Matrix.add_apply, Matrix.one_apply, hab, if_false, zero_add,
      Matrix.single_apply] at hne
    split_ifs at hne with h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨hij, hS⟩
    · exact absurd rfl hne
  · simp [transvection, Matrix.single_apply]
    intro h1 h2; subst h1; subst h2; exact absurd hij (lt_irrefl _)

lemma ss0 {i j k l : Fin (d + 1)} (h : j ≠ k) (a b : F) :
    (Matrix.single i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * Matrix.single k l b = 0 :=
  by
    ext x y
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    split_ifs with h1 h2 <;> first | (exfalso; exact h (h1.2.trans h2.1.symm)) | simp

lemma tv_mul (i j : Fin (d + 1)) (hij : i ≠ j) (a b : F) :
    (transvection i j a : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j b =
      transvection i j (a + b) := by
  simp only [transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    ss0 (Ne.symm hij), add_zero, Matrix.single_add]
  abel

/-- Elements of `UL S` are unitriangular with support in `S`-runs. -/
lemma pat_of_mem_UL {S : Finset ℕ} {g : SLd d F} (hg : g ∈ UL d F S) :
    Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    rw [hx]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) lam
  | inv_mem x hx =>
    obtain ⟨lam, i, j, hjS, -, hij, hx⟩ := hx
    have hne : i ≠ j := fun h => by subst h; omega
    have : ((x⁻¹ : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j (-lam) := by
      have h1 : (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * transvection i j (-lam) = 1 := by
        rw [hx, tv_mul i j hne]; simp [transvection]
      have : x⁻¹ = (⟨transvection i j (-lam), det_transvection_of_ne _ _ hne _⟩ : SLd d F) := by
        exact inv_eq_of_mul_eq_one_right (Subtype.ext h1)
      rw [this]
    rw [this]
    exact pat_transvection i j (Fin.lt_def.2 (by omega))
      (fun c h1 h2 => by have : c = j := by omega
                         subst this; exact hjS) _
  | one => exact ⟨fun i j hij hne => absurd (by simp [hij]) hne, fun i => by simp⟩
  | mul x y _ _ hx hy =>
    have e : ((x * y : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) =
        (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) * y := rfl
    rw [e]
    exact pat_mul hx.1 hy.1 hx.2 hy.2

lemma comm_identity {A : Type*} [Ring A] (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
    (hFE : F * E = 0) : (1 + E) * (1 + F) * (1 + -E) * (1 + -F) = 1 + E * F := by
  have h1 : E * F * E = 0 := by rw [mul_assoc, hFE, mul_zero]
  have h2 : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_neg, neg_mul, hEE, hFF, hFE, h1, h2,
    add_zero]
  abel

/-- `t_{ij}(c) ∈ UL S` when `i < j` and every colour of `(i, j]` is in `S`. -/
lemma transvection_mem_UL {S : Finset ℕ} :
    ∀ (k : ℕ) (i j : Fin (d + 1)) (c : F), (j : ℕ) = i + k + 1 →
      (∀ c' : ℕ, (i : ℕ) < c' → c' ≤ j → c' ∈ S) →
      ∀ g : SLd d F, (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i j c →
        g ∈ UL d F S := by
  intro k
  induction k with
  | zero =>
    intro i j c hj hS g hg
    exact Subgroup.subset_closure ⟨c, i, j, hS j (by omega) le_rfl, by omega, by omega, hg⟩
  | succ k ih =>
    intro i j c hj hS g hg
    let m : Fin (d + 1) := ⟨i + k + 1, by omega⟩
    have him : i ≠ m := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hmj : m ≠ j := fun h => by
      have := congrArg Fin.val h; simp only [m] at this; omega
    have hij : i ≠ j := fun h => by subst h; omega
    let e1 : SLd d F := ⟨transvection i m c, det_transvection_of_ne _ _ him _⟩
    let e2 : SLd d F := ⟨transvection m j 1, det_transvection_of_ne _ _ hmj _⟩
    let e3 : SLd d F := ⟨transvection i m (-c), det_transvection_of_ne _ _ him _⟩
    let e4 : SLd d F := ⟨transvection m j (-1), det_transvection_of_ne _ _ hmj _⟩
    have h1 : e1 ∈ UL d F S := ih i m c (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e1 rfl
    have h3 : e3 ∈ UL d F S := ih i m (-c) (by simp [m]) (fun c' h1 h2 => hS c' h1 (by
      simp [m] at h2; omega)) e3 rfl
    have h2 : e2 ∈ UL d F S := Subgroup.subset_closure
      ⟨1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have h4 : e4 ∈ UL d F S := Subgroup.subset_closure
      ⟨-1, m, j, hS j (by omega) le_rfl, by omega, by simp only [m]; omega, rfl⟩
    have hprod : g = e1 * e2 * e3 * e4 := by
      apply Subtype.ext
      show (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = transvection i m c * transvection m j 1 *
        transvection i m (-c) * transvection m j (-1)
      rw [hg]
      simp only [transvection]
      have hn1 : Matrix.single i m (-c) = -Matrix.single i m c := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      have hn2 : Matrix.single m j (-1 : F) = -Matrix.single m j 1 := by
        ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
      rw [hn1, hn2, comm_identity _ _ (ss0 (Ne.symm him) _ _) (ss0 (Ne.symm hmj) _ _)
        (ss0 (Ne.symm hij) _ _), single_mul_single_same, mul_one]
    rw [hprod]
    exact mul_mem (mul_mem (mul_mem h1 h2) h3) h4

lemma det_of_pat {S : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (h : Pat S M)
    (hd : Diag1 M) : M.det = 1 := by
  have hU : M.IsUpperTriangular := fun i j hij => h.lower hij
  rw [Matrix.det_of_isUpperTriangular hU]
  exact Finset.prod_eq_one fun i _ => hd i

/-- The `SL` element of a unitriangular matrix. -/
noncomputable def mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : SLd d F := ⟨M, det_of_pat h hd⟩

@[simp] lemma coe_mkSL (S : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) (h : Pat S M)
    (hd : Diag1 M) : ((mkSL S M h hd : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = M := rfl

/-- A unitriangular `SL` element with support in `S`-runs lies in `UL S`. -/
theorem mem_UL_of_pat {S : Finset ℕ} :
    ∀ g : SLd d F, Pat (S : Set ℕ) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → g ∈ UL d F S := by
  intro g
  generalize hN : (Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) =>
    p.1 ≠ p.2 ∧ (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0)).card = N
  induction N using Nat.strong_induction_on generalizing g with
  | _ N ih =>
    intro hg hdg
    set Mg := (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hMg
    set Sx := Finset.univ.filter
      (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧ Mg p.1 p.2 ≠ 0) with hSx
    by_cases hne : Sx.Nonempty
    · obtain ⟨⟨a, b⟩, hp, hmin⟩ := Sx.exists_min_image (fun p => p.2) hne
      simp only [hSx, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hab, hrun⟩ := hg a b hp.1 hp.2
      set c := Mg a b with hc
      have hcol : ∀ i, i ≠ a → Mg i a = 0 := by
        intro i hi
        by_contra h
        have := hmin (i, a) (by simp [hSx, hi, h])
        exact absurd hab (not_lt.2 this)
      have hab' : a ≠ b := ne_of_lt hab
      let t : SLd d F := ⟨transvection a b (-c), det_transvection_of_ne _ _ hab' _⟩
      let ti : SLd d F := ⟨transvection a b c, det_transvection_of_ne _ _ hab' _⟩
      have hti : ti ∈ UL d F S := transvection_mem_UL ((b : ℕ) - a - 1) a b c (by omega)
        (fun c' h1 h2 => hrun c' h1 h2) ti rfl
      have hgt_mat : ∀ i j, ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
          if i = a ∧ j = b then 0 else Mg i j := by
        intro i j
        show (Mg * transvection a b (-c)) i j = _
        rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
        simp only [Matrix.single_apply, mul_ite, mul_zero]
        rw [Finset.sum_eq_single a]
        · by_cases hj : j = b
          · subst hj
            by_cases hi : i = a
            · subst hi; simp [hdg i, hc]
            · simp [hcol i hi, hi]
          · simp [Ne.symm hj, hj]
        · intro k _ hk; simp [Ne.symm hk]
        · simp
      have htti : t * ti = 1 := by
        apply Subtype.ext
        show transvection a b (-c) * transvection a b c = 1
        rw [tv_mul a b hab']; simp [transvection]
      have hg_eq : g = (g * t) * ti := by rw [mul_assoc, htti, mul_one]
      rw [hg_eq]
      refine mul_mem ?_ hti
      have hS' : Finset.univ.filter (fun p : Fin (d + 1) × Fin (d + 1) => p.1 ≠ p.2 ∧
          ((g * t : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) p.1 p.2 ≠ 0) =
          Sx.erase (a, b) := by
        ext ⟨i, j⟩
        simp only [hgt_mat i j, hSx, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, ne_eq, Prod.mk.injEq]
        by_cases h : i = a ∧ j = b
        · simp [h]
        · simp [h]
      refine ih _ ?_ (g * t) rfl ?_ ?_
      · rw [hS', ← hN]
        exact Finset.card_erase_lt_of_mem (by simpa [hSx, hp.1] using hp.2)
      · intro i j hij hne'
        rw [hgt_mat] at hne'
        split_ifs at hne' with h
        · exact absurd rfl hne'
        · exact hg i j hij hne'
      · intro i
        rw [hgt_mat]
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hab'
        · exact hdg i
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : g = 1 := by
        apply Subtype.ext
        ext i j
        show Mg i j = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j
        rw [Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp [hdg i]
        · simp only [hij, if_false]
          by_contra h
          have : (i, j) ∈ Sx := by simp [hSx, hij, h]
          rw [hne] at this
          simp at this
      rw [this]; exact one_mem _

section Coset

variable {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι] (H : ι → Subgroup G)

lemma chamber_exists (g : G) : ∃ τ ∈ (cosetComplex G H).tops,
    ∀ i, (⟨i, (g : G ⧸ H i)⟩ : Σ i, G ⧸ H i) ∈ τ := by
  unfold cosetComplex
  simp only
  rw [dif_pos ‹Finite G›]
  exact ⟨_, Finset.mem_image.2 ⟨g, @Finset.mem_univ _ (Fintype.ofFinite G) g, rfl⟩,
    fun i => Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

lemma vert_mem (g : G) (i : ι) :
    (⟨i, (g : G ⧸ H i)⟩ : Σ i, G ⧸ H i) ∈ (cosetComplex G H).vertices := by
  obtain ⟨τ, hτ, hmem⟩ := chamber_exists H g
  unfold WComplex.vertices
  simp only [Finset.mem_biUnion, id]
  exact ⟨τ, hτ, hmem i⟩

omit [Finite G] [Fintype ι] in
lemma face_of_mem {V : Type*} (X : WComplex V) {τ : Finset V} (hτ : τ ∈ X.tops) {u v : V}
    (hu : u ∈ τ) (hv : v ∈ τ) : X.IsFace {u, v} :=
  ⟨τ, hτ, by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv⟩

lemma face_pair (g : G) (i j : ι) : ∃ τ ∈ (cosetComplex G H).tops,
    (⟨i, (g : G ⧸ H i)⟩ : Σ i, G ⧸ H i) ∈ τ ∧ (⟨j, (g : G ⧸ H j)⟩ : Σ i, G ⧸ H i) ∈ τ := by
  obtain ⟨τ, hτ, hmem⟩ := chamber_exists H g
  exact ⟨τ, hτ, hmem i, hmem j⟩

omit [Finite G] [Fintype ι] in
lemma path_cons {V : Type*} (X : WComplex V) {u v w : V} {P : List V} (hP : X.IsPathFrom v w P)
    (huv : u ≠ v) (hf : X.IsFace {u, v}) (hu : u ∈ X.vertices) :
    X.IsPathFrom u w (u :: P) := by
  obtain ⟨⟨hne, hvert, hch⟩, hhead, hlast⟩ := hP
  obtain ⟨p, ps⟩ := P
  · exact absurd rfl hne
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hhead
  refine ⟨⟨List.cons_ne_nil _ _, ?_, ?_⟩, rfl, ?_⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hu
    · exact hvert x hx
  · exact List.IsChain.cons_cons ⟨huv, hf⟩ hch
  · rw [List.getLast?_cons_cons]; exact hlast

omit [Finite G] [Fintype ι] in
lemma path_single {V : Type*} (X : WComplex V) {u : V} (hu : u ∈ X.vertices) :
    X.IsPathFrom u u [u] :=
  ⟨⟨List.cons_ne_nil _ _, by simpa using hu, List.isChain_singleton _⟩, rfl, rfl⟩

omit [Finite G] [Fintype ι] in
lemma vert_eq {i : ι} {x h : G} (hh : h ∈ H i) :
    (⟨i, ((x * h : G) : G ⧸ H i)⟩ : Σ i, G ⧸ H i) = ⟨i, (x : G ⧸ H i)⟩ := by
  congr 1
  rw [QuotientGroup.eq]
  simpa using inv_mem hh

lemma walk (L : List (ι × G)) (hL : ∀ p ∈ L, p.2 ∈ H p.1) :
    ∀ (x : G) (A C : ι), ∃ P, (cosetComplex G H).IsPathFrom ⟨A, (x : G ⧸ H A)⟩
      ⟨C, ((x * (L.map Prod.snd).prod : G) : G ⧸ H C)⟩ P ∧ P.length ≤ L.length + 2 := by
  induction L with
  | nil =>
    intro x A C
    simp only [List.map_nil, List.prod_nil, mul_one, List.length_nil]
    by_cases hAC : (⟨A, (x : G ⧸ H A)⟩ : Σ i, G ⧸ H i) = ⟨C, (x : G ⧸ H C)⟩
    · refine ⟨[⟨A, (x : G ⧸ H A)⟩], ?_, by simp⟩
      rw [← hAC]; exact path_single _ (vert_mem H x A)
    · obtain ⟨τ, hτ, h1, h2⟩ := face_pair H x A C
      exact ⟨_, path_cons _ (path_single _ (vert_mem H x C)) hAC (face_of_mem _ hτ h1 h2)
        (vert_mem H x A), by simp⟩
  | cons p L ih =>
    intro x A C
    obtain ⟨D, h⟩ := p
    have hh : h ∈ H D := hL (D, h) (by simp)
    obtain ⟨P, hP, hlen⟩ := ih (fun q hq => hL q (by simp [hq])) (x * h) D C
    rw [vert_eq H hh] at hP
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [← mul_assoc]
    by_cases hAD : (⟨A, (x : G ⧸ H A)⟩ : Σ i, G ⧸ H i) = ⟨D, (x : G ⧸ H D)⟩
    · exact ⟨P, by rw [hAD]; exact hP, by omega⟩
    · obtain ⟨τ, hτ, h1, h2⟩ := face_pair H x A D
      exact ⟨_, path_cons _ hP hAD (face_of_mem _ hτ h1 h2) (vert_mem H x A), by simp; omega⟩

/-- Bounded generation by the `H_i` bounds the diameter of the coset complex. -/
theorem diam_le_of_gen (N : ℕ)
    (hgen : ∀ g : G, ∃ L : List (ι × G), L.length ≤ N ∧ (∀ p ∈ L, p.2 ∈ H p.1) ∧
      (L.map Prod.snd).prod = g) :
    (cosetComplex G H).diam ≤ ((N + 1 : ℕ) : ℕ∞) := by
  refine iSup₂_le fun u _ => iSup₂_le fun v _ => ?_
  obtain ⟨A, qa⟩ := u
  obtain ⟨B, qb⟩ := v
  obtain ⟨xa, rfl⟩ := QuotientGroup.mk_surjective qa
  obtain ⟨xb, rfl⟩ := QuotientGroup.mk_surjective qb
  obtain ⟨L, hlen, hL, hprod⟩ := hgen (xa⁻¹ * xb)
  obtain ⟨P, hP, hPlen⟩ := walk H L hL xa A B
  rw [hprod, mul_inv_cancel_left] at hP
  refine iInf₂_le_of_le P hP ?_
  exact_mod_cast (show P.length - 1 ≤ N + 1 by omega)

end Coset

section Bins

variable {J : Finset ℕ}

lemma relabel_lt (j₀ c : ℕ) : relabel d j₀ c < d + 1 := Nat.mod_lt _ (by omega)

lemma relabel_inj {j₀ c c' : ℕ} (hj : j₀ ≤ d) (hc : c < d + 1) (hc' : c' < d + 1)
    (h : relabel d j₀ c = relabel d j₀ c') : c = c' := by
  unfold relabel at h
  have e1 : c + (d + 1) - j₀ = c + (d + 1 - j₀) := by omega
  have e2 : c' + (d + 1) - j₀ = c' + (d + 1 - j₀) := by omega
  rw [e1, e2] at h
  have : c ≡ c' [MOD d + 1] := Nat.ModEq.add_right_cancel' _ h
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this

lemma base_mem (hne : J.Nonempty) : base J ∈ J := by
  simp only [base, dif_pos hne]; exact J.min'_mem hne

lemma zero_mem_rl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) : 0 ∈ rl d J J := by
  refine Finset.mem_image.2 ⟨base J, base_mem hne, ?_⟩
  have := Finset.mem_range.1 (hJ (base_mem hne))
  unfold relabel
  rw [show base J + (d + 1) - base J = d + 1 by omega, Nat.mod_self]

lemma rl_lt {K : Finset ℕ} {c : ℕ} (hc : c ∈ rl d J K) : c < d + 1 := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hc; exact relabel_lt _ _

lemma card_rl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) : (rl d J J).card = J.card := by
  have hb := Finset.mem_range.1 (hJ (base_mem hne))
  refine Finset.card_image_of_injOn fun x hx y hy hxy => ?_
  exact relabel_inj (by omega) (Finset.mem_range.1 (hJ hx)) (Finset.mem_range.1 (hJ hy)) hxy

lemma len_sort (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) :
    ((rl d J J).sort (· ≤ ·)).length = J.card := by
  rw [Finset.length_sort, card_rl hne hJ]

lemma jAt_eq (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k : ℕ} (hk : k < J.card) :
    jAt d J k = ((rl d J J).sort (· ≤ ·))[k]'(by rw [len_sort hne hJ]; exact hk) := by
  simp only [jAt, if_pos hk]
  rw [List.getD_eq_getElem]

lemma jAt_card : jAt d J J.card = d + 1 := by simp [jAt]

lemma jAt_mem (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k : ℕ} (hk : k < J.card) :
    jAt d J k ∈ rl d J J := by
  rw [jAt_eq hne hJ hk, ← Finset.mem_sort (· ≤ ·)]; exact List.getElem_mem _

lemma jAt_le (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) (k : ℕ) : jAt d J k ≤ d + 1 := by
  by_cases hk : k < J.card
  · exact (rl_lt (jAt_mem hne hJ hk)).le
  · simp [jAt, hk]

lemma jAt_zero (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) : jAt d J 0 = 0 := by
  have h0 := zero_mem_rl hne hJ
  have hpos : 0 < J.card := Finset.card_pos.2 hne
  rw [jAt_eq hne hJ hpos]
  obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.1 ((Finset.mem_sort (· ≤ ·)).2 h0)
  have hle := (Finset.sortedLT_sort (rl d J J)).getElem_le_getElem_iff
    (hi := (by rw [len_sort hne hJ]; exact hpos : 0 < ((rl d J J).sort (· ≤ ·)).length))
    (hj := hi) |>.2 (Nat.zero_le i)
  omega

lemma jAt_lt_succ (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k : ℕ} (hk : k < J.card) :
    jAt d J k < jAt d J (k + 1) := by
  by_cases hk1 : k + 1 < J.card
  · rw [jAt_eq hne hJ hk, jAt_eq hne hJ hk1]
    exact (Finset.sortedLT_sort (rl d J J)).getElem_lt_getElem_iff.2 (by omega)
  · have : k + 1 = J.card := by omega
    rw [this, jAt_card]; exact rl_lt (jAt_mem hne hJ hk)

lemma jAt_mono (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k k' : ℕ} (hkk : k < k')
    (hk' : k' ≤ J.card) : jAt d J k < jAt d J k' := by
  induction k' with
  | zero => omega
  | succ k' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkk with h | h
    · exact (ih h (by omega)).trans (jAt_lt_succ hne hJ (by omega))
    · subst h; exact jAt_lt_succ hne hJ (by omega)

lemma not_between (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {k c : ℕ} (hk : k < J.card)
    (hc : c ∈ rl d J J) (hlt : jAt d J k < c) : jAt d J (k + 1) ≤ c := by
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 ((Finset.mem_sort (· ≤ ·)).2 hc)
  have hmc : m < J.card := by rw [len_sort hne hJ] at hm; exact hm
  have hkm : k < m := by
    rw [jAt_eq hne hJ hk] at hlt
    exact (Finset.sortedLT_sort (rl d J J)).getElem_lt_getElem_iff.1 hlt
  have hk1 : k + 1 < J.card := by omega
  rw [jAt_eq hne hJ hk1]
  exact (Finset.sortedLT_sort (rl d J J)).getElem_le_getElem_iff.2 (by omega)

lemma bin_not_rl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {ℓ c : ℕ} (hℓ : ℓ < J.card)
    (hc : c ∈ bin d J ℓ) : c ∉ rl d J J := by
  intro hmem
  simp only [bin, binLo, binHi, Finset.mem_Icc] at hc
  have := not_between hne hJ hℓ hmem (by omega)
  omega

lemma bin_sub_compl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {ℓ c : ℕ}
    (hℓ : ℓ < J.card) (hc : c ∈ bin d J ℓ) : c ∈ compl d J := by
  refine Finset.mem_sdiff.2 ⟨?_, bin_not_rl hne hJ hℓ hc⟩
  have := jAt_le hne hJ (ℓ + 1)
  simp only [bin, binLo, binHi, Finset.mem_Icc] at hc
  exact Finset.mem_range.2 (by omega)

lemma compl_cover (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {c : ℕ}
    (hc : c ∈ compl d J) : ∃ ℓ < J.card, c ∈ bin d J ℓ := by
  obtain ⟨hcr, hcn⟩ := Finset.mem_sdiff.1 hc
  have hcd := Finset.mem_range.1 hcr
  have hc0 : c ≠ 0 := fun h => hcn (h ▸ zero_mem_rl hne hJ)
  have hpos : 0 < J.card := Finset.card_pos.2 hne
  set A := (Finset.range J.card).filter (fun k => jAt d J k < c) with hA
  have hAne : A.Nonempty := ⟨0, by simp [hA, hpos, jAt_zero hne hJ]; omega⟩
  obtain ⟨ℓ, hℓA, hmax⟩ : ∃ ℓ ∈ A, ∀ k ∈ A, k ≤ ℓ :=
    ⟨A.max' hAne, A.max'_mem hAne, fun k hk => A.le_max' k hk⟩
  simp only [hA, Finset.mem_filter, Finset.mem_range] at hℓA
  refine ⟨ℓ, hℓA.1, ?_⟩
  have hnext : c < jAt d J (ℓ + 1) := by
    by_cases h1 : ℓ + 1 < J.card
    · have hge : c ≤ jAt d J (ℓ + 1) := by
        by_contra h
        have : ℓ + 1 ∈ A := by simp [hA, h1]; omega
        have := hmax _ this
        omega
      rcases lt_or_eq_of_le hge with h | h
      · exact h
      · exact absurd (h ▸ jAt_mem hne hJ h1) hcn
    · rw [show ℓ + 1 = J.card by omega, jAt_card]; omega
  simp only [bin, binLo, binHi, Finset.mem_Icc]
  omega

lemma lo_not_compl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {ℓ : ℕ} (hℓ : ℓ < J.card) :
    jAt d J ℓ ∉ compl d J := fun h => (Finset.mem_sdiff.1 h).2 (jAt_mem hne hJ hℓ)

lemma hi_not_compl (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {ℓ : ℕ}
    (hℓ : ℓ < J.card) : jAt d J (ℓ + 1) ∉ compl d J := by
  intro h
  obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 h
  by_cases hl : ℓ + 1 < J.card
  · exact h2 (jAt_mem hne hJ hl)
  · rw [show ℓ + 1 = J.card by omega, jAt_card] at h1; simp at h1

lemma bins_disjoint (hne : J.Nonempty) (hJ : J ⊆ Finset.range (d + 1)) {ℓ ℓ' c : ℕ}
    (hℓ : ℓ < J.card) (hℓ' : ℓ' < J.card) (h1 : c ∈ bin d J ℓ) (h2 : c ∈ bin d J ℓ') : ℓ = ℓ' := by
  simp only [bin, binLo, binHi, Finset.mem_Icc] at h1 h2
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with h | h
  · have := jAt_mono hne hJ (show ℓ < ℓ' + 0 + 1 - 1 + 0 by omega) (by omega : ℓ' ≤ J.card)
    rcases lt_or_eq_of_le (show ℓ + 1 ≤ ℓ' by omega) with h' | h'
    · have := jAt_mono hne hJ h' (by omega : ℓ' ≤ J.card); omega
    · subst h'; omega
  · rcases lt_or_eq_of_le (show ℓ' + 1 ≤ ℓ by omega) with h' | h'
    · have := jAt_mono hne hJ h' (by omega : ℓ ≤ J.card); omega
    · subst h'; omega

end Bins

section Restrict

/-- `M` restricted to the runs inside `W`. -/
noncomputable def res (W : Set ℕ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F :=
  fun i j => if i = j then 1 else
    if (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W) then M i j else 0

lemma res_pat {S W : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (hM : Pat S M) :
    Pat W (res W M) ∧ Diag1 (res W M) := by
  refine ⟨fun i j hij hne => ?_, fun i => by simp [res]⟩
  simp only [res, hij, if_false] at hne
  split_ifs at hne with h
  · exact ⟨(hM i j hij hne).1, h⟩
  · exact absurd rfl hne

lemma res_offdiag {W : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} {i j : Fin (d + 1)}
    (hij : i ≠ j) (hne : res W M i j ≠ 0) :
    M i j ≠ 0 ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W := by
  simp only [res, hij, if_false] at hne
  split_ifs at hne with h
  · exact ⟨hne, h⟩
  · exact absurd rfl hne

lemma res_split {S W₁ W₂ : Set ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} (hM : Pat S M)
    (dM : Diag1 M) (hdisj : Disjoint W₁ W₂)
    (hsep : ∀ i j : Fin (d + 1), i < j → (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) →
      (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₁) ∨ (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₂)) :
    res W₁ M * res W₂ M = M := by
  have key : ∀ i j k : Fin (d + 1), k ≠ i → k ≠ j → res W₁ M i k * res W₂ M k j = 0 := by
    intro i j k hki hkj
    by_contra h
    obtain ⟨h1, h1W⟩ := res_offdiag (Ne.symm hki) (left_ne_zero_of_mul h)
    obtain ⟨h2, h2W⟩ := res_offdiag hkj (right_ne_zero_of_mul h)
    obtain ⟨a1, a2⟩ := hM i k (Ne.symm hki) h1
    obtain ⟨b1, b2⟩ := hM k j hkj h2
    rcases hsep i j (a1.trans b1) (fun c hc1 hc2 => by
        by_cases hc : c ≤ (k : ℕ)
        · exact a2 c hc1 hc
        · exact b2 c (by omega) hc2) with hW | hW
    · exact Set.disjoint_left.1 hdisj (hW j (a1.trans b1) le_rfl) (h2W j b1 le_rfl)
    · exact Set.disjoint_left.1 hdisj (h1W k a1 le_rfl) (hW k a1 (le_of_lt b1))
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i (fun k _ hk => key i i k hk hk) (by simp)]
    simp [res, dM i]
  · rw [Finset.sum_eq_add i j hij (fun k _ hk => key i j k hk.1 hk.2) (by simp) (by simp)]
    have r1 : res W₁ M i i = 1 := by simp [res]
    have r2 : res W₂ M j j = 1 := by simp [res]
    rw [r1, r2, one_mul, mul_one]
    by_cases hM0 : M i j = 0
    · simp [res, hij, hM0]
    · obtain ⟨h1, h2⟩ := hM i j hij hM0
      rcases hsep i j h1 h2 with hW | hW
      · have : ¬ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₂ := fun h =>
          Set.disjoint_left.1 hdisj (hW j h1 le_rfl) (h j h1 le_rfl)
        simp only [res, hij, if_false, if_pos hW, if_neg this, zero_add]
      · have : ¬ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₁ := fun h =>
          Set.disjoint_left.1 hdisj (h j h1 le_rfl) (hW j h1 le_rfl)
        simp only [res, hij, if_false, if_pos hW, if_neg this, add_zero]

lemma pat_one_add {S : Set ℕ} (N : Matrix (Fin (d + 1)) (Fin (d + 1)) F)
    (h : ∀ i j, N i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S) :
    Pat S (1 + N) ∧ Diag1 (1 + N) := by
  refine ⟨fun i j hij hne => ?_, fun i => ?_⟩
  · simp only [Matrix.add_apply, Matrix.one_apply, hij, if_false, zero_add] at hne
    exact h i j hne
  · have : N i i = 0 := by by_contra hn; exact absurd (h i i hn).1 (lt_irrefl _)
    simp [this]

lemma zero_of_supp (X W : Matrix (Fin (d + 1)) (Fin (d + 1)) F)
    (h : ∀ a c b, X a c ≠ 0 → W c b ≠ 0 → False) : X * W = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1' : X a c = 0
  · simp [h1']
  · by_cases h2' : W c b = 0
    · simp [h2']
    · exact (h a c b h1' h2').elim

end Restrict

section BinSix

lemma pat_Icc_iff {a b : ℕ} {M : Matrix (Fin (d + 1)) (Fin (d + 1)) F} :
    Pat (↑(Finset.Icc a b) : Set ℕ) M ↔ Pat (Set.Icc a b) M := by
  rw [Finset.coe_Icc]

/-- Inside one bin `[a, b]`, every element is a product of six factors alternating between the
runs `[a, b - f - 1]` and `[a + f + 1, b]`, `f = ⌊(b - a)/5⌋`. -/
theorem bin_six (a b : ℕ) (ha : 1 ≤ a) (hb : b ≤ d) (hab : 100 < b - a) (M : SLd d F)
    (hM : Pat (Set.Icc a b) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F))
    (dM : Diag1 (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) :
    ∃ x₁ x₂ x₃ x₄ x₅ x₆ : SLd d F,
      (Pat (Set.Icc a (b - (b - a) / 5 - 1)) (x₁ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (x₁ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) ∧
      (Pat (Set.Icc (a + (b - a) / 5 + 1) b) (x₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (x₂ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) ∧
      (Pat (Set.Icc a (b - (b - a) / 5 - 1)) (x₃ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (x₃ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) ∧
      (Pat (Set.Icc (a + (b - a) / 5 + 1) b) (x₄ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (x₄ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) ∧
      (Pat (Set.Icc a (b - (b - a) / 5 - 1)) (x₅ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (x₅ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) ∧
      (Pat (Set.Icc (a + (b - a) / 5 + 1) b) (x₆ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (x₆ : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) ∧
      M = x₁ * x₂ * x₃ * x₄ * x₅ * x₆ := by
  set f := (b - a) / 5 with hfdef
  have hf5 : 5 * f ≤ b - a := by omega
  have hf20 : 20 ≤ f := by omega
  have hUL : ∀ g : SLd d F, Pat (Set.Icc a b) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → g ∈ UL d F (Finset.Icc a b) :=
    fun g hp hd => mem_UL_of_pat g (pat_Icc_iff.2 hp) hd
  have hpat : ∀ g : SLd d F, g ∈ UL d F (Finset.Icc a b) →
      Pat (Set.Icc a b) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) ∧
        Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) :=
    fun g hg => ⟨pat_Icc_iff.1 (pat_of_mem_UL hg).1, (pat_of_mem_UL hg).2⟩
  -- `h₁`: `M` on the run `[a, b - f - 1]`.
  obtain ⟨p1, d1⟩ := res_pat (W := Set.Icc a (b - f - 1)) hM
  let h1 := mkSL _ _ p1 d1
  have h1m : (h1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = res (Set.Icc a (b - f - 1)) M := rfl
  have hsub1 : Set.Icc a (b - f - 1) ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl (by omega)
  have hsub2 : Set.Icc (a + f + 1) b ⊆ Set.Icc a b := Set.Icc_subset_Icc (by omega) le_rfl
  have h1UL : h1 ∈ UL d F (Finset.Icc a b) := hUL h1 (h1m ▸ p1.mono hsub1) (h1m ▸ d1)
  have hMUL : M ∈ UL d F (Finset.Icc a b) := hUL M hM dM
  let Y := h1⁻¹ * M
  obtain ⟨pY, dY⟩ := hpat Y (mul_mem (inv_mem h1UL) hMUL)
  have hcolM : ∀ i j : Fin (d + 1), ((j : ℕ) ≤ b - f - 1 ∨ b < j) →
      (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
        (h1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j := by
    intro i j hj
    rw [h1m]
    simp only [res]
    by_cases hij : i = j
    · subst hij; simp [dM i]
    · rw [if_neg hij]
      split_ifs with hc
      · rfl
      · by_contra hne
        obtain ⟨hlt, hrun⟩ := hM i j hij hne
        apply hc
        intro c hc1 hc2
        have := hrun c hc1 hc2
        have hj' := hrun j hlt le_rfl
        simp only [Set.mem_Icc] at this hj' ⊢
        omega
  have hY : ∀ i j : Fin (d + 1), ((j : ℕ) ≤ b - f - 1 ∨ b < j) →
      (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j = if i = j then 1 else 0 := by
    intro i j hj
    have : (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j =
        ((h1⁻¹ * h1 : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j := by
      show ((h1⁻¹ : SLd d F) * (M : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) i j =
        ((h1⁻¹ : SLd d F) * (h1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F)) i j
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun c _ => by rw [hcolM c j hj]
    rw [this, inv_mul_cancel]
    show (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j = _
    rw [Matrix.one_apply]
  set Ym := (Y : Matrix (Fin (d + 1)) (Fin (d + 1)) F) with hYm
  -- The corner `C` of `Y`.
  let C : Matrix (Fin (d + 1)) (Fin (d + 1)) F := fun i j =>
    if (i : ℕ) < a + f ∧ b - f ≤ (j : ℕ) ∧ (j : ℕ) ≤ b then Ym i j else 0
  have hCs : ∀ i j, C i j ≠ 0 → ((i : ℕ) < a + f ∧ b - f ≤ (j : ℕ) ∧ (j : ℕ) ≤ b) ∧
      Ym i j ≠ 0 := by
    intro i j h; simp only [C] at h; split_ifs at h with h'
    · exact ⟨h', h⟩
    · exact absurd rfl h
  have hCpat : ∀ (N : Matrix (Fin (d + 1)) (Fin (d + 1)) F), (∀ i j, N i j ≠ 0 → C i j ≠ 0) →
      ∀ i j, N i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ Set.Icc a b := by
    intro N hN i j hne
    obtain ⟨⟨h1', h2', -⟩, hy⟩ := hCs i j (hN i j hne)
    have hij : i ≠ j := fun h => by subst h; omega
    exact pY i j hij hy
  obtain ⟨pZ, dZ⟩ := pat_one_add (S := Set.Icc a b) C (hCpat C fun _ _ h => h)
  obtain ⟨pZi, dZi⟩ := pat_one_add (S := Set.Icc a b) (-C)
    (hCpat (-C) fun i j h => by simpa using h)
  have hCC : C * C = 0 := zero_of_supp C C fun a' c b' h1' h2' => by
    have := (hCs a' c h1').1; have := (hCs c b' h2').1; omega
  have hYC : Ym * C = C := by
    ext i j
    simp only [Matrix.mul_apply]
    have : ∀ k, Ym i k * C k j = if i = k then C k j else 0 := by
      intro k
      by_cases h' : C k j = 0
      · simp [h']
      · have := (hCs k j h').1
        have hk := hY i k (Or.inl (by omega))
        rw [hk]
        split_ifs <;> simp
    simp_rw [this]
    simp
  let Z := mkSL _ _ pZ dZ
  let Zi := mkSL _ _ pZi dZi
  have hZiZ : Zi * Z = 1 := by
    apply Subtype.ext
    show (1 + -C) * (1 + C) = 1
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.neg_mul, hCC]
    abel
  let h2 := Y * Zi
  have h2m : (h2 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = Ym - C := by
    show Ym * (1 + -C) = Ym - C
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, hYC, sub_eq_add_neg]
  have p2 : Pat (Set.Icc (a + f + 1) b) (h2 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
    intro i j hij hne
    rw [h2m, Matrix.sub_apply] at hne
    by_cases hj : (j : ℕ) ≤ b - f - 1 ∨ b < j
    · have hc0 : C i j = 0 := by
        by_contra h; have := (hCs i j h).1; omega
      rw [hY i j hj, if_neg hij, hc0] at hne; simp at hne
    · by_cases hi : (i : ℕ) < a + f
      · have : C i j = Ym i j := by simp only [C]; rw [if_pos ⟨hi, by omega, by omega⟩]
        rw [this, sub_self] at hne; exact absurd rfl hne
      · have hc0 : C i j = 0 := by
          by_contra h; have := (hCs i j h).1; omega
        rw [hc0, sub_zero] at hne
        obtain ⟨hlt, hrun⟩ := pY i j hij hne
        refine ⟨hlt, fun c hc1 hc2 => ?_⟩
        have := hrun c hc1 hc2
        simp only [Set.mem_Icc] at this ⊢
        omega
  have d2 : Diag1 (h2 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
    intro i
    rw [h2m, Matrix.sub_apply, dY i]
    have : C i i = 0 := by by_contra h; have := (hCs i i h).1; omega
    rw [this, sub_zero]
  -- The commutator.
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) F := fun i c =>
    if a ≤ (i : ℕ) + 1 ∧ (i : ℕ) < a + f ∧ (c : ℕ) = i + f + 1 then 1 else 0
  let B : Matrix (Fin (d + 1)) (Fin (d + 1)) F := fun c j =>
    if a + f ≤ (c : ℕ) ∧ (c : ℕ) ≤ a + 2 * f ∧ b - f ≤ (j : ℕ) ∧ (j : ℕ) ≤ b then
      Ym ⟨(c : ℕ) - f - 1, by omega⟩ j else 0
  have hAs : ∀ i c, A i c ≠ 0 → a ≤ (i : ℕ) + 1 ∧ (i : ℕ) < a + f ∧ (c : ℕ) = i + f + 1 := by
    intro i c h; simp only [A] at h; split_ifs at h with h'; exact h'; exact absurd rfl h
  have hBs : ∀ c j, B c j ≠ 0 →
      a + f ≤ (c : ℕ) ∧ (c : ℕ) ≤ a + 2 * f ∧ b - f ≤ (j : ℕ) ∧ (j : ℕ) ≤ b := by
    intro c j h; simp only [B] at h; split_ifs at h with h'; exact h'; exact absurd rfl h
  have hApat : ∀ (N : Matrix (Fin (d + 1)) (Fin (d + 1)) F), (∀ i j, N i j ≠ 0 → A i j ≠ 0) →
      ∀ i j, N i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ Set.Icc a (b - f - 1) := by
    intro N hN i j hne
    obtain ⟨h1', h2', h3'⟩ := hAs i j (hN i j hne)
    refine ⟨Fin.lt_def.2 (by omega), fun c hc1 hc2 => ?_⟩
    simp only [Set.mem_Icc]; omega
  have hBpat : ∀ (N : Matrix (Fin (d + 1)) (Fin (d + 1)) F), (∀ i j, N i j ≠ 0 → B i j ≠ 0) →
      ∀ i j, N i j ≠ 0 → i < j ∧ ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ Set.Icc (a + f + 1) b := by
    intro N hN i j hne
    obtain ⟨h1', h2', h3', h4'⟩ := hBs i j (hN i j hne)
    refine ⟨Fin.lt_def.2 (by omega), fun c hc1 hc2 => ?_⟩
    simp only [Set.mem_Icc]; omega
  obtain ⟨px, dx⟩ := pat_one_add A (hApat A fun _ _ h => h)
  obtain ⟨pxi, dxi⟩ := pat_one_add (-A) (hApat (-A) fun i j h => by simpa using h)
  obtain ⟨py, dy⟩ := pat_one_add B (hBpat B fun _ _ h => h)
  obtain ⟨pyi, dyi⟩ := pat_one_add (-B) (hBpat (-B) fun i j h => by simpa using h)
  have hAA : A * A = 0 := zero_of_supp A A fun a' c b' h1' h2' => by
    have := hAs a' c h1'; have := hAs c b' h2'; omega
  have hBB : B * B = 0 := zero_of_supp B B fun a' c b' h1' h2' => by
    have := hBs a' c h1'; have := hBs c b' h2'; omega
  have hBA : B * A = 0 := zero_of_supp B A fun a' c b' h1' h2' => by
    have := hBs a' c h1'; have := hAs c b' h2'; omega
  have hAB : A * B = C := by
    ext i j
    simp only [Matrix.mul_apply]
    by_cases hi : a ≤ (i : ℕ) + 1 ∧ (i : ℕ) < a + f
    · rw [Finset.sum_eq_single ⟨(i : ℕ) + f + 1, by omega⟩]
      · have hA1 : A i ⟨(i : ℕ) + f + 1, by omega⟩ = 1 := by
          simp [A, hi.1, hi.2]
        rw [hA1, one_mul]
        simp only [B, C]
        by_cases hj : b - f ≤ (j : ℕ) ∧ (j : ℕ) ≤ b
        · rw [if_pos ⟨by show a + f ≤ (i : ℕ) + f + 1; omega,
            by show (i : ℕ) + f + 1 ≤ a + 2 * f; omega, hj⟩, if_pos ⟨hi.2, hj⟩]
          congr 1; apply Fin.ext; show (i : ℕ) + f + 1 - f - 1 = i; omega
        · rw [if_neg (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), if_neg (fun h => hj h.2)]
      · intro c _ hc
        have : A i c = 0 := by
          by_contra h; exact hc (Fin.ext (by simp [(hAs i c h).2.2]))
        simp [this]
      · simp
    · have h0 : ∀ c, A i c = 0 := fun c => by
        by_contra h; have := hAs i c h; exact hi ⟨this.1, this.2.1⟩
      simp only [h0, zero_mul, Finset.sum_const_zero]
      symm
      by_contra h
      obtain ⟨⟨h1', h2', h3'⟩, hy⟩ := hCs i j h
      have hij : i ≠ j := fun e => by subst e; omega
      have := (pY i j hij hy).2 ((i : ℕ) + 1) (by omega) (by omega)
      simp only [Set.mem_Icc] at this
      exact hi ⟨by omega, h1'⟩
  let x := mkSL _ _ px dx
  let xi := mkSL _ _ pxi dxi
  let y := mkSL _ _ py dy
  let yi := mkSL _ _ pyi dyi
  have hcomm : xi * yi * x * y = Z := by
    apply Subtype.ext
    show (1 + -A) * (1 + -B) * (1 + A) * (1 + B) = 1 + C
    have := comm_identity (-A) (-B) (by rw [neg_mul_neg, hAA]) (by rw [neg_mul_neg, hBB])
      (by rw [neg_mul_neg, hBA])
    rw [neg_neg, neg_neg, neg_mul_neg, hAB] at this
    exact this
  refine ⟨h1, h2, xi, yi, x, y, ⟨h1m ▸ p1, h1m ▸ d1⟩, ⟨p2, d2⟩, ⟨pxi, dxi⟩, ⟨pyi, dyi⟩,
    ⟨px, dx⟩, ⟨py, dy⟩, ?_⟩
  have : M = h1 * Y := by simp [Y]
  rw [this, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  congr 1
  have e2 : Y = h2 * Z := by simp only [h2]; rw [mul_assoc, hZiZ, mul_one]
  rw [e2, ← hcomm]
  group

end BinSix

section Assemble

variable (F) in
/-- Products over bins: a `UL`-element supported on the bins of `Λ` is a product of at most
`6 |Λ|` elements of the subgroups `H_K`. -/
theorem assemble {I : Finset (Finset ℕ)} {J : Finset ℕ} (hne : J.Nonempty)
    (hJ : J ⊆ Finset.range (d + 1))
    (hA : ∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → 100 < binHi d J ℓ - binLo d J ℓ)
    (hB : ∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → ∃ K ∈ I.erase J, ∀ c ∈ rl d J K,
        c ∈ bin d J ℓ → c ≤ binLo d J ℓ + (binHi d J ℓ - binLo d J ℓ) / 5)
    (hC : ∀ ℓ < J.card, binLo d J ℓ ≤ binHi d J ℓ → ∃ K ∈ I.erase J, ∀ c ∈ rl d J K,
        c ∈ bin d J ℓ → binHi d J ℓ - (binHi d J ℓ - binLo d J ℓ) / 5 ≤ c)
    (Λ : Finset ℕ) :
    (∀ ℓ ∈ Λ, ℓ < J.card ∧ binLo d J ℓ ≤ binHi d J ℓ) →
    ∀ g : SLd d F, Pat (⋃ ℓ ∈ Λ, (bin d J ℓ : Set ℕ)) (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      ∃ L : List ({K // K ∈ I.erase J} × UL d F (compl d J)), L.length ≤ 6 * Λ.card ∧
        (∀ p ∈ L, p.2 ∈ linkH d F I J p.1) ∧
        (((L.map Prod.snd).prod : UL d F (compl d J)) : SLd d F) = g := by
  have hcompl : ∀ ℓ < J.card, ∀ c ∈ bin d J ℓ, c ∈ compl d J := fun ℓ hℓ c hc =>
    bin_sub_compl hne hJ hℓ hc
  have toG : ∀ x : SLd d F, ∀ (S : Set ℕ), S ⊆ ↑(compl d J) →
      Pat S (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
      Diag1 (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) → x ∈ UL d F (compl d J) :=
    fun x S hS hp hd => mem_UL_of_pat x (hp.mono hS) hd
  induction Λ using Finset.induction_on with
  | empty =>
    intro _ g hg dg
    refine ⟨[], by simp, by simp, ?_⟩
    simp only [List.map_nil, List.prod_nil, OneMemClass.coe_one]
    apply Subtype.ext
    ext i j
    show (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) F) i j = _
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [dg i]
    · rw [if_neg hij]
      by_contra h
      have := (hg i j hij (Ne.symm h)).2 (i + 1) (by omega)
        (Nat.succ_le_of_lt (hg i j hij (Ne.symm h)).1)
      simp at this
  | insert ℓ Λ hℓΛ ih =>
    intro hΛ g hg dg
    obtain ⟨hℓ, hlohi⟩ := hΛ ℓ (Finset.mem_insert_self _ _)
    set lo := binLo d J ℓ with hlo
    set hi := binHi d J ℓ with hhi
    have hlo1 : lo = jAt d J ℓ + 1 := rfl
    have hhi1 : hi = jAt d J (ℓ + 1) - 1 := rfl
    have hjle := jAt_le hne hJ (ℓ + 1)
    have hbin : (bin d J ℓ : Set ℕ) = Set.Icc lo hi := by simp [bin, hlo, hhi]
    set W₁ : Set ℕ := (bin d J ℓ : Set ℕ)
    set W₂ : Set ℕ := ⋃ ℓ' ∈ Λ, (bin d J ℓ' : Set ℕ)
    have hW : (⋃ ℓ' ∈ insert ℓ Λ, (bin d J ℓ' : Set ℕ)) = W₁ ∪ W₂ := by
      simp [W₁, W₂]
    rw [hW] at hg
    have hW₁c : W₁ ⊆ ↑(compl d J) := fun c hc => hcompl ℓ hℓ c hc
    have hW₂c : W₂ ⊆ ↑(compl d J) := by
      intro c hc
      simp only [W₂, Set.mem_iUnion] at hc
      obtain ⟨ℓ', hℓ', hc⟩ := hc
      exact hcompl ℓ' (hΛ ℓ' (Finset.mem_insert_of_mem hℓ')).1 c hc
    have hdisj : Disjoint W₁ W₂ := by
      rw [Set.disjoint_left]
      intro c h1 h2
      simp only [W₂, Set.mem_iUnion] at h2
      obtain ⟨ℓ', hℓ', h2⟩ := h2
      have := bins_disjoint hne hJ hℓ (hΛ ℓ' (Finset.mem_insert_of_mem hℓ')).1 h1 h2
      subst this; exact hℓΛ hℓ'
    have hsep : ∀ i j : Fin (d + 1), i < j →
        (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₁ ∪ W₂) →
        (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₁) ∨ (∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₂) := by
      intro i j _ hrun
      by_cases hall : ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ W₁
      · exact Or.inl hall
      · right
        push Not at hall
        obtain ⟨c₀, hc₀1, hc₀2, hc₀⟩ := hall
        intro c hc1 hc2
        rcases hrun c hc1 hc2 with h | h
        · exfalso
          rw [hbin, Set.mem_Icc] at h
          rw [hbin, Set.mem_Icc] at hc₀
          by_cases hlt : c₀ < lo
          · have hm := hrun (jAt d J ℓ) (by omega) (by omega)
            exact lo_not_compl hne hJ hℓ (hm.elim (fun h' => hW₁c h') (fun h' => hW₂c h'))
          · have hm := hrun (jAt d J (ℓ + 1)) (by omega) (by omega)
            exact hi_not_compl hne hJ hℓ (hm.elim (fun h' => hW₁c h') (fun h' => hW₂c h'))
        · exact h
    -- Split `g` into its bin-`ℓ` part and the rest.
    obtain ⟨p1, d1⟩ := res_pat (W := W₁) hg
    obtain ⟨p2, d2⟩ := res_pat (W := W₂) hg
    let g₁ := mkSL _ _ p1 d1
    let g₂ := mkSL _ _ p2 d2
    have hsplit : g = g₁ * g₂ := by
      apply Subtype.ext
      show (g : Matrix (Fin (d + 1)) (Fin (d + 1)) F) = res W₁ g * res W₂ g
      rw [res_split hg dg hdisj hsep]
    obtain ⟨L₂, hL₂len, hL₂, hL₂prod⟩ := ih (fun ℓ' h => hΛ ℓ' (Finset.mem_insert_of_mem h))
      g₂ p2 d2
    -- Six factors in bin `ℓ`.
    have hp1 : Pat (Set.Icc lo hi) (g₁ : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
      rw [← hbin]; exact p1
    obtain ⟨x₁, x₂, x₃, x₄, x₅, x₆, ⟨q1, e1⟩, ⟨q2, e2⟩, ⟨q3, e3⟩, ⟨q4, e4⟩, ⟨q5, e5⟩, ⟨q6, e6⟩,
      hx⟩ := bin_six lo hi (by omega) (by omega) (hA ℓ hℓ hlohi) g₁ hp1 d1
    obtain ⟨K₁, hK₁, hK₁c⟩ := hB ℓ hℓ hlohi
    obtain ⟨K₂, hK₂, hK₂c⟩ := hC ℓ hℓ hlohi
    have hP : Set.Icc lo (hi - (hi - lo) / 5 - 1) ⊆ ↑(compl d J \ rl d J K₂) := by
      intro c hc
      simp only [Set.mem_Icc] at hc
      have hcb : c ∈ bin d J ℓ := by simp [bin, ← hlo, ← hhi]; omega
      refine Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hcompl ℓ hℓ c hcb, fun hk => ?_⟩)
      have := hK₂c c hk hcb; omega
    have hQ : Set.Icc (lo + (hi - lo) / 5 + 1) hi ⊆ ↑(compl d J \ rl d J K₁) := by
      intro c hc
      simp only [Set.mem_Icc] at hc
      have hcb : c ∈ bin d J ℓ := by simp [bin, ← hlo, ← hhi]; omega
      refine Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hcompl ℓ hℓ c hcb, fun hk => ?_⟩)
      have := hK₁c c hk hcb; omega
    have hPc : ↑(compl d J \ rl d J K₂) ⊆ (↑(compl d J) : Set ℕ) :=
      Finset.coe_subset.2 Finset.sdiff_subset
    have hQc : ↑(compl d J \ rl d J K₁) ⊆ (↑(compl d J) : Set ℕ) :=
      Finset.coe_subset.2 Finset.sdiff_subset
    let y₁ : UL d F (compl d J) := ⟨x₁, toG x₁ _ (hP.trans hPc) q1 e1⟩
    let y₂ : UL d F (compl d J) := ⟨x₂, toG x₂ _ (hQ.trans hQc) q2 e2⟩
    let y₃ : UL d F (compl d J) := ⟨x₃, toG x₃ _ (hP.trans hPc) q3 e3⟩
    let y₄ : UL d F (compl d J) := ⟨x₄, toG x₄ _ (hQ.trans hQc) q4 e4⟩
    let y₅ : UL d F (compl d J) := ⟨x₅, toG x₅ _ (hP.trans hPc) q5 e5⟩
    let y₆ : UL d F (compl d J) := ⟨x₆, toG x₆ _ (hQ.trans hQc) q6 e6⟩
    let k₁ : {K // K ∈ I.erase J} := ⟨K₁, hK₁⟩
    let k₂ : {K // K ∈ I.erase J} := ⟨K₂, hK₂⟩
    have memP : ∀ (x : SLd d F) (hxG : x ∈ UL d F (compl d J)),
        Pat (Set.Icc lo (hi - (hi - lo) / 5 - 1)) (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
        Diag1 (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
        (⟨x, hxG⟩ : UL d F (compl d J)) ∈ linkH d F I J k₂ := by
      intro x hxG hp hd
      exact Subgroup.mem_subgroupOf.2 (mem_UL_of_pat x (hp.mono hP) hd)
    have memQ : ∀ (x : SLd d F) (hxG : x ∈ UL d F (compl d J)),
        Pat (Set.Icc (lo + (hi - lo) / 5 + 1) hi) (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
        Diag1 (x : Matrix (Fin (d + 1)) (Fin (d + 1)) F) →
        (⟨x, hxG⟩ : UL d F (compl d J)) ∈ linkH d F I J k₁ := by
      intro x hxG hp hd
      exact Subgroup.mem_subgroupOf.2 (mem_UL_of_pat x (hp.mono hQ) hd)
    refine ⟨[(k₂, y₁), (k₁, y₂), (k₂, y₃), (k₁, y₄), (k₂, y₅), (k₁, y₆)] ++ L₂, ?_, ?_, ?_⟩
    · rw [List.length_append, Finset.card_insert_of_notMem hℓΛ]; simp; omega
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
        · exact memP _ _ q1 e1
        · exact memQ _ _ q2 e2
        · exact memP _ _ q3 e3
        · exact memQ _ _ q4 e4
        · exact memP _ _ q5 e5
        · exact memQ _ _ q6 e6
      · exact hL₂ p hp
    · rw [List.map_append, List.prod_append, Subgroup.coe_mul, hL₂prod, hsplit, hx]
      simp [y₁, y₂, y₃, y₄, y₅, y₆, mul_assoc]

end Assemble

end PolySwap.KMS.Sol71

open PolySwap.KMS PolySwap.KMS.Sol71

theorem solution (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)) (hI : I ∈ disjointColorSets d r T) (hnice : IsNice d I)
    (J : Finset ℕ) (hJ : J ∈ I) :
    (linkY d F I J).diam ≤ ((6 * (r + 1) + 1 : ℕ) : ℕ∞) := by
  have hJmem : J ∈ (Finset.range (d + 1)).powersetCard (r + 1) := by
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    exact hI.1.1 hJ
  obtain ⟨hJsub, hJcard⟩ := Finset.mem_powersetCard.1 hJmem
  have hne : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨hA, hB, hC, -, -⟩ := hnice J hJ
  unfold linkY
  apply diam_le_of_gen
  intro g
  set Λ₀ := (Finset.range J.card).filter (fun ℓ => binLo d J ℓ ≤ binHi d J ℓ)
  have hΛ₀ : ∀ ℓ ∈ Λ₀, ℓ < J.card ∧ binLo d J ℓ ≤ binHi d J ℓ := by
    intro ℓ hℓ; simpa [Λ₀] using hℓ
  obtain ⟨pg, dg⟩ := pat_of_mem_UL g.2
  have pg' : Pat (⋃ ℓ ∈ Λ₀, (bin d J ℓ : Set ℕ))
      ((g : SLd d F) : Matrix (Fin (d + 1)) (Fin (d + 1)) F) := by
    refine pg.mono fun c hc => ?_
    obtain ⟨ℓ, hℓ, hcb⟩ := compl_cover hne hJsub hc
    simp only [Set.mem_iUnion]
    refine ⟨ℓ, ?_, hcb⟩
    simp only [Λ₀, Finset.mem_filter, Finset.mem_range]
    simp only [bin, Finset.mem_Icc] at hcb
    exact ⟨hℓ, by omega⟩
  obtain ⟨L, hlen, hL, hprod⟩ := assemble F hne hJsub hA hB hC Λ₀ hΛ₀ g pg' dg
  refine ⟨L, ?_, hL, Subtype.ext hprod⟩
  have : Λ₀.card ≤ r + 1 := by
    calc Λ₀.card ≤ (Finset.range J.card).card := Finset.card_filter_le _ _
      _ = r + 1 := by simp [hJcard]
  omega
