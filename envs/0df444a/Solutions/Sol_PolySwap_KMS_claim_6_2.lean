-- Prove2me | solution 1 for PolySwap.KMS.claim_6_2
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T10:07:46.102201+00:00
-- url     : https://prove2.me/submissions/261c214a-d168-4ec2-9a07-ce86e65e7d70

import Mathlib
import Definitions.Def_PolySwap_KMS_Complex
import Definitions.Def_PolySwap_KMS_Dehn
import Definitions.Def_PolySwap_KMS_KMSComplex

open Classical Matrix

namespace PolySwap.KMS.Sol62

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

section AreaCalc

variable {Sg : Type*}

/-- `l` is a product of conjugates of relators: the data witnessing `Area_R(w) ≤ |l|`. -/
def Valid (R : Set (FreeGroup Sg)) (w : FreeGroup Sg) (l : List (FreeGroup Sg × FreeGroup Sg)) :
    Prop :=
  (∀ p ∈ l, p.2 ∈ R ∨ p.2⁻¹ ∈ R) ∧ w = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod

lemma area_le {R : Set (FreeGroup Sg)} {w : FreeGroup Sg} {l} (h : Valid R w l) :
    area R w ≤ l.length :=
  iInf_le_of_le l (iInf_le_of_le h le_rfl)

lemma area_attained {R : Set (FreeGroup Sg)} {w : FreeGroup Sg} (h : area R w ≠ ⊤) :
    ∃ l, Valid R w l ∧ (l.length : ℕ∞) = area R w := by
  have hne : ∃ l, Valid R w l := by
    by_contra hc
    push Not at hc
    apply h
    simp only [area]
    exact le_antisymm le_top (le_iInf fun l => le_iInf fun hl => absurd hl (hc l))
  have : Nonempty {l // Valid R w l} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨l, hl⟩, hmin⟩ := csInf_mem (Set.range_nonempty
    (fun l : {l // Valid R w l} => (l.1.length : ℕ∞)))
  refine ⟨l, hl, ?_⟩
  simp only at hmin
  rw [hmin]
  apply le_antisymm
  · exact le_iInf fun l' => le_iInf fun hl' => csInf_le (OrderBot.bddBelow _) ⟨⟨l', hl'⟩, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨⟨l', hl'⟩, rfl⟩; exact area_le hl')

lemma area_one (R : Set (FreeGroup Sg)) : area R 1 = 0 :=
  le_antisymm (by simpa using area_le (R := R) (w := 1) (l := []) ⟨by simp, by simp⟩) bot_le

lemma area_mul_le (R : Set (FreeGroup Sg)) (a b : FreeGroup Sg) :
    area R (a * b) ≤ area R a + area R b := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  by_cases hb : area R b = ⊤
  · simp [hb]
  obtain ⟨la, ⟨ha1, ha2⟩, hla⟩ := area_attained ha
  obtain ⟨lb, ⟨hb1, hb2⟩, hlb⟩ := area_attained hb
  rw [← hla, ← hlb]
  have := area_le (R := R) (w := a * b) (l := la ++ lb)
    ⟨fun p hp => by
      rcases List.mem_append.1 hp with h | h
      · exact ha1 p h
      · exact hb1 p h,
     by rw [List.map_append, List.prod_append, ← ha2, ← hb2]⟩
  simpa using this

lemma area_conj_le (R : Set (FreeGroup Sg)) (a u : FreeGroup Sg) :
    area R (u⁻¹ * a * u) ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup Sg × FreeGroup Sg),
      u⁻¹ * (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod * u =
        ((l.map (fun p => (p.1 * u, p.2))).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih]; group
  have := area_le (R := R) (w := u⁻¹ * a * u) (l := l.map (fun p => (p.1 * u, p.2)))
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact h1 q hq,
     by rw [h2, key]⟩
  simpa using this

lemma area_inv_le (R : Set (FreeGroup Sg)) (a : FreeGroup Sg) : area R a⁻¹ ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup Sg × FreeGroup Sg),
      ((l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod)⁻¹ =
        (((l.map (fun p => (p.1, p.2⁻¹))).reverse).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, _root_.mul_inv_rev] at ih ⊢
      rw [ih]; group
  have := area_le (R := R) (w := a⁻¹) (l := (l.map (fun p => (p.1, p.2⁻¹))).reverse)
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hp)
      rcases h1 q hq with h | h
      · exact Or.inr (by simpa using h)
      · exact Or.inl h,
     by rw [h2, key]⟩
  simpa using this

lemma area_of_mem {R : Set (FreeGroup Sg)} {ρ : FreeGroup Sg} (h : ρ ∈ R) : area R ρ ≤ 1 := by
  simpa using area_le (R := R) (w := ρ) (l := [(1, ρ)]) ⟨by simp [h], by simp⟩

end AreaCalc

/-! ## Block factorisation of unitriangular matrices -/

abbrev Mat (d : ℕ) (F : Type*) := Matrix (Fin (d + 1)) (Fin (d + 1)) F

/-- Every colour of `(i, j]` lies in `S`. -/
def ColOK (S : Finset ℕ) (i j : Fin (d + 1)) : Prop := ∀ c : ℕ, (i : ℕ) < c → c ≤ j → c ∈ S

/-- `M` is a product of at most `n` elements of `U_S`, each supported on a block of size `k`. -/
def FactM (S : Finset ℕ) (k n : ℕ) (M : Mat d F) : Prop :=
  ∃ L : List (SLd d F), L.length ≤ n ∧
    (∀ x ∈ L, x ∈ UL d F S ∧ SupportedOnBlock d F (x : Mat d F) k) ∧
    ((L.prod : SLd d F) : Mat d F) = M

lemma FactM.mono {S : Finset ℕ} {k n m : ℕ} {M : Mat d F} (h : FactM S k n M) (hnm : n ≤ m) :
    FactM S k m M := by
  obtain ⟨L, h1, h2, h3⟩ := h; exact ⟨L, h1.trans hnm, h2, h3⟩

lemma FactM.one (S : Finset ℕ) (k n : ℕ) : FactM (d := d) (F := F) S k n 1 :=
  ⟨[], by simp, by simp, by simp⟩

lemma FactM.mul {S : Finset ℕ} {k n m : ℕ} {M N : Mat d F} (h1 : FactM S k n M)
    (h2 : FactM S k m N) : FactM S k (n + m) (M * N) := by
  obtain ⟨L1, a1, b1, c1⟩ := h1
  obtain ⟨L2, a2, b2, c2⟩ := h2
  refine ⟨L1 ++ L2, by simp; omega, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with h | h
    exacts [b1 x h, b2 x h]
  · rw [List.prod_append, ← c1, ← c2]; rfl

/-- The entries of `X` on the index pairs satisfying `E`. -/
noncomputable def restr (E : Fin (d + 1) → Fin (d + 1) → Prop) (X : Mat d F) : Mat d F :=
  Matrix.of fun i j => if E i j then X i j else 0

lemma restr_ne {E : Fin (d + 1) → Fin (d + 1) → Prop} {X : Mat d F} {i j : Fin (d + 1)}
    (h : restr E X i j ≠ 0) : E i j ∧ X i j ≠ 0 := by
  unfold restr at h
  simp only [Matrix.of_apply] at h
  split_ifs at h with hE
  · exact ⟨hE, h⟩
  · exact absurd rfl h

lemma restr_add (E : Fin (d + 1) → Fin (d + 1) → Prop) (X : Mat d F) :
    restr E X + restr (fun i j => ¬ E i j) X = X := by
  ext i j
  simp only [restr, Matrix.add_apply, Matrix.of_apply]
  split_ifs <;> simp_all

lemma one_add_split (Y Z : Mat d F) (h : Y * Z = 0) : (1 + Y) * (1 + Z) = 1 + (Y + Z) := by
  rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, h]; abel

lemma mul_win_zero (w : Fin (d + 1) → ℕ) (q : ℕ) (X Y : Mat d F)
    (hX : ∀ i k, X i k ≠ 0 → w k = q) (hY : ∀ k j, Y k j ≠ 0 → w k ≠ q) : X * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hx : X i k = 0
  · simp [hx]
  by_cases hy : Y k j = 0
  · simp [hy]
  exact absurd (hX _ _ hx) (hY _ _ hy)

/-- A unitriangular `1 + X` with `X` supported on two consecutive windows of width `h` is one
factor supported on a block of size `2h`. -/
lemma leaf (S : Finset ℕ) {h : ℕ} (hh : 0 < h) (P : ℕ) (X : Mat d F)
    (hX : ∀ i j, X i j ≠ 0 → (i : ℕ) < j ∧ ColOK S i j ∧ P ≤ (i : ℕ) / h ∧
      (i : ℕ) / h ≤ P + 1 ∧ P ≤ (j : ℕ) / h ∧ (j : ℕ) / h ≤ P + 1) :
    FactM S (2 * h) 1 (1 + X) := by
  have hdiag : Diag1 (1 + X) := fun i => by
    have : X i i = 0 := by
      by_contra hne; exact lt_irrefl _ (hX i i hne).1
    simp [this]
  have hpat : Pat (S : Set ℕ) (1 + X) := by
    intro i j hij hne
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, zero_add] at hne
    obtain ⟨h1, h2, -⟩ := hX i j hne
    exact ⟨Fin.lt_def.2 h1, fun c hc1 hc2 => by simpa using h2 c hc1 hc2⟩
  refine ⟨[mkSL _ (1 + X) hpat hdiag], by simp, ?_, by simp⟩
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  refine ⟨mem_UL_of_pat _ hpat hdiag, P * h, fun i j hout => ?_⟩
  rw [coe_mkSL, Matrix.add_apply, Matrix.one_apply]
  suffices X i j = 0 by simp [this]
  by_contra hne
  obtain ⟨-, -, h1, h2, h3, h4⟩ := hX i j hne
  apply hout
  rw [Nat.le_div_iff_mul_le hh] at h1 h3
  have h2' := (Nat.div_lt_iff_lt_mul hh).1 (Nat.lt_succ_of_le h2)
  have h4' := (Nat.div_lt_iff_lt_mul hh).1 (Nat.lt_succ_of_le h4)
  have e : (P + 1).succ * h = P * h + 2 * h := by rw [Nat.succ_eq_add_one]; ring
  rw [e] at h2' h4'
  exact ⟨h1, h2', h3, h4'⟩

/-- The factor count of the commutator recursion. -/
def fN : ℕ → ℕ
  | 0 => 1
  | t + 1 => 2 + 2 * fN t

lemma fN_mono : Monotone fN := monotone_nat_of_le_succ fun t => by simp only [fN]; omega

lemma fN_eq (t : ℕ) : fN t + 2 = 3 * 2 ^ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [fN, pow_succ]; omega

lemma lt_of_win {h i j : ℕ} (hw : i / h < j / h) : i < j := by
  by_contra hc
  exact absurd (Nat.div_le_div_right (not_lt.1 hc)) (not_le.2 hw)

lemma pair0 (S : Finset ℕ) {h : ℕ} (hh : 0 < h) (P : ℕ) (X : Mat d F)
    (hX : ∀ i j, X i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + 1) :
    FactM S (2 * h) 1 (1 + X) :=
  leaf S hh P X fun i j hne => by
    obtain ⟨h1, h2, h3⟩ := hX i j hne
    exact ⟨lt_of_win (h := h) (by omega), h1, by omega, by omega, by omega, by omega⟩

/-- A block `X` from window `P` to window `P + t + 1` factors into `fN t` adjacent-window factors,
by writing `1 + X = [1 + A, 1 + B]` with `A` a partial shift by `h` and `B` the shifted `X`. -/
lemma pair (S : Finset ℕ) {h : ℕ} (hh : 0 < h) : ∀ (t P : ℕ) (X : Mat d F),
    (∀ i j, X i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + t + 1) →
    FactM S (2 * h) (fN t) (1 + X) := by
  intro t
  induction t with
  | zero => intro P X hX; exact pair0 S hh P X fun i j hne => hX i j hne
  | succ t ih =>
    intro P X hX
    have hshift : ∀ i j, X i j ≠ 0 → (i : ℕ) + h < j := by
      intro i j hne
      obtain ⟨-, h2, h3⟩ := hX i j hne
      by_contra hc
      have := Nat.div_le_div_right (c := h) (not_lt.1 hc)
      rw [Nat.add_div_right _ hh] at this
      omega
    let A : Mat d F := Matrix.of fun i j => if (j : ℕ) = i + h ∧ ∃ j', X i j' ≠ 0 then 1 else 0
    let B : Mat d F := Matrix.of fun k j =>
      if hk : h ≤ (k : ℕ) then X ⟨k - h, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ j else 0
    have hAB : A * B = X := by
      ext i j
      rw [Matrix.mul_apply]
      by_cases hrow : ∃ j', X i j' ≠ 0
      · obtain ⟨j', hj'⟩ := hrow
        have hk : (i : ℕ) + h < d + 1 := lt_trans (hshift i j' hj') j'.isLt
        rw [Finset.sum_eq_single (⟨(i : ℕ) + h, hk⟩ : Fin (d + 1))]
        · have hex : ∃ j', X i j' ≠ 0 := ⟨j', hj'⟩
          simp [A, B, Matrix.of_apply, hex]
        · intro k _ hk'
          simp only [A, Matrix.of_apply]
          rw [if_neg, zero_mul]
          rintro ⟨hk'', -⟩
          exact hk' (Fin.ext hk'')
        · simp
      · push Not at hrow
        rw [hrow j]
        refine Finset.sum_eq_zero fun k _ => ?_
        simp only [A, Matrix.of_apply]
        rw [if_neg, zero_mul]
        rintro ⟨-, j', hj'⟩
        exact hj' (hrow j')
    have hA : ∀ i j, A i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + 1 := by
      intro i j hne
      simp only [A, Matrix.of_apply] at hne
      split_ifs at hne with hc
      · obtain ⟨hj, j', hj'⟩ := hc
        obtain ⟨h1, h2, -⟩ := hX i j' hj'
        have := hshift i j' hj'
        refine ⟨fun c hc1 hc2 => h1 c hc1 (by omega), h2, ?_⟩
        rw [hj, Nat.add_div_right _ hh, h2]
      · exact absurd rfl hne
    have hnA : ∀ i j, (-A) i j ≠ 0 → ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = P + 1 :=
      fun i j hne => hA i j (by simpa using hne)
    have hB : ∀ k j, B k j ≠ 0 →
        ColOK S k j ∧ (k : ℕ) / h = P + 1 ∧ (j : ℕ) / h = P + 1 + t + 1 := by
      intro k j hne
      simp only [B, Matrix.of_apply] at hne
      split_ifs at hne with hk
      · obtain ⟨h1, h2, h3⟩ := hX _ j hne
        simp only at h2
        refine ⟨fun c hc1 hc2 => h1 c (by simp only; omega) hc2, ?_, by omega⟩
        calc (k : ℕ) / h = ((k : ℕ) - h + h) / h := by rw [Nat.sub_add_cancel hk]
          _ = P + 1 := by rw [Nat.add_div_right _ hh, h2]
      · exact absurd rfl hne
    have hnB : ∀ k j, (-B) k j ≠ 0 →
        ColOK S k j ∧ (k : ℕ) / h = P + 1 ∧ (j : ℕ) / h = P + 1 + t + 1 :=
      fun i j hne => hB i j (by simpa using hne)
    have hAA : A * A = 0 := mul_win_zero (fun i => (i : ℕ) / h) (P + 1) A A
      (fun i k hne => (hA i k hne).2.2) (fun k j hne => by simp only [(hA k j hne).2.1]; omega)
    have hBB : B * B = 0 := mul_win_zero (fun i => (i : ℕ) / h) (P + 1 + t + 1) B B
      (fun i k hne => (hB i k hne).2.2) (fun k j hne => by simp only [(hB k j hne).2.1]; omega)
    have hBA : B * A = 0 := mul_win_zero (fun i => (i : ℕ) / h) (P + 1 + t + 1) B A
      (fun i k hne => (hB i k hne).2.2) (fun k j hne => by simp only [(hA k j hne).2.1]; omega)
    have hid : (1 + A) * (1 + B) * (1 + -A) * (1 + -B) = 1 + X := by
      rw [comm_identity A B hAA hBB hBA, hAB]
    rw [← hid]
    refine ((((pair0 S hh P A hA).mul (ih (P + 1) B hB)).mul (pair0 S hh P (-A) hnA)).mul
      (ih (P + 1) (-B) hnB)).mono ?_
    simp only [fN]; omega

lemma pairQ (S : Finset ℕ) {h : ℕ} (hh : 0 < h) (T P Q : ℕ) (X : Mat d F)
    (hX : ∀ i j, X i j ≠ 0 →
      ColOK S i j ∧ (i : ℕ) / h = P ∧ (j : ℕ) / h = Q ∧ P < Q ∧ Q ≤ P + T) :
    FactM S (2 * h) (fN T) (1 + X) := by
  by_cases hPQ : P < Q ∧ Q ≤ P + T
  · refine (pair S hh (Q - P - 1) P X fun i j hne => ?_).mono (fN_mono (by omega))
    obtain ⟨h1, h2, h3, -⟩ := hX i j hne
    exact ⟨h1, h2, by omega⟩
  · have : X = 0 := by
      ext i j; by_contra hne; exact hPQ (hX i j hne).2.2.2
    rw [this, add_zero]; exact FactM.one S _ _

/-- Peeling off one window (of the row or of the column, according to `key`) at a time. -/
lemma peel (S : Finset ℕ) (k c w0 : ℕ) (key : Fin (d + 1) → Fin (d + 1) → ℕ)
    (Φ : Mat d F → Prop)
    (hres : ∀ X E, Φ X → Φ (restr E X))
    (hzero : ∀ X top, Φ X → (∀ i j, X i j ≠ 0 → key i j ≤ top) →
      restr (fun i j => key i j = top) X * restr (fun i j => ¬ key i j = top) X = 0)
    (hleaf : ∀ X top, Φ X → (∀ i j, X i j ≠ 0 → key i j = top) → FactM S k c (1 + X)) :
    ∀ m (X : Mat d F), Φ X → (∀ i j, X i j ≠ 0 → w0 ≤ key i j ∧ key i j < w0 + m) →
      FactM S k (m * c) (1 + X) := by
  intro m
  induction m with
  | zero =>
    intro X _ hX
    have : X = 0 := by ext i j; by_contra hne; have := hX i j hne; omega
    rw [this, add_zero, zero_mul]; exact FactM.one S k 0
  | succ m ih =>
    intro X hΦ hX
    have heq : 1 + X = (1 + restr (fun i j => key i j = w0 + m) X) *
        (1 + restr (fun i j => ¬ key i j = w0 + m) X) := by
      rw [one_add_split _ _ (hzero X _ hΦ fun i j hne => by have := hX i j hne; omega),
        restr_add]
    rw [heq]
    refine ((hleaf _ (w0 + m) (hres X _ hΦ) fun i j hne => (restr_ne hne).1).mul
      (ih _ (hres X _ hΦ) fun i j hne => ?_)).mono (le_of_eq (by ring))
    obtain ⟨h1, h2⟩ := restr_ne hne
    have := hX i j h2
    exact ⟨this.1, by omega⟩

/-- Every `g ∈ U_S`, `S ⊆ [a, b]`, is a product of a bounded number of elements of `U_S`
supported on blocks of size `2h`. -/
theorem main (S : Finset ℕ) (a b h : ℕ) (hh : 0 < h) (hS : ∀ c ∈ S, a ≤ c ∧ c ≤ b)
    (g : SLd d F) (hg : g ∈ UL d F S) :
    FactM S (2 * h) ((b / h - (a - 1) / h + 1) + (b / h - (a - 1) / h + 1) *
      ((b / h - (a - 1) / h) * fN (b / h - (a - 1) / h))) (g : Mat d F) := by
  set w0 := (a - 1) / h
  set T := b / h - w0
  have hwin : ∀ i j : Fin (d + 1), (i : ℕ) < j → ColOK S i j →
      w0 ≤ (i : ℕ) / h ∧ (j : ℕ) / h ≤ w0 + T ∧ (i : ℕ) / h ≤ (j : ℕ) / h := by
    intro i j hij hc
    have h1 := hS _ (hc (i + 1) (by omega) (by omega))
    have h2 := hS _ (hc j hij le_rfl)
    have e1 : w0 ≤ (i : ℕ) / h := Nat.div_le_div_right (by omega)
    have e2 : (j : ℕ) / h ≤ b / h := Nat.div_le_div_right h2.2
    have e3 : (i : ℕ) / h ≤ (j : ℕ) / h := Nat.div_le_div_right hij.le
    exact ⟨e1, by omega, e3⟩
  have inner : ∀ Q (X : Mat d F), (∀ i j, X i j ≠ 0 →
      (i : ℕ) < j ∧ ColOK S i j ∧ (j : ℕ) / h = Q ∧ (i : ℕ) / h < Q) →
      FactM S (2 * h) (T * fN T) (1 + X) := by
    intro Q X hX
    refine peel S (2 * h) (fN T) w0 (fun i _ => (i : ℕ) / h)
      (fun X => ∀ i j, X i j ≠ 0 →
        (i : ℕ) < j ∧ ColOK S i j ∧ (j : ℕ) / h = Q ∧ (i : ℕ) / h < Q)
      (fun X E hΦ i j hne => hΦ i j (restr_ne hne).2) ?_ ?_ T X hX ?_
    · intro X top hΦ _
      apply mul_win_zero (fun i => (i : ℕ) / h) Q
      · intro i k hne; exact (hΦ i k (restr_ne hne).2).2.2.1
      · intro k j hne; have := hΦ k j (restr_ne hne).2; omega
    · intro X top hΦ hkey
      exact pairQ S hh T top Q X fun i j hne => by
        obtain ⟨h1, h2, h3, h4⟩ := hΦ i j hne
        have := hwin i j h1 h2
        have h5 := hkey i j hne
        try simp only at h5
        exact ⟨h2, h5, h3, by omega, by omega⟩
    · intro i j hne
      obtain ⟨h1, h2, h3, h4⟩ := hX i j hne
      have := hwin i j h1 h2
      omega
  have outer : ∀ X : Mat d F, (∀ i j, X i j ≠ 0 →
      (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h < (j : ℕ) / h) →
      FactM S (2 * h) ((T + 1) * (T * fN T)) (1 + X) := by
    intro X hX
    refine peel S (2 * h) (T * fN T) w0 (fun _ j => (j : ℕ) / h)
      (fun X => ∀ i j, X i j ≠ 0 → (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h < (j : ℕ) / h)
      (fun X E hΦ i j hne => hΦ i j (restr_ne hne).2) ?_ ?_ (T + 1) X hX ?_
    · intro X top hΦ hle
      apply mul_win_zero (fun i => (i : ℕ) / h) top
      · intro i k hne; exact (restr_ne hne).1
      · intro k j hne
        obtain ⟨hE, hne'⟩ := restr_ne hne
        have := hΦ k j hne'
        have := hle k j hne'
        try simp only at hE this ⊢
        omega
    · intro X top hΦ hkey
      exact inner top X fun i j hne => by
        obtain ⟨h1, h2, h3⟩ := hΦ i j hne
        have := hkey i j hne
        try simp only at this
        exact ⟨h1, h2, this, by omega⟩
    · intro i j hne
      obtain ⟨h1, h2, h3⟩ := hX i j hne
      have := hwin i j h1 h2
      omega
  have diag : ∀ X : Mat d F, (∀ i j, X i j ≠ 0 →
      (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h = (j : ℕ) / h) →
      FactM S (2 * h) ((T + 1) * 1) (1 + X) := by
    intro X hX
    refine peel S (2 * h) 1 w0 (fun i _ => (i : ℕ) / h)
      (fun X => ∀ i j, X i j ≠ 0 → (i : ℕ) < j ∧ ColOK S i j ∧ (i : ℕ) / h = (j : ℕ) / h)
      (fun X E hΦ i j hne => hΦ i j (restr_ne hne).2) ?_ ?_ (T + 1) X hX ?_
    · intro X top hΦ _
      apply mul_win_zero (fun i => (i : ℕ) / h) top
      · intro i k hne
        obtain ⟨hE, hne'⟩ := restr_ne hne
        have := hΦ i k hne'
        try simp only at hE ⊢
        omega
      · intro k j hne
        exact (restr_ne hne).1
    · intro X top hΦ hkey
      exact leaf S hh top X fun i j hne => by
        obtain ⟨h1, h2, h3⟩ := hΦ i j hne
        have := hkey i j hne
        try simp only at this
        exact ⟨h1, h2, by omega, by omega, by omega, by omega⟩
    · intro i j hne
      obtain ⟨h1, h2, h3⟩ := hX i j hne
      have := hwin i j h1 h2
      omega
  obtain ⟨hpM, hdM⟩ := pat_of_mem_UL hg
  set M : Mat d F := (g : Mat d F) with hM
  let D : Mat d F := Matrix.of fun i j => if (i : ℕ) / h = (j : ℕ) / h then M i j else 0
  have hpD : Pat (S : Set ℕ) D := fun i j hij hne => by
    simp only [D, Matrix.of_apply] at hne
    split_ifs at hne
    · exact hpM i j hij hne
    · exact absurd rfl hne
  have hdD : Diag1 D := fun i => by simp [D, hdM i]
  set Dsl := mkSL _ D hpD hdD with hDsl
  have hDmem : Dsl ∈ UL d F S := mem_UL_of_pat _ hpD hdD
  set R := Dsl⁻¹ * g with hR
  have hRmem : R ∈ UL d F S := mul_mem (inv_mem hDmem) hg
  obtain ⟨hpH, hdH⟩ := pat_of_mem_UL hRmem
  obtain ⟨hpI, -⟩ := pat_of_mem_UL (inv_mem hDmem)
  have hblock : ∀ i j : Fin (d + 1), (i : ℕ) / h = (j : ℕ) / h →
      (R : Mat d F) i j = (1 : Mat d F) i j := by
    intro i j hw
    have e1 : (R : Mat d F) = ((Dsl⁻¹ : SLd d F) : Mat d F) * M := rfl
    have e2 : ((Dsl⁻¹ : SLd d F) : Mat d F) * D = 1 := by
      show ((Dsl⁻¹ * Dsl : SLd d F) : Mat d F) = 1
      rw [inv_mul_cancel]; rfl
    rw [e1, ← e2, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) / h = (j : ℕ) / h
    · simp [D, hk]
    · by_cases hki : k < i
      · rw [hpI.lower hki]; simp
      · have hjk : j < k := by
          by_contra hjk
          have := Nat.div_le_div_right (c := h) (Fin.le_def.1 (not_lt.1 hki))
          have := Nat.div_le_div_right (c := h) (Fin.le_def.1 (not_lt.1 hjk))
          omega
        simp [D, hpM.lower hjk]
  have hD : FactM S (2 * h) ((T + 1) * 1) D := by
    have := diag (D - 1) fun i j hne => by
      have hij : i ≠ j := by rintro rfl; simp [hdD i] at hne
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at hne
      have hw : (i : ℕ) / h = (j : ℕ) / h := by
        by_contra hw; simp [D, hw] at hne
      obtain ⟨h1, h2⟩ := hpD i j hij hne
      exact ⟨h1, fun c hc1 hc2 => by simpa using h2 c hc1 hc2, hw⟩
    rwa [add_sub_cancel] at this
  have hH : FactM S (2 * h) ((T + 1) * (T * fN T)) (R : Mat d F) := by
    have := outer ((R : Mat d F) - 1) fun i j hne => by
      have hij : i ≠ j := by rintro rfl; simp [hdH i] at hne
      rw [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at hne
      obtain ⟨h1, h2⟩ := hpH i j hij hne
      have hw : (i : ℕ) / h ≠ (j : ℕ) / h := fun hw =>
        hne (by rw [hblock i j hw, Matrix.one_apply_ne hij])
      have := Nat.div_le_div_right (c := h) (Fin.le_def.1 h1.le)
      exact ⟨h1, fun c hc1 hc2 => by simpa using h2 c hc1 hc2, by omega⟩
    rwa [add_sub_cancel] at this
  have hg' : (g : Mat d F) = D * (R : Mat d F) := by
    show (g : Mat d F) = ((Dsl * R : SLd d F) : Mat d F)
    rw [hR, mul_inv_cancel_left]
  rw [hM, hg']
  exact (hD.mul hH).mono (by rw [mul_one])

/-! ## Turning factor lists into generator lists, and the area bound -/

lemma UL_mono {S S' : Finset ℕ} (h : S ⊆ S') : UL d F S ≤ UL d F S' :=
  Subgroup.closure_mono fun _ ⟨lam, i, j, hj, h1, h2, h3⟩ => ⟨lam, i, j, h hj, h1, h2, h3⟩

lemma UL_empty_eq (g : SLd d F) (hg : g ∈ UL d F ∅) : g = 1 := by
  have : UL d F ∅ = ⊥ := by
    unfold UL
    rw [Subgroup.closure_eq_bot_iff]
    rintro x ⟨_, _, _, hj, -⟩
    simp at hj
  rw [this] at hg
  exact hg

lemma build {B S' : Finset ℕ} {ι : Type*} (H : ι → Subgroup (UL d F B)) (K : ι)
    (hH : ∀ x : UL d F B, (x : SLd d F) ∈ UL d F S' → x ∈ H K) (hSB : S' ⊆ B)
    (P : SLd d F → Prop) :
    ∀ L : List (SLd d F), (∀ x ∈ L, x ∈ UL d F S' ∧ P x) →
      ∃ gs : List (CosetGen H), gs.length ≤ L.length ∧
        (∀ y ∈ gs, y.1 ∈ H K ∧ P (y.1 : SLd d F)) ∧
        (((gs.map Subtype.val).prod : UL d F B) : SLd d F) = L.prod := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], by simp, by simp, by simp⟩
  | cons x L ih =>
    intro hL
    obtain ⟨gs, h1, h2, h3⟩ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    obtain ⟨hx1, hx2⟩ := hL x (by simp)
    by_cases hx : x = 1
    · exact ⟨gs, by simp; omega, h2, by rw [List.prod_cons, hx, one_mul, ← h3]⟩
    · let y : UL d F B := ⟨x, UL_mono hSB hx1⟩
      have hy1 : y ≠ 1 := fun h => hx (by simpa [y] using congrArg Subtype.val h)
      refine ⟨⟨y, hy1, K, hH y hx1⟩ :: gs, by simp; omega, ?_, by
        simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, h3]; rfl⟩
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨hH y hx1, hx2⟩
      · exact h2 z hz

section AreaList

variable {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G) (K : ι)

lemma rel_le (l : List (CosetGen H)) (h1 : 1 ≤ l.length) (h2 : l.length ≤ 3)
    (hl : ∀ x ∈ l, x.1 ∈ H K) (hp : (l.map Subtype.val).prod = 1) :
    area (multTable H K) ((l.map FreeGroup.of).prod) ≤ 1 :=
  area_of_mem ⟨l, h1, h2, hl, hp, rfl⟩

/-- `Area([g] ([g₁] ⋯ [g_s])⁻¹) ≤ 2s` when `g = g₁ ⋯ g_s` in `H_K`. -/
lemma area_list (gs : List (CosetGen H)) (hgs : ∀ x ∈ gs, x.1 ∈ H K) (g : G) (hg : g ∈ H K)
    (hprod : (gs.map Subtype.val).prod = g) :
    area (multTable H K) (cosetWord H g ⟨K, hg⟩ * ((gs.map FreeGroup.of).prod)⁻¹) ≤
      ((2 * gs.length : ℕ) : ℕ∞) := by
  induction gs generalizing g with
  | nil =>
    simp only [List.map_nil, List.prod_nil] at hprod
    subst hprod
    simp [cosetWord, area_one]
  | cons x rest ih =>
    simp only [List.map_cons, List.prod_cons] at hprod ⊢
    have hg' : (rest.map Subtype.val).prod ∈ H K := Subgroup.list_prod_mem (H K) fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact hgs z (List.mem_cons_of_mem _ hz)
    set g' := (rest.map Subtype.val).prod
    have ih' := ih (fun y hy => hgs y (List.mem_cons_of_mem _ hy)) g' hg' rfl
    set W := (rest.map FreeGroup.of).prod
    have hx : x.1 ∈ H K := hgs x (by simp)
    have e : cosetWord H g ⟨K, hg⟩ * (FreeGroup.of x * W)⁻¹ =
        (cosetWord H g ⟨K, hg⟩ * (cosetWord H g' ⟨K, hg'⟩)⁻¹ * (FreeGroup.of x)⁻¹) *
        ((FreeGroup.of x)⁻¹⁻¹ * (cosetWord H g' ⟨K, hg'⟩ * W⁻¹) * (FreeGroup.of x)⁻¹) := by
      group
    rw [e]
    have hE : area (multTable H K) (cosetWord H g ⟨K, hg⟩ * (cosetWord H g' ⟨K, hg'⟩)⁻¹ *
        (FreeGroup.of x)⁻¹) ≤ 2 := by
      by_cases h1 : g' = 1
      · have hxg : x.1 = g := by rw [← hprod, h1, mul_one]
        have hgne : g ≠ 1 := hxg ▸ x.2.1
        have hw1 : cosetWord H g ⟨K, hg⟩ = FreeGroup.of x := by
          simp only [cosetWord, dif_neg hgne]
          congr 1
          exact Subtype.ext hxg.symm
        have hw2 : cosetWord H g' ⟨K, hg'⟩ = 1 := by simp [cosetWord, h1]
        rw [hw1, hw2]
        simp [area_one]
      · have hw2 : cosetWord H g' ⟨K, hg'⟩ = FreeGroup.of ⟨g', h1, K, hg'⟩ := by
          simp [cosetWord, h1]
        by_cases h2 : g = 1
        · have hw1 : cosetWord H g ⟨K, hg⟩ = 1 := by simp [cosetWord, h2]
          rw [hw1, hw2, one_mul, ← _root_.mul_inv_rev]
          have := rel_le H K [x, ⟨g', h1, K, hg'⟩] (by simp) (by simp)
            (by simp [hx, hg']) (by simp [hprod, h2])
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
            at this
          exact (area_inv_le _ _).trans (this.trans (by norm_num))
        · have hw1 : cosetWord H g ⟨K, hg⟩ = FreeGroup.of ⟨g, h2, K, hg⟩ := by
            simp [cosetWord, h2]
          rw [hw1, hw2]
          let gi : CosetGen H := ⟨g⁻¹, inv_ne_one.2 h2, K, inv_mem hg⟩
          have e2 : FreeGroup.of (⟨g, h2, K, hg⟩ : CosetGen H) *
              (FreeGroup.of (⟨g', h1, K, hg'⟩ : CosetGen H))⁻¹ * (FreeGroup.of x)⁻¹ =
              (FreeGroup.of ⟨g, h2, K, hg⟩ * FreeGroup.of gi) *
                (FreeGroup.of x * FreeGroup.of ⟨g', h1, K, hg'⟩ * FreeGroup.of gi)⁻¹ := by
            group
          rw [e2]
          have r1 := rel_le H K [⟨g, h2, K, hg⟩, gi] (by simp) (by simp)
            (by simp [gi, hg, inv_mem hg]) (by simp [gi])
          have r2 := rel_le H K [x, ⟨g', h1, K, hg'⟩, gi] (by simp) (by simp)
            (by simp [gi, hx, hg', inv_mem hg])
            (by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gi]
                rw [mul_one, ← mul_assoc, hprod, mul_inv_cancel])
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
            ← mul_assoc] at r1 r2
          calc _ ≤ _ + _ := area_mul_le _ _ _
            _ ≤ 1 + 1 := add_le_add r1 ((area_inv_le _ _).trans r2)
            _ = 2 := by norm_num
    calc _ ≤ _ + _ := area_mul_le _ _ _
      _ ≤ 2 + ((2 * rest.length : ℕ) : ℕ∞) := add_le_add hE ((area_conj_le _ _ _).trans ih')
      _ = ((2 * (x :: rest).length : ℕ) : ℕ∞) := by
        rw [List.length_cons]; push_cast; ring

end AreaList

/-- The total factor count for `T + 1` windows. -/
def Nb (T : ℕ) : ℕ := (T + 1) + (T + 1) * (T * fN T)

lemma Nb_mono {T T' : ℕ} (h : T ≤ T') : Nb T ≤ Nb T' := by
  unfold Nb
  have := fN_mono h
  gcongr

lemma Nb_61 : 2 * Nb 61 ≤ 2 ^ 80 := by
  have h := fN_eq 61
  unfold Nb
  have : fN 61 ≤ 3 * 2 ^ 61 := by omega
  calc 2 * (61 + 1 + (61 + 1) * (61 * fN 61)) ≤ 2 * (61 + 1 + (61 + 1) * (61 * (3 * 2 ^ 61))) := by
        gcongr
    _ ≤ 2 ^ 80 := by norm_num

end PolySwap.KMS.Sol62

open PolySwap.KMS PolySwap.KMS.Sol62

theorem solution : ∃ p : Polynomial ℕ, ∀ (d r T : ℕ) (F : Type*) [Field F] [Fintype F]
    (I : Finset (Finset ℕ)), I ∈ disjointColorSets d r T → IsNice d I →
    ∀ J ∈ I, ∀ ℓ ≤ r, ∀ C : ℕ, 1 ≤ C → C ≤ 20 → ∀ K : {K // K ∈ I.erase J},
    ∀ g, (hg : g ∈ binH d F I J ℓ K) →
      ∃ gs : List (CosetGen (binH d F I J ℓ)), gs.length ≤ p.eval C ∧
        (∀ x ∈ gs, x.1 ∈ binH d F I J ℓ K) ∧ (gs.map Subtype.val).prod = g ∧
        (∀ x ∈ gs, ∃ k : ℕ, (k : ℝ) ≤ ((binHi d J ℓ : ℝ) - binLo d J ℓ) / C ∧
          SupportedOnBlock d F
            (((x.1 : UL d F (bin d J ℓ)) : Matrix.SpecialLinearGroup (Fin (d + 1)) F) :
              Matrix (Fin (d + 1)) (Fin (d + 1)) F) k) ∧
        area (multTable (binH d F I J ℓ) K)
            (cosetWord (binH d F I J ℓ) g ⟨K, hg⟩ *
              ((gs.map FreeGroup.of).prod)⁻¹) ≤ ((p.eval C : ℕ) : ℕ∞) := by
  refine ⟨Polynomial.C (2 ^ 80), ?_⟩
  intro d r T F _ _ I hI hnice J hJ ℓ hℓ C hC1 hC20 K g hg
  simp only [Polynomial.eval_C]
  have hJc : J.card = r + 1 := by
    simp only [disjointColorSets, Finset.mem_filter, Finset.mem_powersetCard] at hI
    exact (Finset.mem_powersetCard.1 (hI.1.1 hJ)).2
  set a := binLo d J ℓ with ha
  set b := binHi d J ℓ with hb
  set S := bin d J ℓ \ rl d J K.1 with hSdef
  have hgS : (g : SLd d F) ∈ UL d F S := Subgroup.mem_subgroupOf.1 hg
  have hSB : S ⊆ bin d J ℓ := Finset.sdiff_subset
  obtain ⟨k0, L, hlen, hL, hprod⟩ : ∃ k0 : ℕ, ∃ L : List (SLd d F), L.length ≤ Nb 61 ∧
      (∀ x ∈ L, x ∈ UL d F S ∧
        (SupportedOnBlock d F (x : Mat d F) k0 ∧ (k0 : ℝ) ≤ ((b : ℝ) - a) / C)) ∧
      L.prod = (g : SLd d F) := by
    by_cases hab : a ≤ b
    · have h100 : 100 < b - a := (hnice J hJ).1 ℓ (by omega) hab
      have hC0 : 0 < 2 * C := by omega
      set h := (b - a) / (2 * C) with hhdef
      have hh2 : 2 ≤ h := (Nat.le_div_iff_mul_le hC0).2 (by omega)
      have hh : 0 < h := by omega
      have hS : ∀ c ∈ S, a ≤ c ∧ c ≤ b := fun c hc => by
        have := hSB hc
        simp only [bin, Finset.mem_Icc] at this
        exact this
      obtain ⟨L, h1, h2, h3⟩ := main S a b h hh hS (g : SLd d F) hgS
      have hT : b / h - (a - 1) / h ≤ 61 := by
        have e1 : h * (b / h) ≤ b := Nat.mul_div_le b h
        have e2 : a - 1 < h * ((a - 1) / h + 1) := Nat.lt_mul_div_succ _ hh
        have e3 : b - a < 2 * C * (h + 1) := by
          have := Nat.lt_mul_div_succ (b - a) hC0
          rwa [← hhdef] at this
        have e4 : 2 * C * (h + 1) ≤ 40 * (h + 1) := Nat.mul_le_mul_right _ (by omega)
        by_contra hc
        have e5 : h * ((a - 1) / h + 62) ≤ h * (b / h) := Nat.mul_le_mul_left _ (by omega)
        rw [mul_add] at e2 e5
        omega
      refine ⟨2 * h, L, ?_, fun x hx => ⟨(h2 x hx).1, (h2 x hx).2, ?_⟩, Subtype.ext h3⟩
      · unfold Nb; exact h1.trans (Nb_mono hT)
      · have e : 2 * C * h ≤ b - a := by
          rw [mul_comm (2 * C)]; exact Nat.div_mul_le_self _ _
        have e' : ((2 * C * h : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast e
        push_cast [Nat.cast_sub hab] at e'
        rw [le_div_iff₀ (by positivity)]
        push_cast
        linarith
    · refine ⟨0, [], by simp, by simp, ?_⟩
      have hbin : bin d J ℓ = ∅ := Finset.Icc_eq_empty (by omega)
      have hS0 : S = ∅ := by rw [hSdef, hbin]; simp
      rw [hS0] at hgS
      exact (UL_empty_eq _ hgS).symm
  obtain ⟨gs, hlen', hgs, hprod'⟩ := build (binH d F I J ℓ) K
    (fun x hx => Subgroup.mem_subgroupOf.2 hx) hSB _ L hL
  have hgsprod : (gs.map Subtype.val).prod = g := Subtype.ext (hprod'.trans hprod)
  refine ⟨gs, ?_, fun x hx => (hgs x hx).1, hgsprod, fun x hx => ⟨k0, (hgs x hx).2.2,
    (hgs x hx).2.1⟩, ?_⟩
  · have := Nb_61; omega
  · refine (area_list _ K gs (fun x hx => (hgs x hx).1) g hg hgsprod).trans ?_
    have := Nb_61
    exact_mod_cast (by omega : 2 * gs.length ≤ 2 ^ 80)
