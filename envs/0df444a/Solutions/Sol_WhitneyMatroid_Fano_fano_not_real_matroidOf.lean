-- Prove2me | solution 1 for WhitneyMatroid.Fano.fano_not_real_matroidOf
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T21:19:53.440994+00:00
-- url     : https://prove2.me/submissions/0738750a-d1c3-4763-b294-4abfe1e99c4b

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_IsFano

open WhitneyMatroid.Fano Module Set


namespace WhitneyFano

section Lin

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix (Fin m) ι K)

lemma finrank_span_of_indep {s : Set ι} (h : LinearIndepOn K A.col s) :
    finrank K (Submodule.span K (A.col '' s)) = s.ncard := by
  have : Fintype s := Fintype.ofFinite s
  rw [image_eq_range, finrank_span_eq_card h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

lemma mem_span_of_not_indep {s : Set ι} {e : ι} (hs : LinearIndepOn K A.col s)
    (hn : ¬ LinearIndepOn K A.col (insert e s)) : A.col e ∈ Submodule.span K (A.col '' s) := by
  by_cases he : e ∈ s
  · exact Submodule.subset_span (mem_image_of_mem _ he)
  · by_contra hc
    exact hn ((linearIndepOn_insert he).2 ⟨hs, hc⟩)

/-- The matroid of the columns of `A`: a set of columns is independent iff it is linearly
independent. -/
noncomputable def linMatroid : Matroid ι :=
  (IndepMatroid.ofFinite (E := univ) finite_univ (fun I => LinearIndepOn K A.col I)
    (linearIndepOn_empty K A.col)
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun I J hI hJ hlt => by
      by_contra hno
      push Not at hno
      have hsub : A.col '' J ⊆ Submodule.span K (A.col '' I) := by
        rintro _ ⟨e, heJ, rfl⟩
        by_cases heI : e ∈ I
        · exact Submodule.subset_span (mem_image_of_mem _ heI)
        · exact mem_span_of_not_indep A hI (hno e heJ heI)
      have hle := Submodule.finrank_mono (Submodule.span_le.2 hsub)
      rw [finrank_span_of_indep A hI, finrank_span_of_indep A hJ] at hle
      omega)
    (fun _ _ => subset_univ _)).matroid

lemma linMatroid_indep {I : Set ι} : (linMatroid A).Indep I ↔ LinearIndepOn K A.col I := by
  simp [linMatroid]

lemma linMatroid_ground : (linMatroid A).E = univ := rfl

lemma linMatroid_eRk (S : Set ι) :
    (linMatroid A).eRk S = (finrank K (Submodule.span K (A.col '' S)) : ℕ∞) := by
  obtain ⟨I, hI⟩ := (linMatroid A).exists_isBasis S (by rw [linMatroid_ground]; exact subset_univ _)
  have hIi : LinearIndepOn K A.col I := (linMatroid_indep A).1 hI.indep
  have hspan : Submodule.span K (A.col '' S) = Submodule.span K (A.col '' I) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (image_mono hI.subset))
    rintro _ ⟨e, heS, rfl⟩
    by_cases heI : e ∈ I
    · exact Submodule.subset_span (mem_image_of_mem _ heI)
    · refine mem_span_of_not_indep A hIi fun hins => ?_
      exact (hI.insert_dep ⟨heS, heI⟩).not_indep ((linMatroid_indep A).2 hins)
  rw [hI.eRk_eq_encard, ← I.toFinite.cast_ncard_eq, hspan, finrank_span_of_indep A hIi]

lemma submatrix_rank (N : Finset ι) :
    (A.submatrix id (fun j : N => (j : ι))).rank =
      finrank K (Submodule.span K (A.col '' (N : Set ι))) := by
  have hr : range (A.submatrix id (fun j : N => (j : ι))).col = A.col '' (N : Set ι) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  rw [Matrix.rank_eq_finrank_span_cols, hr]

lemma linMatroid_isMatroidOf : IsMatroidOf (linMatroid A) A :=
  ⟨linMatroid_ground A, fun N => by rw [linMatroid_eRk, submatrix_rank]⟩

lemma eq_linMatroid {M : Matroid ι} (h : IsMatroidOf M A) : M = linMatroid A := by
  have hr : ∀ I : Set ι, M.eRk I = (linMatroid A).eRk I := fun I => by
    rw [← I.toFinite.coe_toFinset, h.2, (linMatroid_isMatroidOf A).2]
  refine Matroid.ext_indep (h.1.trans (linMatroid_ground A).symm) fun I _ => ?_
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite I.toFinite,
    Matroid.indep_iff_eRk_eq_encard_of_finite I.toFinite, hr]

lemma indep_iff {M : Matroid ι} (h : IsMatroidOf M A) {I : Set ι} :
    M.Indep I ↔ LinearIndepOn K A.col I := by
  rw [eq_linMatroid A h, linMatroid_indep]

end Lin

end WhitneyFano


namespace WhitneyFano

/-- The seven lines (16.1) as finsets. -/
def linesF : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {0, 2, 4}, {0, 5, 6}, {1, 2, 5}, {1, 4, 6}, {2, 3, 6}, {3, 4, 5}}

lemma triple_coe (a b c : Fin 7) : ({a, b, c} : Set (Fin 7)) = ↑({a, b, c} : Finset (Fin 7)) := by
  push_cast; rfl

lemma mem_fanoLines_iff (F : Finset (Fin 7)) : (F : Set (Fin 7)) ∈ fanoLines ↔ F ∈ linesF := by
  simp only [fanoLines, linesF, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
    Finset.mem_singleton, triple_coe, Finset.coe_inj]

lemma ncard_triple {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set (Fin 7)).ncard = 3 :=
  Set.ncard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩

lemma ncard_line {L : Set (Fin 7)} (hL : L ∈ fanoLines) : L.ncard = 3 := by
  simp only [fanoLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ncard_triple (by decide) (by decide) (by decide)

variable {M : Matroid (Fin 7)}

lemma isBase_triple (hM : IsFano M) {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hl : ({a, b, c} : Finset (Fin 7)) ∉ linesF) : M.IsBase {a, b, c} :=
  (hM.2 _).2 ⟨ncard_triple hab hac hbc, by rw [triple_coe, mem_fanoLines_iff]; exact hl⟩

lemma indep_pair (hM : IsFano M) {i j : Fin 7} (hij : i ≠ j) : M.Indep {i, j} := by
  have key : ∀ i j : Fin 7, i ≠ j → ∃ k, i ≠ k ∧ j ≠ k ∧ ({i, j, k} : Finset (Fin 7)) ∉ linesF := by
    decide
  obtain ⟨k, hik, hjk, hl⟩ := key i j hij
  refine (isBase_triple hM hij hik hjk hl).indep.subset ?_
  intro x hx
  rcases hx with rfl | rfl <;> simp

lemma not_indep_line (hM : IsFano M) {L : Set (Fin 7)} (hL : L ∈ fanoLines) : ¬ M.Indep L := by
  intro hI
  obtain ⟨B, hB, hLB⟩ := hI.exists_isBase_superset
  have h3 := ((hM.2 B).1 hB)
  have hLB' : L = B := Set.eq_of_subset_of_ncard_le hLB (by rw [ncard_line hL, h3.1]) B.toFinite
  exact h3.2 (hLB' ▸ hL)

section LinAlg

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*} (v : ι → V)

lemma span_of_line {a b c : ι} (hac : a ≠ c) (hbc : b ≠ c)
    (hdep : ¬ LinearIndepOn K v (insert c {a, b})) (hind : LinearIndepOn K v {a, b}) :
    ∃ x y : K, x • v a + y • v b = v c := by
  have hc : c ∉ ({a, b} : Set ι) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hac.symm, hbc.symm⟩
  by_contra h
  apply hdep
  rw [linearIndepOn_insert hc]
  refine ⟨hind, fun hm => h ?_⟩
  rw [Set.image_pair, Submodule.mem_span_pair] at hm
  exact hm

lemma pair_ne {a b : ι} (hab : a ≠ b) (h : LinearIndepOn K v {a, b}) (x : K) : x • v a ≠ v b := by
  have hva : v a ≠ 0 := (linearIndepOn_singleton_iff K).1 (h.mono (by simp))
  exact (linearIndepOn_pair_iff v hab hva).1 h x

lemma coef_eq_zero {s : Set ι} {c : ι} (h : LinearIndepOn K v (insert c s)) (hc : c ∉ s) {w : V}
    (hw : w ∈ Submodule.span K (v '' s)) {z : K} (hs : w + z • v c = 0) : z = 0 := by
  by_contra hz
  apply ((linearIndepOn_insert hc).1 h).2
  have h2 : z • v c = -w := by linear_combination (norm := module) hs
  have h3 : v c = z⁻¹ • -w := by
    rw [← h2, smul_smul, inv_mul_cancel₀ hz, one_smul]
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hw)

lemma triple_zero {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : LinearIndepOn K v {a, b, c}) {x y z : K} (hs : x • v a + y • v b + z • v c = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have e1 : ({a, b, c} : Set ι) = insert c {a, b} := by
    ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hc : c ∉ ({a, b} : Set ι) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hac.symm, hbc.symm⟩
  rw [e1] at h
  have hz : z = 0 := coef_eq_zero v h hc (by
    rw [Set.image_pair, Submodule.mem_span_pair]; exact ⟨x, y, rfl⟩) hs
  subst hz
  have h2 : LinearIndepOn K v (insert b {a}) := h.mono (by
    intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢; tauto)
  have hb : b ∉ ({a} : Set ι) := by simpa using hab.symm
  have hy : y = 0 := coef_eq_zero v h2 hb (by
    rw [Set.image_singleton, Submodule.mem_span_singleton]; exact ⟨x, rfl⟩)
    (by simpa using hs)
  subst hy
  have hva : v a ≠ 0 := (linearIndepOn_singleton_iff K).1 (h2.mono (by simp))
  simp only [zero_smul, add_zero] at hs
  exact ⟨(smul_eq_zero.1 hs).resolve_right hva, rfl, rfl⟩

end LinAlg

/-- No real matrix corresponds to a matroid satisfying (16.1). -/
theorem not_real (hM : IsFano M) {m : ℕ} (A : Matrix (Fin m) (Fin 7) ℝ) (h : IsMatroidOf M A) :
    False := by
  set v := A.col with hv
  have hI : ∀ I, M.Indep I ↔ LinearIndepOn ℝ v I := fun I => indep_iff A h
  have pair : ∀ {i j : Fin 7}, i ≠ j → LinearIndepOn ℝ v {i, j} := fun hij =>
    (hI _).1 (indep_pair hM hij)
  have line : ∀ {L : Set (Fin 7)}, L ∈ fanoLines → ¬ LinearIndepOn ℝ v L := fun hL hli =>
    not_indep_line hM hL ((hI _).2 hli)
  have l3 : ∀ {a b c : Fin 7}, ({a, b, c} : Set (Fin 7)) ∈ fanoLines →
      ¬ LinearIndepOn ℝ v (insert c {a, b}) := fun {a b c} hL => by
    rw [show (insert c {a, b} : Set (Fin 7)) = {a, b, c} by
      ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
    exact line hL
  obtain ⟨a1, a2, h013⟩ := span_of_line v (a := 0) (b := 1) (c := 3) (by decide) (by decide)
    (l3 (by simp [fanoLines])) (pair (by decide))
  obtain ⟨b1, b3, h024⟩ := span_of_line v (a := 0) (b := 2) (c := 4) (by decide) (by decide)
    (l3 (by simp [fanoLines])) (pair (by decide))
  obtain ⟨c2, c3, h125⟩ := span_of_line v (a := 1) (b := 2) (c := 5) (by decide) (by decide)
    (l3 (by simp [fanoLines])) (pair (by decide))
  obtain ⟨s, t, h056⟩ := span_of_line v (a := 0) (b := 5) (c := 6) (by decide) (by decide)
    (l3 (by simp [fanoLines])) (pair (by decide))
  obtain ⟨s', t', h146⟩ := span_of_line v (a := 1) (b := 4) (c := 6) (by decide) (by decide)
    (l3 (by simp [fanoLines])) (pair (by decide))
  obtain ⟨s'', t'', h236⟩ := span_of_line v (a := 2) (b := 3) (c := 6) (by decide) (by decide)
    (l3 (by simp [fanoLines])) (pair (by decide))
  obtain ⟨β, γ, h453⟩ := span_of_line v (a := 4) (b := 5) (c := 3) (by decide) (by decide)
    (l3 (by
      rw [show ({4, 5, 3} : Set (Fin 7)) = {3, 4, 5} by
        ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto]
      simp [fanoLines])) (pair (by decide))
  have hb1 : b1 ≠ 0 := by
    rintro rfl
    exact pair_ne v (a := 2) (b := 4) (by decide) (pair (by decide)) b3
      (by rw [← h024, zero_smul, zero_add])
  have hc2 : c2 ≠ 0 := by
    rintro rfl
    exact pair_ne v (a := 2) (b := 5) (by decide) (pair (by decide)) c3
      (by rw [← h125, zero_smul, zero_add])
  have hc3 : c3 ≠ 0 := by
    rintro rfl
    exact pair_ne v (a := 1) (b := 5) (by decide) (pair (by decide)) c2
      (by rw [← h125, zero_smul, add_zero])
  have ht : t ≠ 0 := by
    rintro rfl
    exact pair_ne v (a := 0) (b := 6) (by decide) (pair (by decide)) s
      (by rw [← h056, zero_smul, add_zero])
  have ht'' : t'' ≠ 0 := by
    rintro rfl
    exact pair_ne v (a := 2) (b := 6) (by decide) (pair (by decide)) s''
      (by rw [← h236, zero_smul, add_zero])
  have h012 : LinearIndepOn ℝ v {0, 1, 2} :=
    (hI _).1 (isBase_triple hM (by decide) (by decide) (by decide) (by decide)).indep
  rw [← h125] at h056
  rw [← h024] at h146
  rw [← h013] at h236
  rw [← h013, ← h024, ← h125] at h453
  obtain ⟨x1a, -, x1c⟩ := triple_zero v (by decide) (by decide) (by decide) h012
    (x := s - t' * b1) (y := t * c2 - s') (z := t * c3 - t' * b3)
    (by linear_combination (norm := module) h056 - h146)
  obtain ⟨x2a, x2b, -⟩ := triple_zero v (by decide) (by decide) (by decide) h012
    (x := s - t'' * a1) (y := t * c2 - t'' * a2) (z := t * c3 - s'')
    (by linear_combination (norm := module) h056 - h236)
  obtain ⟨x3a, x3b, x3c⟩ := triple_zero v (by decide) (by decide) (by decide) h012
    (x := β * b1 - a1) (y := γ * c2 - a2) (z := β * b3 + γ * c3)
    (by linear_combination (norm := module) h453)
  have k1 : t' = t'' * β :=
    mul_right_cancel₀ hb1 (by linear_combination x2a - x1a - t'' * x3a)
  have k2 : t = t'' * γ :=
    mul_right_cancel₀ hc2 (by linear_combination x2b - t'' * x3b)
  have k3 : t'' * c3 * (2 * γ) = 0 := by
    linear_combination (-c3) * k2 + x1c + b3 * k1 + t'' * x3c
  have hγ : γ = 0 := by
    rcases mul_eq_zero.1 k3 with h0 | h0
    · exact absurd h0 (mul_ne_zero ht'' hc3)
    · linarith
  exact ht (by rw [k2, hγ, mul_zero])

end WhitneyFano


namespace WhitneyFano

/-- The mod-2 matrix of p. 533. -/
def A2 : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 1;
     0, 1, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 1]

lemma A2_col_ne_zero : ∀ a : Fin 7, A2.col a ≠ 0 := by decide

lemma A2_pair : ∀ a b : Fin 7, a ≠ b → ∀ x : ZMod 2, x • A2.col a ≠ A2.col b := by decide

lemma A2_line : ∀ a b c : Fin 7, a ≠ b → a ≠ c → b ≠ c →
    ((∃ x y : ZMod 2, x • A2.col a + y • A2.col b = A2.col c) ↔
      ({a, b, c} : Finset (Fin 7)) ∈ linesF) := by decide


lemma A2_indep_triple {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndepOn (ZMod 2) A2.col {a, b, c} ↔ ({a, b, c} : Finset (Fin 7)) ∉ linesF := by
  have e1 : ({a, b, c} : Set (Fin 7)) = insert c {a, b} := by
    ext t; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  have hc : c ∉ ({a, b} : Set (Fin 7)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hac.symm, hbc.symm⟩
  have hp : LinearIndepOn (ZMod 2) A2.col {a, b} :=
    (linearIndepOn_pair_iff _ hab (A2_col_ne_zero a)).2 (A2_pair a b hab)
  rw [e1, linearIndepOn_insert hc, Set.image_pair, Submodule.mem_span_pair,
    A2_line a b c hab hac hbc]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

lemma A2_eRank_le : (linMatroid A2).eRank ≤ 3 := by
  rw [← Matroid.eRk_ground, linMatroid_eRk]
  have := Submodule.finrank_le (Submodule.span (ZMod 2) (A2.col '' (linMatroid A2).E))
  rw [Module.finrank_fin_fun] at this
  exact_mod_cast this

lemma A2_isBase_of_indep {B : Set (Fin 7)} (hB : (linMatroid A2).Indep B) (h3 : B.ncard = 3) :
    (linMatroid A2).IsBase B :=
  hB.isBase_of_eRk_ge B.toFinite (A2_eRank_le.trans (by
    rw [hB.eRk_eq_encard, ← B.toFinite.cast_ncard_eq, h3]; rfl))

/-- The matroid of the mod-2 matrix is the matroid `M′` of §16. -/
theorem A2_isFano : IsFano (linMatroid A2) := by
  have h012 : (linMatroid A2).IsBase {0, 1, 2} :=
    A2_isBase_of_indep ((linMatroid_indep A2).2
      ((A2_indep_triple (by decide) (by decide) (by decide)).2 (by decide)))
      (ncard_triple (by decide) (by decide) (by decide))
  refine ⟨linMatroid_ground A2, fun B => ⟨fun hB => ?_, fun ⟨h3, hl⟩ => ?_⟩⟩
  · have h3 : B.ncard = 3 := by
      rw [hB.ncard_eq_ncard_of_isBase h012, ncard_triple (by decide) (by decide) (by decide)]
    refine ⟨h3, ?_⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 h3
    rw [triple_coe, mem_fanoLines_iff]
    exact (A2_indep_triple hab hac hbc).1 ((linMatroid_indep A2).1 hB.indep)
  · refine A2_isBase_of_indep ((linMatroid_indep A2).2 ?_) h3
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 h3
    rw [triple_coe, mem_fanoLines_iff] at hl
    exact (A2_indep_triple hab hac hbc).2 hl

end WhitneyFano

theorem solution :
    (∃ M : Matroid (Fin 7), IsFano M) ∧
      ∀ M : Matroid (Fin 7), IsFano M →
        ∀ (m : ℕ) (A : Matrix (Fin m) (Fin 7) ℝ), ¬ IsMatroidOf M A :=
  ⟨⟨_, WhitneyFano.A2_isFano⟩, fun _ hM _ A h => WhitneyFano.not_real hM A h⟩
