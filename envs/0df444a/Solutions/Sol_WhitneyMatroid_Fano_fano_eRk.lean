-- Prove2me | solution 1 for WhitneyMatroid.Fano.fano_eRk
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T21:35:28.080974+00:00
-- url     : https://prove2.me/submissions/397285b0-cd46-4509-9163-989077eba170

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

lemma four_pts : ∀ a b c d : Fin 7, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ({a, b, c} : Finset (Fin 7)) ∉ linesF ∨ ({a, b, d} : Finset (Fin 7)) ∉ linesF := by
  decide +kernel


variable {M : Matroid (Fin 7)}

lemma eRank_eq (hM : IsFano M) : M.eRank = 3 := by
  have hB := isBase_triple hM (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide)
    (by decide)
  rw [← hB.encard_eq_eRank, ← (toFinite _).cast_ncard_eq,
    ncard_triple (by decide) (by decide) (by decide)]
  rfl

lemma indep_of_ncard_le_two (hM : IsFano M) {S : Set (Fin 7)} (hS : S.ncard ≤ 2) : M.Indep S := by
  obtain h | h | h : S.ncard = 0 ∨ S.ncard = 1 ∨ S.ncard = 2 := by omega
  · rw [Set.ncard_eq_zero] at h
    rw [h]
    exact M.empty_indep
  · obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 h
    obtain ⟨b, hab⟩ : ∃ b : Fin 7, a ≠ b := (by decide : ∀ a : Fin 7, ∃ b, a ≠ b) a
    exact (indep_pair hM hab).subset (by simp)
  · obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 h
    exact indep_pair hM hab

theorem fano_eRk' (hM : IsFano M) (S : Set (Fin 7)) :
    (S.ncard ≤ 2 → M.eRk S = S.ncard) ∧
      (4 ≤ S.ncard → M.eRk S = 3) ∧
      (S.ncard = 3 → S ∈ fanoLines → M.eRk S = 2) ∧
      (S.ncard = 3 → S ∉ fanoLines → M.eRk S = 3) := by
  have hR := eRank_eq hM
  have hle : M.eRk S ≤ 3 := hR ▸ M.eRk_le_eRank S
  refine ⟨fun h => ?_, fun h => ?_, fun h hl => ?_, fun h hl => ?_⟩
  · rw [(indep_of_ncard_le_two hM h).eRk_eq_encard, S.toFinite.cast_ncard_eq]
  · obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      (Set.three_lt_ncard_iff (s := S)).1 (by omega)
    refine le_antisymm hle ?_
    have key : ∀ {x y z : Fin 7}, x ∈ S → y ∈ S → z ∈ S → x ≠ y → x ≠ z → y ≠ z →
        ({x, y, z} : Finset (Fin 7)) ∉ linesF → 3 ≤ M.eRk S := by
      intro x y z hx hy hz hxy hxz hyz hl
      have hB := isBase_triple hM hxy hxz hyz hl
      calc (3 : ℕ∞) = M.eRank := hR.symm
        _ = M.eRk {x, y, z} := hB.eRk_eq_eRank.symm
        _ ≤ M.eRk S := M.eRk_mono (by
            intro t ht
            rcases ht with rfl | rfl | rfl <;> assumption)
    rcases four_pts a b c d hab hac had hbc hbd hcd with hl | hl
    · exact key ha hb hc hab hac hbc hl
    · exact key ha hb hd hab had hbd hl
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 h
    have h2 : 2 ≤ M.eRk {a, b, c} := by
      have := M.eRk_mono (show ({a, b} : Set (Fin 7)) ⊆ {a, b, c} by
        intro t ht
        rcases ht with rfl | rfl <;> simp)
      rw [(indep_pair hM hab).eRk_eq_encard, Set.encard_pair hab] at this
      exact this
    have h3 : M.eRk {a, b, c} ≠ 3 := by
      intro h3
      apply not_indep_line hM hl
      rw [Matroid.indep_iff_eRk_eq_encard_of_finite (toFinite _), h3, ← (toFinite _).cast_ncard_eq,
        ncard_triple hab hac hbc]
      rfl
    obtain ⟨k, hk⟩ : ∃ k : ℕ, M.eRk {a, b, c} = k :=
      ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) hle)).symm⟩
    rw [hk] at h2 h3 hle ⊢
    norm_cast at h2 h3 hle ⊢
    omega
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.1 h
    rw [triple_coe, mem_fanoLines_iff] at hl
    exact (isBase_triple hM hab hac hbc hl).eRk_eq_eRank.trans hR

end WhitneyFano
open WhitneyFano in
theorem solution (M : Matroid (Fin 7)) (hM : IsFano M) (S : Set (Fin 7)) :
    (S.ncard ≤ 2 → M.eRk S = S.ncard) ∧
      (4 ≤ S.ncard → M.eRk S = 3) ∧
      (S.ncard = 3 → S ∈ fanoLines → M.eRk S = 2) ∧
      (S.ncard = 3 → S ∉ fanoLines → M.eRk S = 3) :=
  fano_eRk' hM S
