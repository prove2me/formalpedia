-- Prove2me | solution 1 for WhitneyMatroid.Fano.exists_matroidOf_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T21:30:10.382561+00:00
-- url     : https://prove2.me/submissions/dcd83fa3-b5d5-4ba6-8428-36700c94f298

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
open WhitneyFano in
theorem solution {ι : Type*} [Fintype ι] (m : ℕ) (A : Matrix (Fin m) ι ℝ) :
    ∃ M : Matroid ι, IsMatroidOf M A :=
  ⟨linMatroid A, linMatroid_isMatroidOf A⟩
