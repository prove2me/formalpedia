-- Prove2me | solution 1 for WhitneyMatroid.Fano.exists_circuitMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T21:30:14.429003+00:00
-- url     : https://prove2.me/submissions/f5af4d02-8805-4199-b9a2-3420cd2280bf

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_IsFano
import Definitions.Def_WhitneyMatroid_Fano_IsCircuitMatrix

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

section Circ

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix (Fin m) ι K)

lemma mulVec_eq_sum (b : ι → K) : A.mulVec b = ∑ j, b j • A.col j := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- A set of columns is linearly independent iff no nonzero vector of the kernel of `A` is
supported on it. -/
lemma linIndep_iff_ker {s : Set ι} :
    LinearIndepOn K A.col s ↔ ∀ b : ι → K, (∀ j ∉ s, b j = 0) → A.mulVec b = 0 → b = 0 := by
  classical
  rw [linearIndepOn_iff'']
  constructor
  · intro h b hb hA
    funext j
    by_cases hj : j ∈ s
    · refine h s.toFinset b (by simp) (fun i hi => hb i (by simpa using hi)) ?_ j (by simpa using hj)
      rw [← hA, mulVec_eq_sum]
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      rw [hb i (by simpa using hi), zero_smul]
    · exact hb j hj
  · intro h t g hts htg h0 i _
    have := h g (fun j hj => htg j fun hjt => hj (hts hjt)) (by
      rw [mulVec_eq_sum, ← h0]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by rw [htg i hi, zero_smul]).symm)
    rw [this]
    rfl

variable {M : Matroid ι}

lemma indep_iff_ker (h : IsMatroidOf M A) {s : Set ι} :
    M.Indep s ↔ ∀ b : ι → K, (∀ j ∉ s, b j = 0) → A.mulVec b = 0 → b = 0 :=
  (indep_iff A h).trans (linIndep_iff_ker A)

/-- (14.1): every circuit carries a kernel vector of `A` whose nonzero coordinates are exactly the
circuit. -/
lemma circuit_vec (h : IsMatroidOf M A) {P : Set ι} (hP : M.IsCircuit P) :
    ∃ b : ι → K, A.mulVec b = 0 ∧ InZ b P := by
  have hdep := hP.not_indep
  rw [indep_iff_ker A h] at hdep
  push Not at hdep
  obtain ⟨b, hb, hA, hne⟩ := hdep
  refine ⟨b, hA, fun j => ⟨fun hj => by_contra fun hjP => hj (hb j hjP), fun hjP hj0 => hne ?_⟩⟩
  refine (indep_iff_ker A h).1 (hP.diff_singleton_indep hjP) b (fun i hi => ?_) hA
  by_cases hiP : i ∈ P
  · have : i = j := by
      by_contra hij
      exact hi ⟨hiP, hij⟩
    rw [this, hj0]
  · exact hb i hiP

lemma mulVec_eq_zero_of_mem_span {κ : Type*} {B : Matrix κ ι K} (hB : ∀ k, A.mulVec (B k) = 0)
    {b : ι → K} (hb : b ∈ Submodule.span K (range B)) : A.mulVec b = 0 := by
  have hle : Submodule.span K (range B) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact hB k
  exact hle hb

/-- Lemma 11 core: two kernel vectors with the same support, a circuit, are proportional. -/
lemma proportional {P : Set ι} (h : IsMatroidOf M A) (hP : M.IsCircuit P) {b b' : ι → K}
    (hA : A.mulVec b = 0) (hA' : A.mulVec b' = 0) (hbP : InZ b P) (hb'P : InZ b' P) :
    ∃ c : K, c ≠ 0 ∧ b' = c • b := by
  obtain ⟨j, hj⟩ := hP.nonempty
  have hbj : b j ≠ 0 := (hbP j).2 hj
  have hb'j : b' j ≠ 0 := (hb'P j).2 hj
  refine ⟨b' j / b j, div_ne_zero hb'j hbj, ?_⟩
  have hz := (indep_iff_ker A h).1 (hP.diff_singleton_indep hj) (b' - (b' j / b j) • b)
    (fun i hi => ?_) (by rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hA, hA', smul_zero, sub_zero])
  · exact sub_eq_zero.1 hz
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hiP : i ∈ P
  · have : i = j := by
      by_contra hij
      exact hi ⟨hiP, hij⟩
    subst this
    rw [div_mul_cancel₀ _ hbj, sub_self]
  · have h1 : b i = 0 := by
      by_contra h1
      exact hiP ((hbP i).1 h1)
    have h2 : b' i = 0 := by
      by_contra h2
      exact hiP ((hb'P i).1 h2)
    rw [h1, h2, mul_zero, sub_zero]

/-- Lemma 10 core: every element of the support of a kernel vector lies on a circuit inside the
support. -/
lemma exists_circuit_of_mem_support (h : IsMatroidOf M A) {b : ι → K} (hA : A.mulVec b = 0)
    {N : Set ι} (hbN : InZ b N) {j : ι} (hj : j ∈ N) :
    ∃ C, M.IsCircuit C ∧ j ∈ C ∧ C ⊆ N := by
  classical
  obtain rfl := eq_linMatroid A h
  set v := A.col
  set S := N \ {j}
  obtain ⟨I, hI⟩ := (linMatroid A).exists_isBasis S
    (by rw [linMatroid_ground]; exact subset_univ _)
  have hIi : LinearIndepOn K v I := (linMatroid_indep A).1 hI.indep
  have hle : Submodule.span K (v '' S) ≤ Submodule.span K (v '' I) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨e, heS, rfl⟩
    by_cases heI : e ∈ I
    · exact Submodule.subset_span (mem_image_of_mem _ heI)
    · refine mem_span_of_not_indep A hIi fun hins => ?_
      exact (hI.insert_dep ⟨heS, heI⟩).not_indep ((linMatroid_indep A).2 hins)
  have hmem : ∑ i ∈ Finset.univ.erase j, b i • v i ∈ Submodule.span K (v '' S) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    by_cases hiN : i ∈ N
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨i, ⟨hiN, Finset.ne_of_mem_erase hi⟩, rfl⟩)
    · have : b i = 0 := by
        by_contra h0
        exact hiN ((hbN i).1 h0)
      rw [this, zero_smul]
      exact Submodule.zero_mem _
  have hsum := Finset.add_sum_erase Finset.univ (fun i => b i • v i) (Finset.mem_univ j)
  rw [← mulVec_eq_sum, hA] at hsum
  have hbj : b j ≠ 0 := (hbN j).2 hj
  have hvj : v j ∈ Submodule.span K (v '' S) := by
    have h1 : b j • v j ∈ Submodule.span K (v '' S) := by
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact Submodule.neg_mem _ hmem
    have h2 := Submodule.smul_mem _ (b j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hbj, one_smul] at h2
  have hjI : j ∉ I := fun hjI => (hI.subset hjI).2 rfl
  have hdep : (linMatroid A).Dep (insert j I) :=
    ⟨fun hi => ((linearIndepOn_insert hjI).1 ((linMatroid_indep A).1 hi)).2 (hle hvj),
      by rw [linMatroid_ground]; exact subset_univ _⟩
  obtain ⟨C, hCs, hC⟩ := hdep.exists_isCircuit_subset
  have hjC : j ∈ C := by
    by_contra hjC
    exact hC.not_indep (hI.indep.subset fun x hx => (hCs hx).resolve_left fun hxj => hjC (hxj ▸ hx))
  refine ⟨C, hC, hjC, fun x hx => ?_⟩
  rcases hCs hx with rfl | hxI
  · exact hj
  · exact (hI.subset hxI).1

end Circ

end WhitneyFano
open WhitneyFano in
theorem solution {ι : Type*} [Fintype ι] {m : ℕ} (A : Matrix (Fin m) ι ℝ)
    (M : Matroid ι) (hM : IsMatroidOf M A) :
    ∃ B : Matrix {P : Set ι // M.IsCircuit P} ι ℝ, IsCircuitMatrix M A B (Equiv.refl _) := by
  choose f hf using fun P : {P : Set ι // M.IsCircuit P} => circuit_vec A hM P.2
  exact ⟨fun P => f P, hM, fun k => hf k⟩
