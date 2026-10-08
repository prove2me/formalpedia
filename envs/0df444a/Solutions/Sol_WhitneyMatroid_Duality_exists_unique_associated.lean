-- Prove2me | solution 1 for WhitneyMatroid.Duality.exists_unique_associated
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T21:00:30.818651+00:00
-- url     : https://prove2.me/submissions/4c89b939-003a-4e3f-9c35-09f90e0eb212

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsAssociated

open WhitneyMatroid.Duality Module Set

namespace WhitneyDualLin

variable {n : ℕ}

/-- `K S`: the vectors of `Eₙ` whose coordinates in `S` all vanish (the kernel of `coordProj S`). -/
noncomputable abbrev K (S : Set (Fin n)) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.ker (coordProj S)

lemma mem_K {S : Set (Fin n)} {x : EuclideanSpace ℝ (Fin n)} : x ∈ K S ↔ ∀ i ∈ S, x i = 0 := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro h i hi
    have := congrFun h ⟨i, hi⟩
    simpa [coordProj] using this
  · intro h
    funext i
    simpa [coordProj] using h i i.2

/-- Rank–nullity on `H`: `dim proj_S(H) + dim (H ∩ K S) = dim H`. -/
lemma subspaceRank_add (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (S : Set (Fin n)) :
    subspaceRank H S + finrank ℝ ↥(H ⊓ K S) = finrank ℝ H := by
  have h := LinearMap.finrank_range_add_finrank_ker ((coordProj S).comp H.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h
  exact h

variable (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))

/-- The `i`-th coordinate functional, restricted to `H`. -/
noncomputable def f (i : Fin n) : Module.Dual ℝ H :=
  (EuclideanSpace.projₗ (𝕜 := ℝ) i).comp H.subtype

lemma f_apply (i : Fin n) (x : H) : f H i x = (x : EuclideanSpace ℝ (Fin n)) i := rfl

lemma finrank_span_of_indep {s : Set (Fin n)} (h : LinearIndepOn ℝ (f H) s) :
    finrank ℝ (Submodule.span ℝ (f H '' s)) = s.ncard := by
  have : Fintype s := Fintype.ofFinite s
  rw [image_eq_range, finrank_span_eq_card h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

lemma mem_span_of_not_indep {s : Set (Fin n)} {e : Fin n} (hs : LinearIndepOn ℝ (f H) s)
    (hn : ¬ LinearIndepOn ℝ (f H) (insert e s)) : f H e ∈ Submodule.span ℝ (f H '' s) := by
  by_cases he : e ∈ s
  · exact Submodule.subset_span (mem_image_of_mem _ he)
  · by_contra hc
    exact hn ((linearIndepOn_insert he).2 ⟨hs, hc⟩)

/-- The linear matroid of the restricted coordinate functionals. -/
noncomputable def linMatroid : Matroid (Fin n) :=
  (IndepMatroid.ofFinite (E := univ) finite_univ (fun I => LinearIndepOn ℝ (f H) I)
    (linearIndepOn_empty ℝ (f H))
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun I J hI hJ hlt => by
      by_contra hno
      push Not at hno
      have hsub : f H '' J ⊆ Submodule.span ℝ (f H '' I) := by
        rintro _ ⟨e, heJ, rfl⟩
        by_cases heI : e ∈ I
        · exact Submodule.subset_span (mem_image_of_mem _ heI)
        · exact mem_span_of_not_indep H hI (hno e heJ heI)
      have hle := Submodule.finrank_mono (Submodule.span_le.2 hsub)
      rw [finrank_span_of_indep H hI, finrank_span_of_indep H hJ] at hle
      omega)
    (fun _ _ => subset_univ _)).matroid

lemma linMatroid_indep {I : Set (Fin n)} : (linMatroid H).Indep I ↔ LinearIndepOn ℝ (f H) I := by
  simp [linMatroid]

lemma linMatroid_ground : (linMatroid H).E = univ := rfl

/-- `dim span {f_i : i ∈ S} = dim proj_S(H)`, via the dual coannihilator. -/
lemma finrank_span_eq (S : Set (Fin n)) :
    finrank ℝ (Submodule.span ℝ (f H '' S)) = subspaceRank H S := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span ℝ (f H '' S))
  have h2 := subspaceRank_add H S
  have hc : (Submodule.span ℝ (f H '' S)).dualCoannihilator = (K S).comap H.subtype := by
    ext x
    rw [Submodule.mem_dualCoannihilator, Submodule.mem_comap, Submodule.subtype_apply, mem_K]
    constructor
    · intro h i hi
      exact h _ (Submodule.subset_span (mem_image_of_mem _ hi))
    · intro h φ hφ
      have hle : Submodule.span ℝ (f H '' S) ≤ LinearMap.ker (Module.Dual.eval ℝ H x) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        simp [f_apply, h i hi]
      simpa using hle hφ
  rw [hc, ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h1
  omega

lemma linMatroid_eRk (S : Set (Fin n)) : (linMatroid H).eRk S = (subspaceRank H S : ℕ∞) := by
  obtain ⟨I, hI⟩ := (linMatroid H).exists_isBasis S (by rw [linMatroid_ground]; exact subset_univ _)
  have hIi : LinearIndepOn ℝ (f H) I := (linMatroid_indep H).1 hI.indep
  have hspan : Submodule.span ℝ (f H '' S) = Submodule.span ℝ (f H '' I) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (image_mono hI.subset))
    rintro _ ⟨e, heS, rfl⟩
    by_cases heI : e ∈ I
    · exact Submodule.subset_span (mem_image_of_mem _ heI)
    · refine mem_span_of_not_indep H hIi fun hins => ?_
      exact (hI.insert_dep ⟨heS, heI⟩).not_indep ((linMatroid_indep H).2 hins)
  rw [hI.eRk_eq_encard, ← I.toFinite.cast_ncard_eq, ← finrank_span_eq, hspan,
    finrank_span_of_indep H hIi]

lemma linMatroid_isAssociated : IsAssociated (linMatroid H) H :=
  ⟨linMatroid_ground H, linMatroid_eRk H⟩

lemma associated_unique {M₁ M₂ : Matroid (Fin n)} (h₁ : IsAssociated M₁ H)
    (h₂ : IsAssociated M₂ H) : M₁ = M₂ := by
  refine Matroid.ext_indep (h₁.1.trans h₂.1.symm) fun I _ => ?_
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite I.toFinite,
    Matroid.indep_iff_eRk_eq_encard_of_finite I.toFinite, h₁.2, h₂.2]

end WhitneyDualLin

open WhitneyDualLin in
theorem solution (n : ℕ) (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃! M : Matroid (Fin n), IsAssociated M H :=
  ⟨linMatroid H, linMatroid_isAssociated H, fun _ h => associated_unique H h (linMatroid_isAssociated H)⟩
