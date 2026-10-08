-- Prove2me | solution 1 for WhitneyMatroid.Duality.associated_orthogonal_isDual
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T19:13:47.991031+00:00
-- url     : https://prove2.me/submissions/dbc91ee1-5912-4e4c-b6c7-caf7b758001d

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual
import Definitions.Def_WhitneyMatroid_Duality_IsAssociated

open WhitneyMatroid.Duality Module

namespace WhitneyDual

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

lemma coordProj_surjective (S : Set (Fin n)) : Function.Surjective (coordProj S) := by
  classical
  intro y
  refine ⟨WithLp.toLp 2 (fun i => if h : i ∈ S then y ⟨i, h⟩ else 0), ?_⟩
  funext i
  simp [coordProj, i.2]

lemma card_coe (S : Set (Fin n)) [Fintype S] : Fintype.card S = S.ncard := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- `dim K S + |S| = n`. -/
lemma finrank_K (S : Set (Fin n)) : finrank ℝ (K S) + S.ncard = n := by
  have : Fintype S := Fintype.ofFinite S
  have h := LinearMap.finrank_range_add_finrank_ker (coordProj S)
  rw [LinearMap.range_eq_top.2 (coordProj_surjective S), finrank_top, Module.finrank_fintype_fun_eq_card,
    card_coe, finrank_euclideanSpace_fin] at h
  show finrank ℝ (LinearMap.ker (coordProj S)) + S.ncard = n
  omega

/-- Rank–nullity on `H`: `dim proj_S(H) + dim (H ∩ K S) = dim H`. -/
lemma subspaceRank_add (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (S : Set (Fin n)) :
    subspaceRank H S + finrank ℝ ↥(H ⊓ K S) = finrank ℝ H := by
  have h := LinearMap.finrank_range_add_finrank_ker ((coordProj S).comp H.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp,
    ← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype] at h
  exact h

/-- The vectors vanishing on `Sᶜ` are the orthogonal complement of those vanishing on `S`. -/
lemma K_compl (S : Set (Fin n)) : K Sᶜ = (K S)ᗮ := by
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [mem_K] at hx hy
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i ∈ S
    · simp [hy i hi]
    · simp [hx i hi]
  · have h1 := finrank_K S
    have h2 := finrank_K Sᶜ
    have h3 := (K S).finrank_add_finrank_orthogonal
    have h4 := Set.ncard_add_ncard_compl S
    rw [finrank_euclideanSpace_fin] at h3
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h4
    omega

/-- The dimension count behind Theorem 28: `r_{H⊥}(Nᶜ) + |N| = dim H⊥ + r_H(N)`. -/
lemma key (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (N : Set (Fin n)) :
    subspaceRank Hᗮ Nᶜ + N.ncard = finrank ℝ Hᗮ + subspaceRank H N := by
  have a1 := subspaceRank_add Hᗮ Nᶜ
  have a2 := subspaceRank_add H N
  rw [K_compl, Submodule.inf_orthogonal] at a1
  have b1 := (H ⊔ K N).finrank_add_finrank_orthogonal
  have b2 := H.finrank_add_finrank_orthogonal
  have b3 := Submodule.finrank_sup_add_finrank_inf_eq H (K N)
  have b4 := finrank_K N
  have b5 := Set.ncard_add_ncard_compl N
  rw [finrank_euclideanSpace_fin] at b1 b2
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at b5
  omega

lemma subspaceRank_univ (H : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    subspaceRank H Set.univ = finrank ℝ H := by
  have h := subspaceRank_add H Set.univ
  have hK : K (Set.univ : Set (Fin n)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_K] at hx
    rw [Submodule.mem_bot]
    ext i
    simp [hx i (Set.mem_univ i)]
  rw [hK, inf_bot_eq, finrank_bot] at h
  omega

end WhitneyDual

open WhitneyDual in
theorem solution (n : ℕ) (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (M M' : Matroid (Fin n)) (hM : IsAssociated M H) (hM' : IsAssociated M' Hᗮ) :
    IsDualVia M M' (Equiv.refl (Fin n)) := by
  refine ⟨hM.1, hM'.1, fun N => ?_⟩
  have hk := key H N
  have hu := subspaceRank_univ Hᗮ
  simp only [Equiv.coe_refl, Set.image_id, WhitneyMatroid.Components.nullity, hM.2, hM'.2,
    ENat.toNat_natCast, ← Set.compl_eq_univ_sdiff]
  omega
