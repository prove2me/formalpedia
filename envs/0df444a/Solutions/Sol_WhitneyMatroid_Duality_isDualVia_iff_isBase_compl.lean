-- Prove2me | solution 1 for WhitneyMatroid.Duality.isDualVia_iff_isBase_compl
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T20:57:15.300791+00:00
-- url     : https://prove2.me/submissions/843c8ab4-6158-41b0-9b88-d7b2149a1952

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual

open WhitneyMatroid.Duality WhitneyMatroid.Components Set

namespace WhitneyDualAbs

variable {α β : Type*} [Finite α] [Finite β]

lemma cast_r (M : Matroid α) (X : Set α) : ((M.eRk X).toNat : ℕ∞) = M.eRk X :=
  ENat.natCast_toNat (ne_top_of_le_ne_top X.toFinite.encard_lt_top.ne (M.eRk_le_encard X))

lemma cast_ncard (X : Set α) : (X.ncard : ℕ∞) = X.encard := X.toFinite.cast_ncard_eq

lemma eRk_eq_of_toNat {M : Matroid α} {M' : Matroid β} {X : Set α} {Y : Set β}
    (h : (M.eRk X).toNat = (M'.eRk Y).toNat) : M.eRk X = M'.eRk Y := by
  rw [← cast_r M X, ← cast_r M' Y, h]

lemma ncard_univ_eq (σ : α ≃ β) : (univ : Set α).ncard = (univ : Set β).ncard := by
  rw [ncard_univ, ncard_univ, Nat.card_congr σ]

/-- Rank of the dual on a complement (Whitney (11.1) for `M✶`), in `ℤ`. -/
lemma dual_eq {M : Matroid α} (hE : M.E = univ) (N : Set α) :
    ((M✶.eRk (univ \ N)).toNat : ℤ) = ((M✶.eRk univ).toNat : ℤ) - nullity M N := by
  have e1 := M.eRk_dual_add_eRank (univ \ N) (by rw [hE]; exact subset_univ _)
  have e2 := M.eRk_dual_add_eRank univ (by rw [hE])
  rw [hE, sdiff_sdiff_cancel_left (subset_univ N)] at e1
  rw [hE, sdiff_self, Matroid.eRk_empty, zero_add] at e2
  rw [← Matroid.eRk_ground, hE] at e1 e2
  rw [← cast_r M✶ (univ \ N), ← cast_r M univ, ← cast_r M N, ← cast_ncard (univ \ N)] at e1
  rw [← cast_r M✶ univ, ← cast_r M univ, ← cast_ncard univ] at e2
  norm_cast at e1 e2
  have h3 := ncard_add_ncard_compl N
  rw [compl_eq_univ_sdiff, ← ncard_univ] at h3
  unfold nullity
  omega

lemma image_compl (σ : α ≃ β) (N : Set α) : univ \ σ '' N = σ '' (univ \ N) := by
  rw [← compl_eq_univ_sdiff, ← compl_eq_univ_sdiff, Equiv.image_compl]

lemma compl_image_preimage (σ : α ≃ β) (Y : Set β) : univ \ σ '' (σ ⁻¹' (univ \ Y)) = Y := by
  rw [Equiv.image_preimage, ← compl_eq_univ_sdiff, ← compl_eq_univ_sdiff, compl_compl]

/-- The dual matroid, transported along `σ`, is a dual of `M` via `σ`. -/
lemma isDualVia_mapEquiv {M : Matroid α} (hE : M.E = univ) (σ : α ≃ β) :
    IsDualVia M (M✶.mapEquiv σ) σ := by
  have hg : (M✶.mapEquiv σ).E = univ := by
    rw [Matroid.mapEquiv_ground_eq, Matroid.dual_ground, hE, image_univ_of_surjective σ.surjective]
  have hr : ∀ X : Set α, (M✶.mapEquiv σ).eRk (σ '' X) = M✶.eRk X := fun X => by
    rw [Matroid.mapEquiv_eq_map]
    exact Matroid.eRk_map _ _ (by rw [Matroid.dual_ground, hE]; exact subset_univ _)
  refine ⟨hE, hg, fun N => ?_⟩
  rw [image_compl, hr, ← image_univ_of_surjective σ.surjective, hr]
  exact dual_eq hE N

/-- A dual via `σ` is unique. -/
lemma eq_of_isDualVia {M : Matroid α} {M₁ M₂ : Matroid β} {σ : α ≃ β} (h₁ : IsDualVia M M₁ σ)
    (h₂ : IsDualVia M M₂ σ) : M₁ = M₂ := by
  have top : ((M₁.eRk univ).toNat : ℤ) = ((M₂.eRk univ).toNat : ℤ) := by
    have a := h₁.2.2 univ
    have b := h₂.2.2 univ
    rw [image_univ_of_surjective σ.surjective, sdiff_self, Matroid.eRk_empty, ENat.toNat_zero] at a b
    push_cast at a b
    omega
  have hr : ∀ Y, M₁.eRk Y = M₂.eRk Y := fun Y => by
    have a := h₁.2.2 (σ ⁻¹' (univ \ Y))
    have b := h₂.2.2 (σ ⁻¹' (univ \ Y))
    rw [compl_image_preimage] at a b
    apply eRk_eq_of_toNat
    omega
  refine Matroid.ext_indep (h₁.2.1.trans h₂.2.1.symm) fun I _ => ?_
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite I.toFinite,
    Matroid.indep_iff_eRk_eq_encard_of_finite I.toFinite, hr]

lemma isDualVia_iff_eq {M : Matroid α} {M' : Matroid β} (σ : α ≃ β) (hE : M.E = univ) :
    IsDualVia M M' σ ↔ M' = M✶.mapEquiv σ :=
  ⟨fun h => eq_of_isDualVia h (isDualVia_mapEquiv hE σ), fun h => h ▸ isDualVia_mapEquiv hE σ⟩

lemma mapEquiv_isBase_compl {M : Matroid α} (hE : M.E = univ) (σ : α ≃ β) (B : Set α) :
    (M✶.mapEquiv σ).IsBase (univ \ σ '' B) ↔ M.IsBase B := by
  rw [Matroid.mapEquiv_isBase_iff, image_compl, Equiv.symm_image_image,
    Matroid.dual_isBase_iff (by rw [hE]; exact subset_univ _), hE,
    sdiff_sdiff_cancel_left (subset_univ B)]

/-- Theorem 23. -/
theorem dualVia_iff_isBase_compl (M : Matroid α) (M' : Matroid β) (σ : α ≃ β) (hE : M.E = univ)
    (hE' : M'.E = univ) :
    IsDualVia M M' σ ↔ ∀ B : Set α, M.IsBase B ↔ M'.IsBase (univ \ σ '' B) := by
  rw [isDualVia_iff_eq σ hE]
  constructor
  · rintro rfl B
    exact (mapEquiv_isBase_compl hE σ B).symm
  · intro h
    refine Matroid.ext_isBase (by rw [hE', Matroid.mapEquiv_ground_eq, Matroid.dual_ground, hE,
      image_univ_of_surjective σ.surjective]) fun Y _ => ?_
    rw [← compl_image_preimage σ Y, ← h, mapEquiv_isBase_compl hE]

/-- Theorem 20. -/
theorem rank_nullity_of_isDual {M : Matroid α} {M' : Matroid β} (h : IsDual M M') :
    ((M'.eRk univ).toNat : ℤ) = nullity M univ ∧ nullity M' univ = ((M.eRk univ).toNat : ℤ) := by
  obtain ⟨σ, h⟩ := h
  have a := h.2.2 univ
  rw [image_univ_of_surjective σ.surjective, sdiff_self, Matroid.eRk_empty, ENat.toNat_zero] at a
  push_cast at a
  have hc := ncard_univ_eq σ
  refine ⟨by omega, ?_⟩
  unfold nullity at a ⊢
  omega

/-- Theorem 21. -/
theorem isDual_symm' {M : Matroid α} {M' : Matroid β} (h : IsDual M M') : IsDual M' M := by
  obtain ⟨σ, h⟩ := h
  have hb := (dualVia_iff_isBase_compl M M' σ h.1 h.2.1).1 h
  refine ⟨σ.symm, (dualVia_iff_isBase_compl M' M σ.symm h.2.1 h.1).2 fun B' => ?_⟩
  rw [hb, image_compl, ← compl_eq_univ_sdiff, ← compl_eq_univ_sdiff, compl_compl,
    Equiv.image_symm_image]

/-- Theorem 22. -/
theorem exists_dual (M : Matroid α) (hE : M.E = univ) : ∃ M' : Matroid α, IsDualVia M M' (Equiv.refl α) :=
  ⟨M✶, hE, by rw [Matroid.dual_ground, hE], fun N => by
    simpa only [Equiv.coe_refl, image_id] using dual_eq hE N⟩

/-- Theorem 7. -/
theorem isBase_iff (M : Matroid α) (hE : M.E = univ) (B : Set α) :
    M.IsBase B ↔ (M.eRk B = M.eRk univ ∧ nullity M B = 0) := by
  have hu : M.eRk univ = M.eRank := by rw [← hE, Matroid.eRk_ground]
  constructor
  · intro hB
    refine ⟨by rw [hB.eRk_eq_eRank, hu], ?_⟩
    have := hB.indep.eRk_eq_encard
    rw [← cast_r, ← cast_ncard] at this
    norm_cast at this
    unfold nullity
    omega
  · rintro ⟨h1, h2⟩
    have hI : M.Indep B := by
      rw [Matroid.indep_iff_eRk_eq_encard_of_finite B.toFinite, ← cast_r, ← cast_ncard]
      unfold nullity at h2
      norm_cast
      omega
    exact hI.isBase_of_eRk_ge B.toFinite (by rw [← hu, h1])

/-- Theorem 8. -/
theorem exists_extend (M : Matroid α) {B N : Set α} (hB : M.IsBase B) (hN : M.Indep N) :
    ∃ N' : Set α, N' ⊆ B ∧ M.IsBase (N ∪ N') := by
  obtain ⟨B', hB', hNB', hB'NB⟩ := hN.exists_isBase_subset_union_isBase hB
  refine ⟨B' \ N, fun x hx => (hB'NB hx.1).resolve_left hx.2, ?_⟩
  rwa [union_sdiff_cancel hNB']

end WhitneyDualAbs

open WhitneyDualAbs in
theorem solution {α β : Type*} [Finite α] [Finite β] (M : Matroid α)
    (M' : Matroid β) (σ : α ≃ β) (hE : M.E = Set.univ) (hE' : M'.E = Set.univ) :
    IsDualVia M M' σ ↔ ∀ B : Set α, M.IsBase B ↔ M'.IsBase (Set.univ \ σ '' B) :=
  dualVia_iff_isBase_compl M M' σ hE hE'
