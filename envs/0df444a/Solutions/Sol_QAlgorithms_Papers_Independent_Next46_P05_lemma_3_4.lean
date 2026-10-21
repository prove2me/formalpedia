-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P05.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:31:26.036192+00:00
-- url     : https://prove2.me/submissions/b4cfa30e-5b13-4623-b7ff-dc86b8ddfaa6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P05
open QAlgorithms.Papers.Independent.Next46.P05

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Frontier30.P26
  (bracketSpan innerWord Invariant ClosedCone GeneratingInvariantCone CompactlyEmbedded)

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance 100] LieRing.ofAssociativeRing

section G62EHelpers

attribute [local instance] QAlgorithms.Papers.Independent.Frontier30.P26.lieNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Frontier30.P26.lieNormedSpace

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

theorem g62e_word_cons (y : G) (ys : List G) (z : G) :
    innerWord (y :: ys) z = innerWord [y] (innerWord ys z) := rfl

theorem g62e_exp_eq (y z : G) :
    innerWord [y] z = QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates.expAd y z := by
  show (NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y))) z = _
  set T : G →L[ℝ] G := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y) with hT
  have hs := (NormedSpace.expSeries_summable' (𝕂 := ℝ) T).hasSum.map
    (ContinuousLinearMap.apply ℝ G z) (ContinuousLinearMap.apply ℝ G z).continuous
  rw [NormedSpace.exp_eq_tsum ℝ]
  unfold QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates.expAd
  have hpow : ∀ n : ℕ, (T ^ n) z =
      ((QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates.adMap y) ^ n) z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [hT, QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates.adMap]
  have e : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • T ^ n) z =
      ∑' n : ℕ, ((ContinuousLinearMap.apply ℝ G z) ∘
        fun n : ℕ => ((n.factorial : ℝ)⁻¹) • T ^ n) n := hs.tsum_eq.symm
  show (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • T ^ n) z = _
  rw [e]
  congr 1
  ext n
  simp [hpow]

theorem g62e_word_image (W : Set G) (hi : Invariant W) (xs : List G) :
    innerWord xs '' W = W := by
  induction xs with
  | nil =>
    ext z
    simp [innerWord]
  | cons y ys ih =>
    have h1 : (innerWord (y :: ys) : G → G) =
        QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates.expAd y ∘ innerWord ys := by
      funext z
      rw [Function.comp_apply, g62e_word_cons, g62e_exp_eq]
    rw [h1, Set.image_comp, ih]
    exact hi y

theorem g62e_word_tau (tau : G ≃ₗ⁅ℝ⁆ G) (xs : List G) (hxs : ∀ x ∈ xs, tau x = x) (z : G) :
    tau (innerWord xs z) = innerWord xs (tau z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons y ys ih =>
    rw [g62e_word_cons y ys z, g62e_word_cons y ys (tau z), ← ih (fun x hx => hxs x (List.mem_cons_of_mem _ hx))]
    have hy : tau y = y := hxs y List.mem_cons_self
    show tau ((NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y)))
      (innerWord ys z)) = (NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y)))
      (tau (innerWord ys z))
    set A : G →L[ℝ] G := LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y)
    set T : G →L[ℝ] G := LinearMap.toContinuousLinearMap (tau : G →ₗ[ℝ] G) with hT
    have hc : Commute T A := by
      ext w
      simp only [A, hT, ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap',
        LieAlgebra.ad_apply]
      show tau ⁅y, w⁆ = ⁅y, tau w⁆
      rw [LieEquiv.map_lie, hy]
    have := congrArg (fun F : G →L[ℝ] G => F (innerWord ys z)) hc.exp_right.eq
    simpa [hT] using this

end G62EHelpers

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P05.lieNormedSpace

section LieStatements

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Lemma 3.4, PDF p. 18. No pointedness, generating, simplicity, or hyperbolicity added. -/
theorem solution (W : Set G) (hw : ClosedCone W) (hi : Invariant W)
    (tau phi : G ≃ₗ⁅ℝ⁆ G) (ht : Function.Involutive tau)
    (hr : tau '' W = Neg.neg '' W) (h1 h2 : G)
    (hf1 : tau h1 = h1) (hf2 : tau h2 = h2) (hp : InnerFixed tau phi)
    (hh : phi h1 = h2) :
    phi '' (causalAlgebra W tau h1 : Set G) = (causalAlgebra W tau h2 : Set G) ∧
      Nonempty (causalAlgebra W tau h1 ≃ₗ⁅ℝ⁆ causalAlgebra W tau h2) := by
  obtain ⟨xs, hxs, hphi⟩ := hp
  have hW := g62e_word_image W hi xs
  have hpW : ∀ x, phi x ∈ W ↔ x ∈ W := by
    intro x
    constructor
    · intro hx
      rw [← hW] at hx
      obtain ⟨w, hw, hwx⟩ := hx
      rw [hphi] at hwx
      rwa [← phi.injective hwx]
    · intro hx
      rw [← hphi, ← hW]
      exact ⟨x, hx, rfl⟩
  have htau : ∀ x, tau (phi x) = phi (tau x) := by
    intro x
    rw [← hphi, ← hphi]
    exact g62e_word_tau tau xs hxs x
  have hslice : ∀ t x, phi x ∈ causalSlice W tau h2 t ↔ x ∈ causalSlice W tau h1 t := by
    intro t x
    simp only [causalSlice, derivationSlice, Set.mem_setOf_eq, Set.mem_image,
      LieAlgebra.ad_apply]
    have e1 : (∃ w, w ∈ W ∧ t • w = phi x) ↔ (∃ w, w ∈ W ∧ t • w = x) := by
      constructor
      · rintro ⟨w, hw, hwx⟩
        refine ⟨phi.symm w, (hpW _).1 (by simpa using hw), phi.injective ?_⟩
        rw [map_smul]; simpa using hwx
      · rintro ⟨w, hw, rfl⟩
        exact ⟨phi w, (hpW w).2 hw, by rw [map_smul]⟩
    have e2 : tau (phi x) = -phi x ↔ tau x = -x := by
      rw [htau, ← map_neg]
      exact phi.injective.eq_iff
    have e3 : ⁅h2, phi x⁆ = t • phi x ↔ ⁅h1, x⁆ = t • x := by
      rw [← hh, ← LieEquiv.map_lie, ← map_smul]
      exact phi.injective.eq_iff
    rw [e1, e2, e3]
  have himg : ∀ t, phi '' causalSlice W tau h1 t = causalSlice W tau h2 t := by
    intro t
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hslice t x).2 hx
    · intro hy
      refine ⟨phi.symm y, (hslice t _).1 (by simpa using hy), by simp⟩
  have hmap : (causalAlgebra W tau h1).map (phi : G →ₗ⁅ℝ⁆ G) = causalAlgebra W tau h2 := by
    unfold causalAlgebra
    rw [LieSubalgebra.map_lieSpan, Set.image_union]
    congr 2
    · exact himg (-1)
    · exact himg 1
  refine ⟨?_, ⟨LieEquiv.ofSubalgebras _ _ phi hmap⟩⟩
  rw [← hmap]
  ext x
  simp only [Set.mem_image, SetLike.mem_coe, LieSubalgebra.mem_map]
  rfl
