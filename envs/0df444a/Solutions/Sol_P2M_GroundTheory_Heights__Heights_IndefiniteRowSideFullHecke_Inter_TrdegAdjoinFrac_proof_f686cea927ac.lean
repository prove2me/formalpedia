-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_TrdegAdjoinFrac_proof_f686cea927ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:59:18.476212+00:00
-- url     : https://prove2.me/submissions/06615b6e-7a00-49fe-ac22-e6c83a9854b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTrdegAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTrdegAdjoinFrac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace TrdegAdjoinFrac
theorem _root_.solution : TrdegAdjoinFrac.Statement := by
  intro D _ _ _ E _ _ _ _ s hinj
  set A := Algebra.adjoin ℤ
    (Set.range (fun d : D => algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d)) ∪ s) with hA
  set B := Algebra.adjoin (FractionRing D) s with hB
  have hmem : ∀ c : D, algebraMap (FractionRing D) E (algebraMap D (FractionRing D) c) ∈ A :=
    fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩)
  have hs : ∀ x ∈ s, x ∈ A := fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hAB : ∀ x ∈ A, x ∈ B := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨d, rfl⟩ | hy
      · exact B.algebraMap_mem _
      · exact Algebra.subset_adjoin hy
    | algebraMap n => rw [eq_intCast]; exact intCast_mem B n
    | add y z _ _ hy hz => exact B.add_mem hy hz
    | mul y z _ _ hy hz => exact B.mul_mem hy hz

  have key : ∀ x ∈ B, ∃ d : D, d ≠ 0 ∧
      algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) * x ∈ A := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hs x hx⟩
    | algebraMap r =>
      obtain ⟨⟨a, m⟩, h⟩ := IsLocalization.surj (nonZeroDivisors D) r
      refine ⟨m, nonZeroDivisors.ne_zero m.2, ?_⟩
      rw [← map_mul, mul_comm, h]
      exact hmem a
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨e, he, hey⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      have : algebraMap (FractionRing D) E (algebraMap D (FractionRing D) (d * e)) * (x + y) =
          algebraMap (FractionRing D) E (algebraMap D (FractionRing D) e) *
              (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) * x) +
            algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) *
              (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) e) * y) := by
        simp only [map_mul]; ring
      rw [this]
      exact A.add_mem (A.mul_mem (hmem e) hdx) (A.mul_mem (hmem d) hey)
    | mul x y _ _ hx hy =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨e, he, hey⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      have : algebraMap (FractionRing D) E (algebraMap D (FractionRing D) (d * e)) * (x * y) =
          (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) * x) *
            (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) e) * y) := by
        simp only [map_mul]; ring
      rw [this]
      exact A.mul_mem hdx hey

  have hZD : @FaithfulSMul ℤ D Algebra.toSMul := (faithfulSMul_iff_algebraMap_injective ℤ D).2 hinj
  have tZDΦ : @IsScalarTower ℤ D (FractionRing D) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have h1 : Algebra.trdeg ℤ D = Algebra.trdeg ℤ (FractionRing D) := by
    have e := trdeg_add_eq ℤ D (A := FractionRing D)
    have := IsLocalization.isAlgebraic (FractionRing D) (nonZeroDivisors D)
    rw [trdeg_eq_zero (R := D) (A := FractionRing D), add_zero] at e
    exact e

  have : FaithfulSMul (FractionRing D) B :=
    (faithfulSMul_iff_algebraMap_injective (FractionRing D) B).2 (algebraMap (FractionRing D) B).injective
  have hZΦ : @FaithfulSMul ℤ (FractionRing D) Algebra.toSMul := by
    refine (faithfulSMul_iff_algebraMap_injective ℤ (FractionRing D)).2 ?_
    have : algebraMap ℤ (FractionRing D) = (algebraMap D (FractionRing D)).comp (algebraMap ℤ D) :=
      RingHom.ext_int _ _
    rw [this]
    exact (IsFractionRing.injective D (FractionRing D)).comp hinj
  have tZΦB : @IsScalarTower ℤ (FractionRing D) B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have h2 : Algebra.trdeg ℤ (FractionRing D) + Algebra.trdeg (FractionRing D) B = Algebra.trdeg ℤ B :=
    trdeg_add_eq ℤ (FractionRing D) (A := B)

  let f : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra A B := f.toAlgebra
  have tZAB : @IsScalarTower ℤ A B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have hZE : Function.Injective (algebraMap ℤ E) := by
    have : algebraMap ℤ E = ((algebraMap (FractionRing D) E).comp
        (algebraMap D (FractionRing D))).comp (algebraMap ℤ D) := RingHom.ext_int _ _
    rw [this]
    exact (algebraMap (FractionRing D) E).injective.comp
      ((IsFractionRing.injective D (FractionRing D)).comp hinj)
  have hZA : @FaithfulSMul ℤ A Algebra.toSMul := by
    refine (faithfulSMul_iff_algebraMap_injective ℤ A).2 ?_
    intro m n hmn
    exact hZE (congrArg (fun a : A => (a : E)) hmn)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 (by
    intro a b h
    exact Subtype.ext (congrArg Subtype.val h :))
  have : Algebra.IsAlgebraic A B := by
    refine ⟨fun z => ?_⟩
    obtain ⟨d, hd, hdz⟩ := key z z.2
    have hne : algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap (FractionRing D) E).injective,
        map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))]
      exact hd
    have hy : algebraMap A B ⟨_, hmem d⟩ ∈ nonZeroDivisors B := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      intro h0
      exact hne (congrArg Subtype.val h0 :)
    refine IsAlgebraic.of_mul hy (isAlgebraic_algebraMap _) ?_
    have : algebraMap A B ⟨_, hmem d⟩ * z = algebraMap A B ⟨_, hdz⟩ := Subtype.ext rfl
    rw [this]
    exact isAlgebraic_algebraMap _
  have h3 : Algebra.trdeg ℤ A = Algebra.trdeg ℤ B := by
    have e := trdeg_add_eq ℤ A (A := B)
    rw [trdeg_eq_zero (R := A) (A := B), add_zero] at e
    exact e
  rw [h3, ← h2, h1]
end TrdegAdjoinFrac
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
