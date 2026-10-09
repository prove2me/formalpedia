-- Prove2me | solution 1 for PiTensorProduct.isOpenMap_comap_of_quasiFinite
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T18:22:00.85796+00:00
-- url     : https://prove2.me/submissions/daf90748-8ed6-4ff1-9c38-adbff8742837

import Theorems.Thm_PrimeSpectrum_isOpenMap_comap_baseChange_of_quasiFinite_dominant_components
import Mathlib

section

set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators TensorProduct
noncomputable section

namespace PiTensorProduct

variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
  {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]

/-- The universal algebra map induced by a finite family of algebra maps. -/
def familyLift {B : Type*} [CommRing B] [Algebra A B]
    (e : ∀ i, R i →ₐ[A] B) : (⨂[A] i, R i) →ₐ[A] B :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra A ι B).compLinearMap
    (fun i => (e i).toLinearMap))
    (by simp)
    (by intro x y; simp [Finset.prod_mul_distrib])

@[simp] theorem familyLift_tprod {B : Type*} [CommRing B] [Algebra A B]
    (e : ∀ i, R i →ₐ[A] B) (x : ∀ i, R i) :
    familyLift e (tprod A x) = ∏ i, e i (x i) := by
  simp [familyLift, liftAlgHom, lift.tprod]

@[simp] theorem familyLift_single {B : Type*} [CommRing B] [Algebra A B]
    (e : ∀ i, R i →ₐ[A] B) (i : ι) (x : R i) :
    familyLift e (singleAlgHom i x) = e i x := by
  rw [singleAlgHom_apply, familyLift_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hji]
  · simp

theorem tprod_eq_prod_single (x : ∀ i, R i) :
    tprod A x = ∏ i, singleAlgHom i (x i) := by
  simp only [singleAlgHom_apply, ← tprod_prod]
  congr 1
  ext j
  simp

/-- Finitely many finitely generated algebras have a finitely generated tensor product. -/
theorem finiteType_family [∀ i, Algebra.FiniteType A (R i)] :
    Algebra.FiniteType A (⨂[A] i, R i) := by
  classical
  choose s hs using fun i => (Algebra.FiniteType.out (R := A) (A := R i))
  let T : Set (⨂[A] i, R i) := ⋃ i, singleAlgHom i '' (s i : Set (R i))
  have hT : T.Finite := Set.finite_iUnion fun i => (s i).finite_toSet.image _
  let D : Subalgebra A (⨂[A] i, R i) := Algebra.adjoin A T
  have hsingle (i : ι) (x : R i) : singleAlgHom i x ∈ D := by
    have hle : Algebra.adjoin A (s i : Set (R i)) ≤ D.comap (singleAlgHom i) := by
      apply Algebra.adjoin_le
      intro a ha
      exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩)
    rw [hs i] at hle
    exact hle (by trivial)
  refine ⟨hT.toFinset, ?_⟩
  rw [hT.coe_toFinset]
  apply top_unique
  intro x hx
  clear hx
  change x ∈ D
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      apply D.smul_mem
      rw [tprod_eq_prod_single]
      exact D.prod_mem fun i _ => hsingle i (x i)
  | add x y hx hy => exact D.add_mem hx hy

end PiTensorProduct

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct BigOperators
noncomputable section

namespace PiTensorProduct

variable {A ι κ : Type*} [CommRing A]
  {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]

/-- Reindexing finite tensor products preserves the full algebra structure. -/
def reindexAlgEquiv (e : ι ≃ κ) :
    (⨂[A] i, R i) ≃ₐ[A] (⨂[A] j, R (e.symm j)) := by
  refine AlgEquiv.ofLinearEquiv (reindex A R e) ?_ ?_
  · change reindex A R e (tprod A 1) = tprod A 1
    rw [reindex_tprod]
    rfl
  · intro x y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r x =>
        induction y using PiTensorProduct.induction_on with
        | smul_tprod s y =>
            simp only [smul_mul_assoc, mul_smul_comm, map_smul, tprod_mul_tprod, reindex_tprod]
            rfl
        | add y z hy hz => simp only [mul_add, map_add, hy, hz]
    | add x z hx hz => simp only [add_mul, map_add, hx, hz]

variable [Fintype ι] [DecidableEq ι]

/-- The empty tensor product is the base algebra, including its structural map. -/
def isEmptyAlgEquiv [IsEmpty ι] : (⨂[A] i, R i) ≃ₐ[A] A :=
  AlgEquiv.ofAlgHom (familyLift fun i => isEmptyElim i) (Algebra.ofId A _)
    (Subsingleton.elim _ _)
    (by
      apply algHom_ext
      intro i
      exact isEmptyElim i)

variable {T : Option ι → Type*} [∀ i, CommRing (T i)] [∀ i, Algebra A (T i)]

/-- Separate one factor from a finite family. -/
def optionTo :
    (⨂[A] i, T i) →ₐ[A] ((⨂[A] i, T (some i)) ⊗[A] T none) :=
  familyLift fun i => match i with
    | none => Algebra.TensorProduct.includeRight
    | some i => Algebra.TensorProduct.includeLeft.comp
        (singleAlgHom (R := A) (A := fun i => T (some i)) i)

def optionFrom :
    ((⨂[A] i, T (some i)) ⊗[A] T none) →ₐ[A] (⨂[A] i, T i) :=
  Algebra.TensorProduct.lift
    (familyLift fun i => singleAlgHom (some i)) (singleAlgHom none)
    (fun _ _ => Commute.all _ _)

@[simp] theorem optionTo_none (x : T none) :
    optionTo (A := A) (T := T) (singleAlgHom none x) =
      (Algebra.TensorProduct.includeRight : T none →ₐ[A] _) x := by
  exact familyLift_single _ none x

@[simp] theorem optionTo_some (i : ι) (x : T (some i)) :
    optionTo (A := A) (T := T) (singleAlgHom (some i) x) =
      (Algebra.TensorProduct.includeLeft : (⨂[A] i, T (some i)) →ₐ[A] _)
        (singleAlgHom i x) := by
  exact familyLift_single _ (some i) x

@[simp] theorem optionFrom_right (x : T none) :
    optionFrom (A := A) (T := T)
      ((Algebra.TensorProduct.includeRight : T none →ₐ[A] _) x) =
      singleAlgHom none x := by
  simp [optionFrom]

@[simp] theorem optionFrom_left_single (i : ι) (x : T (some i)) :
    optionFrom (A := A) (T := T)
      ((Algebra.TensorProduct.includeLeft : (⨂[A] i, T (some i)) →ₐ[A] _)
      (singleAlgHom i x)) = singleAlgHom (some i) x := by
  simp only [optionFrom, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.lift_tmul, map_one, mul_one, familyLift_single]

/-- An indexed tensor product with one extra index is the binary tensor product
of the old indexed tensor product and the new factor. -/
def optionAlgEquiv :
    (⨂[A] i, T i) ≃ₐ[A] ((⨂[A] i, T (some i)) ⊗[A] T none) :=
  AlgEquiv.ofAlgHom optionTo optionFrom
    (by
      apply Algebra.TensorProduct.ext
      · apply algHom_ext
        intro i
        ext x
        simp only [AlgHom.comp_apply, AlgHom.id_apply, optionFrom_left_single, optionTo_some]
      · ext x
        change optionTo (A := A) (T := T)
          (optionFrom (A := A) (T := T) (Algebra.TensorProduct.includeRight x)) = _
        rw [optionFrom_right, optionTo_none]
        rfl)
    (by
      apply algHom_ext
      intro i
      ext x
      cases i <;>
        simp only [AlgHom.comp_apply, AlgHom.id_apply, optionTo_none, optionTo_some,
          optionFrom_right, optionFrom_left_single])

end PiTensorProduct

end
end


section

set_option autoImplicit false
open TopologicalSpace
open scoped Topology
noncomputable section

/-- An open map from a Noetherian space to an irreducible space maps every
irreducible component densely. -/
theorem IsOpenMap.dense_image_irreducible_component
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [PreirreducibleSpace Y] {f : X → Y}
    (hf : IsOpenMap f) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    Dense (f '' Z) := by
  obtain ⟨U, hU, hUne, hUZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  exact ((hf U hU).dense (hUne.image f)).mono (Set.image_mono hUZ)

/-- The component-dominance premise needed for universal openness follows
from ordinary openness over an integral base. -/
theorem PrimeSpectrum.dense_image_components_of_isOpenMap
    {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (hf : IsOpenMap (PrimeSpectrum.comap (algebraMap A B)))
    (Z : Set (PrimeSpectrum B)) (hZ : Z ∈ irreducibleComponents (PrimeSpectrum B)) :
    Dense (PrimeSpectrum.comap (algebraMap A B) '' Z) := by
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact hf.dense_image_irreducible_component Z hZ

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology
noncomputable section

namespace PrimeSpectrum

/-- Openness of a structural spectrum map is invariant under algebra isomorphism. -/
theorem isOpenMap_comap_of_algEquiv
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (e : B ≃ₐ[A] C) (h : IsOpenMap (comap (algebraMap A C))) :
    IsOpenMap (comap (algebraMap A B)) := by
  have he : e.symm.toRingHom.comp (algebraMap A C) = algebraMap A B :=
    e.symm.toAlgHom.comp_algebraMap
  rw [← he, comap_comp]
  exact h.comp (isHomeomorph_comap_of_bijective e.symm.bijective).isOpenMap

end PrimeSpectrum

namespace PiTensorProduct

universe uA uI uR

/-- Finite indexed products of universally open affine maps are open.
The universal input only has to cover affine base changes. -/
theorem isOpenMap_comap_of_open_baseChanges
    (A : Type uA) [CommRing A]
    (ι : Type uI) [Finite ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    (hbase : ∀ i (B : Type (max uA uI uR)) [CommRing B] [Algebra A B],
      IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] R i)))) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (⨂[A] i, R i))) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  revert R
  refine Fintype.induction_empty_option
    (P := fun κ _ => ∀ (T : κ → Type uR) [∀ i, CommRing (T i)] [∀ i, Algebra A (T i)],
      (∀ i (B : Type (max uA uI uR)) [CommRing B] [Algebra A B],
        IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] T i)))) →
      IsOpenMap (PrimeSpectrum.comap (algebraMap A (⨂[A] i, T i)))) ?_ ?_ ?_ ι
  · intro α β _ e ih R _ _ hbase
    exact PrimeSpectrum.isOpenMap_comap_of_algEquiv
      (reindexAlgEquiv (A := A) (R := R) e.symm)
      (ih (fun i => R (e i)) (fun i => hbase (e i)))
  · intro R _ _ hbase
    apply PrimeSpectrum.isOpenMap_comap_of_algEquiv (isEmptyAlgEquiv (A := A) (R := R))
    intro U hU
    have he : PrimeSpectrum.comap (algebraMap A A) '' U = U := by
      ext x
      simp
    rwa [he]
  · intro α _ ih R _ _ hbase
    let S := ⨂[A] i : α, R (some i)
    have hS : IsOpenMap (PrimeSpectrum.comap (algebraMap A S)) :=
      ih (fun i => R (some i)) (fun i => hbase (some i))
    have hstep : IsOpenMap (PrimeSpectrum.comap (algebraMap S (S ⊗[A] R none))) :=
      hbase none S
    have hprod : IsOpenMap (PrimeSpectrum.comap (algebraMap A (S ⊗[A] R none))) := by
      rw [IsScalarTower.algebraMap_eq A S (S ⊗[A] R none), PrimeSpectrum.comap_comp]
      exact hS.comp hstep
    exact PrimeSpectrum.isOpenMap_comap_of_algEquiv
      (optionAlgEquiv (A := A) (T := R)) hprod

/-- The complete finite-family reduction to the single-algebra normal-base
universal-openness criterion. Component dominance is proved from ordinary openness. -/
theorem finite_tensor_open_of_dominant_baseChange
    (A : Type uA) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (hcriterion : ∀ (R : Type uR) [CommRing R] [Algebra A R]
      [Algebra.FiniteType A R] [Algebra.QuasiFinite A R],
      (∀ Z ∈ irreducibleComponents (PrimeSpectrum R),
        Dense (PrimeSpectrum.comap (algebraMap A R) '' Z)) →
      ∀ (B : Type (max uA uI uR)) [CommRing B] [Algebra A B],
        IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] R))))
    (ι : Type uI) [Finite ι]
    (R : ι → Type uR) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.FiniteType A (R i)]
    (hopen : ∀ i, IsOpenMap (PrimeSpectrum.comap (algebraMap A (R i))))
    (hquasi : ∀ i, Algebra.QuasiFinite A (R i)) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (⨂[A] i, R i))) := by
  apply isOpenMap_comap_of_open_baseChanges
  intro i B _ _
  letI : Algebra.QuasiFinite A (R i) := hquasi i
  exact hcriterion (R i)
    (PrimeSpectrum.dense_image_components_of_isOpenMap (hopen i)) B

end PiTensorProduct

end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology

theorem solution
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (ι : Type*) [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.FiniteType A (R i)]
    (hopen : ∀ i, IsOpenMap (PrimeSpectrum.comap (algebraMap A (R i))))
    (hquasi : ∀ i, Algebra.QuasiFinite A (R i)) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap A (⨂[A] i, R i))) := by
  exact PiTensorProduct.finite_tensor_open_of_dominant_baseChange A
    (PrimeSpectrum.isOpenMap_comap_baseChange_of_quasiFinite_dominant_components A)
    ι R hopen hquasi
