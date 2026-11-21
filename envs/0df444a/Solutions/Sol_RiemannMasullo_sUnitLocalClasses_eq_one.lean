-- Prove2me | solution 1 for RiemannMasullo.sUnitLocalClasses_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T01:55:55.800292+00:00
-- url     : https://prove2.me/submissions/e77ac9d8-cb78-417b-9eb0-0e262faa69f2

module
public import Mathlib
public import Definitions.Def_RiemannMasullo_LocalIdealClasses

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open RiemannMasullo
open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct
variable (F : Type*) [Field F] [NumberField F]
local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
open scoped Classical
local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F
local notation "LocalClass(" F ", " v ")" =>
  (HeightOneSpectrum.adicCompletion F v)ˣ ⧸ Submonoid.units (Submonoid.ofClass (HeightOneSpectrum.adicCompletionIntegers F v))
namespace RiemannMasullo
theorem _root_.solution (S T : Finset (Primes(F))) (h : S ⊆ T)
    (u : (T : Set (Primes(F))).unit F) :
    sUnitLocalClasses F T (T \ S) u = 1 ↔ u.val ∈ (S : Set (Primes(F))).unit F := by
  have local_eq_one (v : ↥(T \ S)) :
      sUnitLocalClasses F T (T \ S) u v = 1 ↔ v.val.valuation F (u.val : F) = 1 := by
    let x := Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom u.val
    change (QuotientGroup.mk x : LocalClass(F, v.val)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := x)).trans ?_
    change Valued.v ((u.val : F) : v.val.adicCompletion F) = 1 ↔ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  change _ ↔ ∀ v : Primes(F), v ∉ S → v.valuation F (u.val : F) = 1
  constructor
  · intro hu v hvS
    by_cases hv : v ∈ T \ S
    · let w : ↥(T \ S) := ⟨v, hv⟩
      exact (local_eq_one w).mp (congrFun hu w)
    · apply u.property v
      change v ∉ T
      rw [← Finset.sdiff_union_of_subset h, Finset.mem_union]
      exact fun hvT ↦ hvT.elim hv hvS
  · intro hu
    funext v
    exact (local_eq_one v).mpr (hu v.val (Finset.mem_sdiff.mp v.property).2)
end RiemannMasullo
