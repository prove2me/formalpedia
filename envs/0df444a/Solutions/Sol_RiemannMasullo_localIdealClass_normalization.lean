-- Prove2me | solution 1 for RiemannMasullo.localIdealClass_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T01:56:06.404216+00:00
-- url     : https://prove2.me/submissions/b3a2af58-d069-4616-b7d7-727f63f6d1eb

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
theorem _root_.solution (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    (x ∈ (v.adicCompletionIntegers F).units → localIdealClass F v x = 1) ∧
    (Valued.v x.val = WithZero.exp (-1 : ℤ) → localIdealClass F v x =
      ClassGroup.equivPic (𝓞 F) (ClassGroup.mk0
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) := by
  constructor
  · intro hx
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hx
    simp [localIdealClass, hx]
  · intro hx
    simp [localIdealClass, hx]
end RiemannMasullo
