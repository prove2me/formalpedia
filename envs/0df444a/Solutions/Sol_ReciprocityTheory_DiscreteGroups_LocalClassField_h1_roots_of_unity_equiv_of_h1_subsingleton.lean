-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.h1_roots_of_unity_equiv_of_h1_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:23.858012+00:00
-- url     : https://prove2.me/submissions/d6c4b353-6542-4b10-a07c-035e111fbb65

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_Kummer
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_adm
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_units_to_invariants_prime_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_units_to_invariants_prime_surjective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_power_map_h0_unitsToInvariants
import Theorems.Thm_ReciprocityTheory_Coh_low_degree_long_exact_sequence


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
open Kummer
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
    (h90 : Subsingleton (H1 (kbarRep p K))) :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  obtain ⟨δ₀, δ₁, -, -, -, -, e2, e3, -⟩ :=
    low_degree_long_exact_sequence ℤ (GK p K) (muT p K n) (kT p K) (kT p K) (iP K hζ) (pP p K n) (adm K hζ)
  have h90' : Subsingleton (ReciprocityTheory.Gal.H1 (kT p K).rho) := h90
  have hs : Function.Surjective δ₀ := fun y => (e3 y).1 (Subsingleton.elim _ _)
  let ψ : Kˣ →* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    AddMonoidHom.toMultiplicativeRight (δ₀.toAddMonoidHom.comp (unitsToInvariants' p K))
  have hψ : ∀ a : Kˣ, ψ a = Multiplicative.ofAdd (δ₀ (unitsToInvariants' p K (Additive.ofMul a))) := fun a => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hs y.toAdd
    obtain ⟨a, rfl⟩ := units_to_invariants_prime_surjective p K x
    exact ⟨a.toMul, hx⟩
  have hker : ψ.ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro ha
      have ha' : δ₀ (unitsToInvariants' p K (Additive.ofMul a)) = 0 := ha
      obtain ⟨y, hy⟩ := (e2 _).1 ha'
      obtain ⟨b, rfl⟩ := units_to_invariants_prime_surjective p K y
      refine ⟨b.toMul, ?_⟩
      have := (power_map_h0_unitsToInvariants p K n b.toMul).symm.trans hy
      exact units_to_invariants_prime_injective p K this
    · rintro ⟨b, rfl⟩
      show δ₀ (unitsToInvariants' p K (Additive.ofMul (b ^ n))) = 0
      exact (e2 _).2 ⟨_, power_map_h0_unitsToInvariants p K n b⟩
  have E1 : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  exact ⟨(h1ScalarEquiv (charRep (cycK p K n)) (muRep p K n) fun _ _ => rfl).trans (MulEquiv.toAdditiveLeft E1).symm⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
