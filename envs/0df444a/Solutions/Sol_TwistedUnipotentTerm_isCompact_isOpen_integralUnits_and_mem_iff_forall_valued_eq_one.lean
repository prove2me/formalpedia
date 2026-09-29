-- Prove2me | solution 1 for TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6dfe6c45-2d8c-5947-af0a-11fd33dfa34b

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one

set_option autoImplicit false

namespace P2mIntegralUnitsStructure

open NumberField IsDedekindDomain
open scoped TensorProduct

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

noncomputable abbrev E : (L ⊗[K] v.adicCompletion K) ≃ₐ[L] (Π w : v.Extension (𝓞 L), w.1.adicCompletion L) :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

noncomputable def Ψ : (L ⊗[K] v.adicCompletion K)ˣ ≃* (Π w : v.Extension (𝓞 L), (w.1.adicCompletion L)ˣ) :=
  (Units.mapEquiv (E K L v).toRingEquiv.toMulEquiv).trans MulEquiv.piUnits

theorem semiLocalUnitComponent_eq (w : v.Extension (𝓞 L)) (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ = Ψ K L v ζ w :=
  Units.ext rfl

open scoped TensorProduct.RightActions in

theorem mem_semiLocalIntegers_iff (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), E K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  rfl

omit [NumberField L] in

theorem mem_integralUnits_iff (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v ↔
      (ζ : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        ((ζ⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          AutomorphicForm.semiLocalIntegers K L v := by
  rw [AutomorphicForm.TransversalMeasure.integralUnits, Submonoid.mem_units_iff]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := (AlgHom.mem_range _).1 h1
    obtain ⟨b, hb⟩ := (AlgHom.mem_range _).1 h2
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨(AlgHom.mem_range _).2 ⟨a, ha⟩, (AlgHom.mem_range _).2 ⟨b, hb⟩⟩

theorem mem_integralUnits_iff_forall_valued_eq_one (ζ : (L ⊗[K] v.adicCompletion K)ˣ) :
    ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v ↔
      ∀ w : v.Extension (𝓞 L), Valued.v ((Ψ K L v ζ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) = 1 := by
  rw [mem_integralUnits_iff, mem_semiLocalIntegers_iff, mem_semiLocalIntegers_iff]
  constructor
  · rintro ⟨h1, h2⟩ w
    have hle : Valued.v ((Ψ K L v ζ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h1 w)
    have hle' : Valued.v ((Ψ K L v ζ⁻¹ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h2 w)
    rw [map_inv, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀] at hle'
    have hne : Valued.v ((Ψ K L v ζ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    exact le_antisymm hle ((inv_le_one₀ (zero_lt_iff.2 hne)).1 hle')
  · intro h
    refine ⟨fun w => ?_, fun w => ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h w).le
    · refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      show Valued.v ((Ψ K L v ζ⁻¹ w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ≤ 1
      rw [map_inv, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, h w, inv_one]

open scoped TensorProduct.RightActions in
omit [NumberField L] in

theorem coe_integralUnits_eq_preimage :
    (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      Units.embedProduct _ ⁻¹'
        ((AutomorphicForm.semiLocalIntegers K L v) ×ˢ
          (MulOpposite.unop ⁻¹' AutomorphicForm.semiLocalIntegers K L v)) :=
  rfl

open scoped TensorProduct.RightActions in

theorem isOpen_integralUnits :
    IsOpen (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  rw [coe_integralUnits_eq_preimage]
  exact ((AutomorphicForm.isOpen_semiLocalIntegers K L v).prod
    ((AutomorphicForm.isOpen_semiLocalIntegers K L v).preimage MulOpposite.continuous_unop)).preimage
      Units.continuous_embedProduct

open scoped TensorProduct.RightActions in

theorem isCompact_integralUnits :
    IsCompact (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensor K L (v.adicCompletion K)
  have h : IsCompact
      (((HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range.toSubmonoid :
          Submonoid (L ⊗[K] v.adicCompletion K)) : Set (L ⊗[K] v.adicCompletion K)) :=
    AutomorphicForm.isCompact_semiLocalIntegers K L v
  exact Submonoid.units_isCompact h

end P2mIntegralUnitsStructure

open NumberField IsDedekindDomain
open scoped TensorProduct

open P2mIntegralUnitsStructure in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ∧
      IsOpen (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) ∧
      ∀ ζ : (L ⊗[K] v.adicCompletion K)ˣ,
        ζ ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v ↔
          ∀ w : v.Extension (𝓞 L),
            Valued.v ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w ζ : (w.1.adicCompletion L)ˣ) :
              w.1.adicCompletion L) = 1 := by
  refine ⟨isCompact_integralUnits K L v, isOpen_integralUnits K L v, fun ζ => ?_⟩
  rw [mem_integralUnits_iff_forall_valued_eq_one]
  simp only [semiLocalUnitComponent_eq]

end S_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one
end P2MW
export P2MW.S_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one (solution)
