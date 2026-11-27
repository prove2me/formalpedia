-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalCurvePointDVR_proof_202d2ba6afb4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:05:25.888125+00:00
-- url     : https://prove2.me/submissions/05070aba-1db5-476b-9c10-56e4aea38f46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurvePointDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalCurvePointDVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace NormalCurvePointDVR
theorem _root_.solution : NormalCurvePointDVR.Statement := by
  intro σ _ I w hI hic hdim hw
  have : I.IsPrime := hI
  let m : Ideal (MvPolynomial σ ℂ) := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  let S := Localization.AtPrime m
  let T := S ⧸ I.map (algebraMap (MvPolynomial σ ℂ) S)
  let A := MvPolynomial σ ℂ ⧸ I
  have hIm : I ≤ m := fun f hf ↦ RingHom.mem_ker.2 (hw f hf)
  let P : Ideal A := m.map (Ideal.Quotient.mk I)
  have hmem : ∀ f, Ideal.Quotient.mk I f ∈ P ↔ f ∈ m := fun f ↦ Ideal.mem_quotient_iff_mem hIm
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIm)

  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.2 (by rw [hdim])
  have : Ring.DimensionLEOne A := ⟨fun hp0 hp ↦ hp.isMaximal_of_ne_bot hp0⟩
  have : IsDedekindRing A := { toIsIntegralClosure := hic }

  have hP0 : P ≠ ⊥ := by
    intro h0
    have hmI : m ≤ I := fun f hf ↦ by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h0]
      exact (hmem f).2 hf
    have hmax : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z ↦ ⟨C z, by simp⟩)
    have hfield : IsField A := (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).1 (le_antisymm hIm hmI ▸ hmax)
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at this
    exact_mod_cast this

  have hsub : Algebra.algebraMapSubmonoid A m.primeCompl = P.primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact fun h ↦ hf ((hmem f).1 h)
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f, fun h ↦ hx ((hmem f).2 h), rfl⟩
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid A m.primeCompl) T := inferInstance
  have hlocP : IsLocalization.AtPrime T P := by
    change IsLocalization P.primeCompl T
    rw [← hsub]
    exact hloc
  have hdom : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  exact ⟨hdom, IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 T⟩
end NormalCurvePointDVR
end GroundTheory.Heights₂.Heights
