-- Prove2me | solution 1 for P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:28.607858+00:00
-- url     : https://prove2.me/submissions/c847ee21-56db-4ddc-93b9-507fd6ed48be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section Red
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
private lemma mk_mul_reduction_eq_mk {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    redP P a * Ideal.Quotient.mk P.asIdeal s = Ideal.Quotient.mk P.asIdeal r := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, h, by
      field_simp⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h', hc'⟩ := hex.choose_spec
  have hs'0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 :=
    fun h0 => hs' (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hE : algebraMap (𝓞 E) E (s' * r) = algebraMap (𝓞 E) E (s * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have hO : s' * r = s * r' := FaithfulSMul.algebraMap_injective (𝓞 E) E hE
  have hQ : Ideal.Quotient.mk P.asIdeal s' * Ideal.Quotient.mk P.asIdeal r =
      Ideal.Quotient.mk P.asIdeal s * Ideal.Quotient.mk P.asIdeal r' := by
    rw [← map_mul, ← map_mul, hO]
  apply mul_left_cancel₀ hs'0
  rw [hQ, ← hc']
  ring
end Red
end PI.TwistedEisensteinNonvanishing.W
end
end

set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a * b) = redP P a * redP P b := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, h⟩ := ha
  obtain ⟨r', s', hs', h'⟩ := hb
  have hss : s * s' ∉ P.asIdeal := fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'
  have hab : algebraMap (𝓞 E) E (s * s') * (a * b) = algebraMap (𝓞 E) E (r * r') := by
    rw [map_mul, map_mul, ← h, ← h']
    ring
  have h1 := mk_mul_reduction_eq_mk P hss hab
  have ha' := mk_mul_reduction_eq_mk P hs h
  have hb' := mk_mul_reduction_eq_mk P hs' h'
  have hss0 : Ideal.Quotient.mk P.asIdeal (s * s') ≠ 0 :=
    fun h0 => hss (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  apply mul_right_cancel₀ hss0
  rw [h1, map_mul, map_mul, ← ha', ← hb']
  ring
end PI.TwistedEisensteinNonvanishing.W
