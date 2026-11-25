-- Prove2me | solution 1 for PI.FinOrdRedOne.Bridge.natCast_not_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:39:59.507706+00:00
-- url     : https://prove2.me/submissions/bd71dc11-4abe-42af-8a85-33c4375742be

import Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_Bridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Bridge
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal WithZero
variable {E : Type} [Field E] [NumberField E]
namespace PI.FinOrdRedOne.Bridge
theorem _root_.solution (p : ℕ) (hp : p.Prime) (hU : Unram E p) (P : HeightOneSpectrum (𝓞 E))
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) : (p : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  have hle : span {(p : ℤ)} ≤ P.asIdeal.comap (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact hpP
  have hne : P.asIdeal.comap (algebraMap ℤ (𝓞 E)) ≠ ⊤ := (P.isPrime.comap _).ne_top
  have heq : span {(p : ℤ)} = P.asIdeal.comap (algebraMap ℤ (𝓞 E)) := hspan.eq_of_le hne hle
  have hlo : P.asIdeal.LiesOver (span {(p : ℤ)}) := ⟨heq⟩
  have he : P.asIdeal.ramificationIdx ℤ = 1 := @hU P.asIdeal P.isPrime hlo
  have hbot : span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have := P.isPrime
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P.asIdeal hbot] at he
  have hmap : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hle
  have hiff := Ideal.ramificationIdx'_ne_one_iff (p := span {(p : ℤ)}) (P := P.asIdeal) hmap
  intro hsq
  apply hiff.mpr _ he
  rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_le, Set.singleton_subset_iff]
  exact hsq
end PI.FinOrdRedOne.Bridge
