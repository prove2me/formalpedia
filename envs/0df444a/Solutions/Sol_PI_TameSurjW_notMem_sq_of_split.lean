-- Prove2me | solution 1 for PI.TameSurjW.notMem_sq_of_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:45.91902+00:00
-- url     : https://prove2.me/submissions/90ec8e18-0ba0-408f-8d64-e0fbf1527647

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TameSurjectivity_RecUnram
import Theorems.Thm_PI_TameSurjW_liesOver_span_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PI PI.TameSurjW
namespace PI.TameSurjW
theorem _root_.solution {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : (Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ Formalism.BasicNotions.placesOver E p) :
    ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 := by
  set P0 : Ideal ℤ := Ideal.span {(p : ℤ)} with hP0def
  have : Fact p.Prime := ⟨hp⟩
  have hmax : P0.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P0 ≠ ⊥ := by
    simp [P0, hp.ne_zero]
  have himg : HeightOneSpectrum.asIdeal '' (Formalism.BasicNotions.placesOver E p) = P0.primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.isPrime, (liesOver_span_iff hp w.asIdeal).2 hw⟩
    · rintro ⟨hPp, hPl⟩
      have hPne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hP0 ⟨hPp, hPl⟩
      exact ⟨⟨P, hPp, hPne⟩, (liesOver_span_iff hp P).1 hPl, rfl⟩
  have hcard : Fintype.card (P0.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, ← himg,
      Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab), h]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P0 (𝓞 E)
  rw [RingOfIntegers.rank] at hsum
  intro hsq
  have hlo : v.asIdeal.LiesOver P0 := (liesOver_span_iff hp v.asIdeal).2 hv
  let q : P0.primesOver (𝓞 E) := ⟨v.asIdeal, v.isPrime, hlo⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) P0 ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
  have hdvd : v.asIdeal ^ 2 ∣ Ideal.map (algebraMap ℤ (𝓞 E)) P0 := by
    rw [Ideal.dvd_iff_le, hP0def, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe]
    simpa using hsq
  have hfin : FiniteMultiplicity v.asIdeal (Ideal.map (algebraMap ℤ (𝓞 E)) P0) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime v.ne_bot v.isPrime) hmap
  have he : 2 ≤ v.asIdeal.ramificationIdx ℤ := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P0 v.asIdeal hmap]
    exact hfin.le_multiplicity_of_pow_dvd hdvd
  have hlt : Fintype.card (P0.primesOver (𝓞 E)) <
      ∑ r : P0.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
    rw [Fintype.card_eq_sum_ones]
    apply Finset.sum_lt_sum
    · intro r _
      exact Nat.mul_pos (Ideal.ramificationIdx_pos r.1 ℤ) (Ideal.inertiaDeg_pos r.1 ℤ)
    · refine ⟨q, Finset.mem_univ _, ?_⟩
      have hf : 0 < v.asIdeal.inertiaDeg ℤ := Ideal.inertiaDeg_pos v.asIdeal ℤ
      show 1 < v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ
      nlinarith
  omega
end PI.TameSurjW
