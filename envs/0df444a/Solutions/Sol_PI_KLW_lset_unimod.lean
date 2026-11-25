-- Prove2me | solution 1 for PI.KLW.lset_unimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:59.314798+00:00
-- url     : https://prove2.me/submissions/c17e523a-dc2d-4bbd-9370-36062dcd15ba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
import Theorems.Thm_PI_KLW_trace_mul_natCast
import Theorems.Thm_PI_KLW_Rp_finset
import Theorems.Thm_PI_KLW_Rp_map
import Theorems.Thm_PI_KLW_Unimod_add_mem
import Theorems.Thm_PI_KLW_Unimod_zero_mem
import Theorems.Thm_PI_KLW_conjK_invol
import Theorems.Thm_PI_KLW_hf_isom
import Theorems.Thm_PI_KLW_hf_symm
import Theorems.Thm_PI_KLW_trace_natCast_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
variable (cj : E ≃ₐ[ℚ] E) (hc : PI.KerIso.IsConj K cj) {n : Type} [Fintype n]
  (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
  (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))
include hc
namespace PI.KLW
theorem _root_.solution (hI : PI.KerIso.SelfDualI K cj I) (hg : PI.KerIso.IsIsom cj g₀) :
    Unimod K (conjK cj hc.2.1) p (Lset I p g₀) := by
  intro v
  constructor
  · rintro ⟨s, hs, hsv⟩ w ⟨t, ht, htw⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e1 : hf (conjK cj hc.2.1) v w =
        ∑ a, Algebra.trace K E (g₀.symm v a * cj (g₀.symm w a)) := by
      rw [← hf_isom cj hc.2.1 g₀ hg]; simp
    rw [e1, Finset.mul_sum]
    refine Subring.sum_mem _ fun a _ => ?_
    rw [← trace_natCast_mul]
    exact (hI _).1 (htw a) _ (hsv a)
  · intro hv
    set x := g₀.symm v with hx

    have claim1 : ∀ a, ∀ z ∈ I, Rp K p (Algebra.trace K E (z * cj (x a))) := by
      intro a z hz
      classical
      have hw : g₀ (Pi.single a z) ∈ Lset I p g₀ := ⟨1, Nat.coprime_one_left p, fun b => by
        rw [Nat.cast_one, one_mul, LinearEquiv.symm_apply_apply]
        by_cases hb : b = a
        · subst hb; simpa using hz
        · rw [Pi.single_eq_of_ne hb]; exact FractionalIdeal.mem_coe.mp (I : Submodule (𝓞 E) E).zero_mem⟩
      have h2 := Rp_map (conjK cj hc.2.1) (hv _ hw)
      rw [← hf_symm _ (conjK_invol cj hc)] at h2
      have e2 : hf (conjK cj hc.2.1) (g₀ (Pi.single a z)) v =
          Algebra.trace K E (z * cj (x a)) := by
        have : v = g₀ x := by simp [hx]
        rw [this, hf_isom cj hc.2.1 g₀ hg, Finset.sum_eq_single a]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ a) h
      rwa [e2] at h2

    obtain ⟨T, hT⟩ := (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).restrictScalars (R := ℤ)
    have hTI : ∀ z ∈ T, z ∈ I := fun z hz => by
      have : z ∈ ((I : Submodule (𝓞 E) E).restrictScalars ℤ) := hT ▸ Submodule.subset_span hz
      exact this
    have claim2 : ∀ a, ∃ s : ℕ, Nat.Coprime s p ∧
        ∀ z ∈ I, (s : K) * Algebra.trace K E (z * cj (x a)) ∈ (algebraMap (𝓞 K) K).range := by
      intro a
      obtain ⟨s, hs, hsT⟩ := Rp_finset (p := p) T (fun z => Algebra.trace K E (z * cj (x a)))
        fun z hz => claim1 a z (hTI z hz)
      refine ⟨s, hs, fun z hz => ?_⟩
      have hz' : z ∈ Submodule.span ℤ (T : Set E) := by
        rw [hT]; exact hz
      clear hz
      induction hz' using Submodule.span_induction with
      | mem z hz => exact hsT z hz
      | zero => simp
      | add z z' _ _ h h' =>
        rw [add_mul, map_add, mul_add]; exact Subring.add_mem _ h h'
      | smul k z _ h =>
        have e : (s : K) * Algebra.trace K E ((k • z) * cj (x a)) =
            k • ((s : K) * Algebra.trace K E (z * cj (x a))) := by
          rw [smul_mul_assoc, map_zsmul, mul_smul_comm]
        rw [e]; exact Subring.zsmul_mem _ h k
    choose s hs hsI using claim2
    refine ⟨∏ a, s a, Nat.Coprime.prod_left fun a _ => hs a, fun a => (hI _).2 fun z hz => ?_⟩
    rw [trace_mul_natCast]
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ a)
    rw [hq, Nat.cast_mul, mul_comm (s a : K), mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ q) (hsI a z hz)
end PI.KLW
