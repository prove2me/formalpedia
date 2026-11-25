-- Prove2me | solution 1 for PI.ScRefExists.TH.theta_series_existence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:08.328801+00:00
-- url     : https://prove2.me/submissions/73b9b984-b6f7-4f29-a12b-9ca07da3e828

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_ThetaSeriesExistence
import Theorems.Thm_PI_ScRefExists_TH_mem_primesG
import Theorems.Thm_PI_ScRefExists_TH_prod_le_radical
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_TH_cj_cj
import Theorems.Thm_PI_ScRefExists_TH_cj_ne
import Theorems.Thm_PI_ScRefExists_TH_mem_cj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
private lemma sk_GE_of_mem_span_natCast (g : ℕ) (z : 𝓞 I.E) (hz : z ∈ Ideal.span {(g : 𝓞 I.E)}) :
    PI.ScRefExists.Sk.GE I g (z : I.E) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨t, ?_⟩
  rw [← ht]
  first
    | (push_cast; ring)
    | simp [mul_comm]
end PI.ScRefExists.TH
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.TH
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.TH
theorem _root_.solution : PI.ScRefExists.Sk.ThetaEx := by
  intro I g hg hS
  classical
  letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := by
    first
      | exact linearOrderOfSTO WellOrderingRel
      | exact IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∏ P ∈ primesG I g hg, P.asIdeal) ^ N ≤ Ideal.span {(g : 𝓞 I.E)} := by
    first
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (prod_le_radical I g hg) (IsNoetherian.noetherian _)
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (IsNoetherian.noetherian _) (prod_le_radical I g hg)
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := primesG I g hg)
    (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal) (fun _ => N) (fun P _ => P.prime)
    (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
    (fun P => if (P : HeightOneSpectrum (𝓞 I.E)) < cj I P then (1 : 𝓞 I.E) else 0)
  have h1 : ∀ P ∈ primesG I g hg, P < cj I P → θ - 1 ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have h0 : ∀ P ∈ primesG I g hg, ¬ P < cj I P → θ ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have hcjS : ∀ P ∈ primesG I g hg, cj I P ∈ primesG I g hg := by
    intro P hP
    rw [mem_primesG] at hP ⊢
    rw [mem_cj, map_natCast]
    exact hP
  have hsg : ∀ (P : HeightOneSpectrum (𝓞 I.E)) (z : 𝓞 I.E), z ∈ (cj I P).asIdeal ^ N →
      sg I z ∈ P.asIdeal ^ N := by
    intro P z hz
    have h2 := Ideal.mem_map_of_mem (sg I) hz
    rwa [Ideal.map_pow, show (cj I P).asIdeal = P.asIdeal.comap (sg I) from rfl,
      Ideal.map_comap_of_surjective _ (fun y => ⟨sg I y, sg_sg I y⟩)] at h2
  have hloc : ∀ P ∈ primesG I g hg, θ * θ - θ ∈ P.asIdeal ^ N ∧ θ * sg I θ ∈ P.asIdeal ^ N ∧
      1 - θ - sg I θ ∈ P.asIdeal ^ N := by
    intro P hP
    have hne : cj I P ≠ P := cj_ne I g hg hS P ((mem_primesG I g hg P).mp hP)
    by_cases hlt : P < cj I P
    · have ha := h1 P hP hlt
      have hb : θ ∈ (cj I P).asIdeal ^ N :=
        h0 (cj I P) (hcjS P hP) (by rw [cj_cj]; exact lt_asymm hlt)
      have hb' := hsg P θ hb
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = (θ - 1) * θ := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_left _ _ hb'
      · have e : 1 - θ - sg I θ = -(θ - 1) - sg I θ := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
    · have ha := h0 P hP hlt
      have hlt' : cj I P < cj I (cj I P) := by
        rw [cj_cj]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have hb' := hsg P _ (h1 (cj I P) (hcjS P hP) hlt')
      rw [map_sub, map_one] at hb'
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = θ * (θ - 1) := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_right _ _ ha
      · have e : 1 - θ - sg I θ = -θ - (sg I θ - 1) := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
  have key : (primesG I g hg).inf (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal ^ N) =
      (∏ P ∈ primesG I g hg, P.asIdeal) ^ N := by
    rw [← Finset.prod_pow]
    exact IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun P _ => P.prime)
      (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
  have hmem : ∀ z : 𝓞 I.E, (∀ P ∈ primesG I g hg, z ∈ P.asIdeal ^ N) →
      z ∈ Ideal.span {(g : 𝓞 I.E)} := by
    intro z hz
    apply hN
    rw [← key]
    exact (Ideal.span_singleton_le_iff_mem _).mp
      (Finset.le_inf fun P hP => (Ideal.span_singleton_le_iff_mem _).mpr (hz P hP))
  refine ⟨θ, ?_, ?_, ?_⟩
  · have e : ((θ * θ - θ : 𝓞 I.E) : I.E) = (θ : I.E) * θ - θ := by push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).1)
  · have e : ((θ * sg I θ : 𝓞 I.E) : I.E) = (θ : I.E) * star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.1)
  · have e : ((1 - θ - sg I θ : 𝓞 I.E) : I.E) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.2)
end PI.ScRefExists.TH
