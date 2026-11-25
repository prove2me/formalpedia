-- Prove2me | solution 1 for PI.SRW.retraction_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:43:49.01915+00:00
-- url     : https://prove2.me/submissions/1db7b9bc-0d41-4af2-ad25-973a1ab9ad6c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_CoordStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorsionFreeGenerators_ProjectiveReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SesquilinearRowSplitting_RetractionReduction
import Theorems.Thm_PI_FGTFG_projective_reduction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.SRW
namespace PI.SRW
theorem _root_.solution : RetrStep := by
  intro E V _ _ _ _ _ _ Λ N hNΛ hfg hsat
  let N' : Submodule (𝓞 E) Λ := N.comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite (𝓞 E) (Λ ⧸ N') := inferInstance
  haveI : NoZeroSMulDivisors (𝓞 E) (Λ ⧸ N') := by
    refine ⟨fun {o q} hq => ?_⟩
    by_cases ho : o = 0
    · exact Or.inl ho
    right
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N' q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hsat o x ho x.2 hq
  haveI : Module.Projective (𝓞 E) (Λ ⧸ N') := PI.FGTFG.projective_reduction (𝓞 E) (Λ ⧸ N')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id (Submodule.mkQ_surjective N')
  let ρ' : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s.comp N'.mkQ
  have hρ' : ∀ x : Λ, ρ' x ∈ N' := by
    intro x
    have h1 : N'.mkQ (ρ' x) = 0 := by
      have h2 := LinearMap.congr_fun hs (N'.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
      show N'.mkQ (x - s (N'.mkQ x)) = 0
      rw [map_sub, h2, sub_self]
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  refine ⟨Λ.subtype.comp ρ', fun x => hρ' x, fun x hx => ?_⟩
  have hx' : x ∈ N' := hx
  have h0 : N'.mkQ x = 0 := by simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx'
  simp [ρ', h0]
end PI.SRW
