-- Prove2me | solution 1 for PI.LocGlobInclWork.mem_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:00:09.449128+00:00
-- url     : https://prove2.me/submissions/5edc15bf-cea9-4a32-8189-eaf0f170fee5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocGlobIncl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalInclusion_SmulMemIdealSmul
import Theorems.Thm_PI_LocGlobInclWork_maximal_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.LocGlobInclWork
variable {K : Type} [Field K] [NumberField K]
namespace PI.LocGlobInclWork
theorem _root_.solution {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (N : Submodule (𝓞 K) W) (x : W)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 K) W x) ≠ ⊤ := by
    intro htop
    apply hx
    have h1 : (1 : 𝓞 K) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 K) W x) := by
      rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, maximal_ne_bot m hm⟩
  apply hs
  apply hle
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  exact hsx
end PI.LocGlobInclWork
