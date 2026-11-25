-- Prove2me | solution 1 for PI.KerDetFinW.det_valuation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:00:57.863511+00:00
-- url     : https://prove2.me/submissions/4ce1d2e0-93aa-473f-bfa7-95c520e54889

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ValuationLeOneOfDenom
import Theorems.Thm_PI_KerDetFinW_det_denom
import Theorems.Thm_PI_KerDetFinW_valuation_le_one_of_denom
import Theorems.Thm_PI_KerDetFinW_comp_denom

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
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type}
    [Fintype n] {M : Set E} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)} {p : ℕ}
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp𝔭 : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal)
    (hg : AtP M g p) (hg' : AtP M g' p) :
    𝔭.valuation K (LinearMap.det ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
      (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))) ≤ 1 := by
  classical
  set f := ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] _) :
    (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K)) with hf
  have hcol : ∀ j : Fin 4 × n, ∃ u : ℕ, Nat.Coprime u p ∧
      ∀ i, (u : K) * LinearMap.toMatrix' f i j ∈ (algebraMap (𝓞 K) K).range := by
    intro j
    have hv : ∀ w, (Pi.single j (1 : K) : Fin 4 × n → K) w ∈ (algebraMap (𝓞 K) K).range := by
      intro w
      by_cases hw : w = j
      · subst hw
        rw [Pi.single_eq_same]
        exact one_mem _
      · rw [Pi.single_eq_of_ne hw]
        exact zero_mem _
    obtain ⟨u, hu, hu'⟩ := comp_denom hg hg' (Pi.single j (1 : K)) hv
    exact ⟨u, hu, fun i => by rw [LinearMap.toMatrix'_apply]; exact hu' i⟩
  choose u hu hu' using hcol
  obtain ⟨U, hU, hUd⟩ := det_denom p (LinearMap.toMatrix' f) u hu (fun i j => hu' j i)
  rw [LinearMap.det_toMatrix'] at hUd
  exact valuation_le_one_of_denom 𝔭 hp𝔭 hU hUd
end PI.KerDetFinW
