-- Prove2me | solution 1 for PI.DvRows.den_of_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:04.150912+00:00
-- url     : https://prove2.me/submissions/4b2040d5-1ce2-40d6-8ac7-287ea01244cb

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
import Theorems.Thm_P2M_PI_DvRows_mem_locP__7b0c6c9a7105


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {X Y : Submodule (𝓞 K) V} (hY : Y.FG) (hYX : Y ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal X) :
    ∃ T : 𝓞 K, T ∉ w.asIdeal ∧ ∀ y ∈ Y, T • y ∈ X := by
  classical
  obtain ⟨S, rfl⟩ := hY
  have hs : ∀ g : S, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • (g : V) ∈ X := fun g => by
    obtain ⟨s, hs, hx⟩ := (mem_locP' w.asIdeal).1 (hYX (Submodule.subset_span g.2))
    exact ⟨s, hs, hx⟩
  choose s hsw hsX using hs
  have hT : (∏ g, s g) ∈ w.asIdeal.primeCompl := Submonoid.prod_mem _ fun g _ => hsw g
  refine ⟨∏ g, s g, hT, ?_⟩
  have key : Submodule.span (𝓞 K) (S : Set V) ≤
      X.comap ((∏ g, s g) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    have hx' : x ∈ S := Finset.mem_coe.1 hx
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨x, hx'⟩ : S)), mul_smul]
    exact X.smul_mem _ (hsX ⟨x, hx'⟩)
  intro y hy
  exact key hy
end PI.DvRows
