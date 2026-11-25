-- Prove2me | solution 1 for PI.MSC.isCompl_map_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:01.453953+00:00
-- url     : https://prove2.me/submissions/535e198d-b03c-4dde-8375-a2b688bfb1b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
import Theorems.Thm_PI_MSC_exists_coeff_ne_zero_of_mem_span
import Theorems.Thm_PI_MSC_monomial_mem_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.MSC
open scoped MonomialOrder
variable {σ R : Type*} [CommRing R]
namespace PI.MSC
theorem _root_.solution (O : MonomialOrder σ) {τ : Type*} {φ : σ → τ}
    (hφ : Function.Injective φ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hinj : Function.Injective fun i => O.degree (c i)) (hlc : ∀ i, O.leadingCoeff (c i) = 1) :
    IsCompl (Submodule.map (rename φ).toLinearMap (Submodule.span R (Set.range c)))
      (restrictSupport R (Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i))ᶜ) := by
  classical
  have hmapinj : Function.Injective (Finsupp.mapDomain φ : (σ →₀ ℕ) → (τ →₀ ℕ)) :=
    Finsupp.mapDomain_injective hφ
  constructor
  · rw [Submodule.disjoint_def]
    intro g hg1 hg2
    obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.mp hg1
    by_contra hne
    have hh0 : h ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    obtain ⟨i, hi⟩ := exists_coeff_ne_zero_of_mem_span O c hinj hlc hh hh0
    have hsupp := (MvPolynomial.mem_restrictSupport_iff R).mp hg2
    have hmem : Finsupp.mapDomain φ (O.degree (c i)) ∈ ((rename φ).toLinearMap h).support := by
      rw [MvPolynomial.mem_support_iff]
      show MvPolynomial.coeff (Finsupp.mapDomain φ (O.degree (c i))) (rename φ h) ≠ 0
      rw [MvPolynomial.coeff_rename_mapDomain φ hφ]
      exact hi
    exact hsupp (Finset.mem_coe.mpr hmem) ⟨O.degree (c i), ⟨i, rfl⟩, rfl⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro g _
    rw [MvPolynomial.as_sum g]
    refine Submodule.sum_mem _ fun d _ => ?_
    by_cases hd : d ∈ Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i)
    · obtain ⟨e, _, rfl⟩ := hd
      have h1 := monomial_mem_sup O c hlc e (g.coeff (Finsupp.mapDomain φ e))
      rw [← MvPolynomial.rename_monomial]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
      rw [← hyz, map_add]
      refine Submodule.add_mem_sup (Submodule.mem_map_of_mem hy) ?_
      rw [MvPolynomial.mem_restrictSupport_iff] at hz ⊢
      intro d' hd'
      have hd2 : d' ∈ (rename φ z).support := hd'
      rw [MvPolynomial.support_rename_of_injective hφ] at hd2
      obtain ⟨d'', hd'', rfl⟩ := Finset.mem_image.mp hd2
      rintro ⟨e', he', heq⟩
      exact hz (Finset.mem_coe.mpr hd'') (hmapinj heq ▸ he')
    · exact Submodule.mem_sup_right ((MvPolynomial.monomial_mem_restrictSupport R).mpr (Or.inl hd))
end PI.MSC
