-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.tower_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:00:00.342749+00:00
-- url     : https://prove2.me/submissions/d03957ae-4825-415c-a554-3ce650459c16

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_range_resGK
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') :
    Bijective (fun x : (GK p K ⧸ subG p K L) × (GK p L ⧸ subG p L L') =>
      (QuotientGroup.mk (x.1.out * resGK h x.2.out) : GK p K ⧸ subG p K L')) := by
  have hres : ∀ τ : GK p L, resGK h τ ∈ subG p K L := fun τ => by
    rw [← range_resGK h]; exact ⟨τ, rfl⟩
  constructor
  · rintro ⟨c, d⟩ ⟨c', d'⟩ hcd
    have h1 : (c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out) ∈ subG p K L' :=
      QuotientGroup.eq.1 hcd
    have h2 : c.out⁻¹ * c'.out ∈ subG p K L := by
      have h3 := (subG p K L).mul_mem ((subG p K L).mul_mem (hres d.out) (subG_anti h' h1))
        ((subG p K L).inv_mem (hres d'.out))
      have h4 : resGK h d.out * ((c.out * resGK h d.out)⁻¹ * (c'.out * resGK h d'.out)) *
          (resGK h d'.out)⁻¹ = c.out⁻¹ * c'.out := by group
      rwa [h4] at h3
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      exact QuotientGroup.eq.2 h2
    subst hc
    have h5 : resGK h (d.out⁻¹ * d'.out) ∈ subG p K L' := by
      have h6 : (c.out * resGK h d.out)⁻¹ * (c.out * resGK h d'.out) = resGK h (d.out⁻¹ * d'.out) := by
        rw [map_mul, map_inv]; group
      rwa [h6] at h1
    have hd : d = d' := by
      rw [← QuotientGroup.out_eq' d, ← QuotientGroup.out_eq' d']
      exact QuotientGroup.eq.2 h5
    rw [hd]
  · intro e
    induction e using QuotientGroup.induction_on with
    | H σ =>
      have h1 : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ subG p K L :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      have h1' : (QuotientGroup.mk σ : GK p K ⧸ subG p K L).out⁻¹ * σ ∈ (resGK h).range := by
        rw [range_resGK h]; exact h1
      obtain ⟨τ, hτ⟩ := h1'
      refine ⟨(QuotientGroup.mk σ, QuotientGroup.mk τ), ?_⟩
      have h2 : (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ ∈ subG p L L' :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
      apply QuotientGroup.eq.2
      have h3 : ((QuotientGroup.mk σ : GK p K ⧸ subG p K L).out *
          resGK h (QuotientGroup.mk τ : GK p L ⧸ subG p L L').out)⁻¹ * σ =
          resGK h ((QuotientGroup.mk τ : GK p L ⧸ subG p L L').out⁻¹ * τ) := by
        rw [map_mul, map_inv, hτ, mul_inv_rev, mul_assoc]
      rw [h3]
      exact h2
end ReciprocityTheory.DiscreteGroups.LocalClassField
