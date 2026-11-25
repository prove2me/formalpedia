-- Prove2me | solution 1 for PI.FoldDCUnfold.W.double_coset_translation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:47:00.998894+00:00
-- url     : https://prove2.me/submissions/630380a2-351a-4d48-89ba-2221f9b5b921

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_TransExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FoldingUnfolding_DoubleCosetTranslation
import Theorems.Thm_PI_FoldDCUnfold_W_dc_core

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
open PI PI.FoldDCUnfold PI.FoldDCUnfold.W
universe u
namespace PI.FoldDCUnfold.W
theorem _root_.solution : DCTrans.{u} := by
  intro G _ Γ S S' hS hS' R hR E hE
  have hEsub : ∀ r ∈ R, E r ⊆ (S : Set G) := fun r hr => (hE r hr).1
  refine ⟨fun p q hpq => ?_, ?_, fun γ hγ => ?_⟩
  · refine (dc_core Γ S S' hS hS' R hR E hE p q 1 1 S'.one_mem S'.one_mem ?_).1
    rw [one_mul, one_mul]
    exact hpq
  · rintro _ ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩
    exact Γ.mul_mem (Γ.inv_mem (hR.1 hr)) (hS (hEsub r hr he))
  · obtain ⟨⟨r, hr⟩, ⟨s, hs, s', hs', hrep⟩, -⟩ := hR.2 γ⁻¹ (Γ.inv_mem hγ)
    change s * r * s' = γ⁻¹ at hrep
    obtain ⟨⟨⟨t, ht⟩, ⟨e, he⟩⟩, hte, -⟩ := (hE r hr).2 s⁻¹ (S.inv_mem hs)
    change t * e = s⁻¹ at hte
    have ht' : r⁻¹ * t * r ∈ S' := by
      have h2 := (Subgroup.mem_inf.mp ht).2
      rw [Subgroup.mem_comap] at h2
      change r⁻¹ * t * r⁻¹⁻¹ ∈ S' at h2
      rwa [inv_inv] at h2
    have hmem : s'⁻¹ * (r⁻¹ * t * r) ∈ S' := S'.mul_mem (S'.inv_mem hs') ht'
    have hγeq : s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = γ := by
      calc s'⁻¹ * (r⁻¹ * t * r) * (r⁻¹ * e) = s'⁻¹ * r⁻¹ * (t * e) := by group
        _ = s'⁻¹ * r⁻¹ * s⁻¹ := by rw [hte]
        _ = (s * r * s')⁻¹ := by group
        _ = γ := by rw [hrep, inv_inv]
    refine ⟨(⟨s'⁻¹ * (r⁻¹ * t * r), hmem⟩,
      ⟨r⁻¹ * e, ⟨⟨⟨r, hr⟩, ⟨e, he⟩⟩, rfl⟩⟩), hγeq, ?_⟩
    rintro ⟨⟨a, ha⟩, ⟨d, ⟨p, rfl⟩⟩⟩ hy
    obtain ⟨hp, ha'⟩ := dc_core Γ S S' hS hS' R hR E hE p ⟨⟨r, hr⟩, ⟨e, he⟩⟩ a
      (s'⁻¹ * (r⁻¹ * t * r)) ha hmem (hy.trans hγeq.symm)
    subst hp
    exact Prod.ext (Subtype.ext ha') (Subtype.ext rfl)
end PI.FoldDCUnfold.W
