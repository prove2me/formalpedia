-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_selfDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:40.692029+00:00
-- url     : https://prove2.me/submissions/459a8802-98df-49d3-836e-4500765fa979

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomSelfDual
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_linIndep_orth
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_orth_sub_proj
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_ortho_unit
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_isom_frameU
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_UpperTheory_Reformulated_B_ExistsOrthogonalBasisWithUnitNorms_exists_ortho_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution [FiniteDimensional K V] (hS : IsHermSemilocal S) (hs : h.IsSymm)
    (hnd : h.Nondegenerate) (hPU : PairUnit S h) {L M : AddSubgroup V} (hL : IsSelfDualMod S h L)
    (hM : IsSelfDualMod S h M) : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ v, v ∈ L ↔ g v ∈ M := by
  classical
  obtain ⟨x, hxL, hxo, hxu⟩ := exists_ortho_unit hS hs hnd hPU hL
  obtain ⟨g, hg, hgM⟩ := exists_isom_frameU hS hs hM x hxo hxu
  have hg' : ∀ a b, h (g a) (g b) = h a b := hg
  have hli := linIndep_orth x hxo (fun i => (hxu i).1)
  have hspan : Submodule.span K (Set.range x) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hexp : ∀ v, v = ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i := by
    intro v
    have hxv' := orth_sub_proj x hxo (fun i => (hxu i).1) v
    have hall : ∀ y, h y (v - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) v) • x i) = 0 := by
      intro y
      have hy : y ∈ Submodule.span K (Set.range x) := by rw [hspan]; trivial
      induction hy using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨j, rfl⟩ := ha
        exact hxv' j
      | zero => simp
      | add a b _ _ ha hb => simp [ha, hb]
      | smul c a _ ha => simp [ha]
    exact sub_eq_zero.1 (hnd.2 _ hall)
  have hfwd : ∀ v, v ∈ L → g v ∈ M := by
    intro v hv
    rw [hexp v, map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul]
    exact hM.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hv)) _ (hgM i)
  refine ⟨g, hg, fun v => ⟨hfwd v, fun hv => hL.dual v fun m hm => ?_⟩⟩
  rw [← hg']
  exact hM.int _ (hfwd m hm) _ hv
end PI.UnitaryGroupMassFormula.CntFormula.UG
