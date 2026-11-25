-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.piQdet_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:55.724384+00:00
-- url     : https://prove2.me/submissions/e22f9f8c-21dd-47ef-8659-c0cc4b613d18

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_ext
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_alt_anti
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_step1
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_evA
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_evQ
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open QuantumDeterminantProducts
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → JMComm → PiQdet := by
  intro hT hJ n M _ _ E hE u
  apply LinearMap.ext
  intro f
  set g := alt Finset.univ f with hgdef
  have hg : IsAnti g := alt_anti f
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hPX : PiJ n E u = ((List.finRange n).map (X E u)).prod := by
    unfold PiJ
    rw [List.ofFn_eq_map]
    rfl
  have hA : IsAnti (PiJ n E u g) := by
    intro σ
    have hc := ((hJ n M E hE n).2.2 u σ).eq
    calc pm σ (PiJ n E u g) = ((pm σ * PiJ n E u : Module.End ℂ (TV n M (Fin n))) g) := rfl
      _ = ((PiJ n E u * pm σ : Module.End ℂ (TV n M (Fin n))) g) := by rw [hc]
      _ = PiJ n E u (pm σ g) := rfl
      _ = sg σ • PiJ n E u g := by rw [hg σ, map_smul]
  have hB : IsAnti (lift (qdet E u) g) := by
    intro σ
    have hl : pm σ (lift (qdet E u) g) = lift (qdet E u) (pm σ g) := by
      funext I
      simp [pm, lift]
    rw [hl, hg σ, map_smul]
  have hD : IsAnti (PiJ n E u g - lift (qdet E u) g) := by
    intro σ
    rw [map_sub, hA σ, hB σ, smul_sub]
  have h0 : (PiJ n E u g - lift (qdet E u) g) id = 0 := by
    rw [Pi.sub_apply, hPX, step1 hT E hE u g hg _ (List.pairwise_lt_finRange n), evA, evQ E u g hg]
    simp [lift]
  exact sub_eq_zero.mp (anti_ext hD h0)
end PositivityTheory.Rg.Cz
