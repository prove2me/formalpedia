-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_A_jet_mem__52c2ce6d0ed4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:09:28.762158+00:00
-- url     : https://prove2.me/submissions/527908a5-27dc-4161-aec8-77ae09131eac

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementM
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ChainRuleFormalGroupVar
import Theorems.Thm_Formalism_L2_Th1_A_jet_integral
import Theorems.Thm_Formalism_L2_Th1_A_More_fw_mem
import Theorems.Thm_Formalism_L2_Th1_A_More_D_mem
import Theorems.Thm_Formalism_L2_Th1_A_More_iterate_D_mem
import Theorems.Thm_Formalism_L2_Th1_A_composition_inverse_spec
import Theorems.Thm_Formalism_L2_Th1_A_expSpec_of
import Theorems.Thm_Formalism_L2_Th1_A_integration_spec
import Theorems.Thm_Formalism_L2_Th1_A_invariant_differential_units


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open More
namespace Formalism.L2.Th1.A
theorem _root_.solution : JetMem.{u} := by
  intro K _ _ W S h1 h2 h3 h4 h6
  have hw := fw_mem W S h1 h2 h3 h4 h6
  have hsec : ∀ f : K⟦X⟧, (∀ n, coeff n f ∈ S) → ∀ n : ℕ,
      (n.factorial : K) * coeff n (f.subst (expSer W)) ∈ S := by
    intro f hf n
    rw [jet_integral K W f n, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact iterate_D_mem W S hw n f hf 0
  refine ⟨fun f hf n => D_mem W S hw f hf n, hsec, fun n => ?_⟩
  have hE0 : constantCoeff (expSer W) = 0 := by
    first
    | exact (expSpec_of integration_spec composition_inverse_spec invariant_differential_units K W).1
    | exact (formal_exponential_spec K W).1
  have hs : HasSubst (expSer W) := by
    first
    | exact HasSubst.of_constantCoeff_zero' hE0
    | exact HasSubst.of_constantCoeff_zero hE0
  have hX : ∀ m, coeff m (X : K⟦X⟧) ∈ S := fun m => by
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact one_mem S
    · exact zero_mem S
  have h := hsec X hX n
  rwa [PowerSeries.subst_X hs] at h
end Formalism.L2.Th1.A
