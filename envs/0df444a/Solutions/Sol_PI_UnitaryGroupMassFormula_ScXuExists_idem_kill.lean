-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.idem_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:00.085789+00:00
-- url     : https://prove2.me/submissions/4f9e28c9-f8ab-48e8-8aa4-04acf8310ad1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_NatCastTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalIdempotentExistence
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_latLoc_fg
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_natCast_mem_max


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (g : ℕ) (hg : (g : 𝓞 I.F) ∈ v.asIdeal)
    (c : RV I v) (hcc : c * c = c)
    (hc : ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = (g : RV I v) • w) :
    ∀ x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)), c • x = 0 := by
  have hfg : ((Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c)).FG :=
    (latLoc_fg I v).map _
  have hle : (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) ≤
      Ideal.span {(g : OV I v)} • (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, hcw⟩ := hc x hx
    have e : (smulLin I v c) x = (g : OV I v) • (smulLin I v c w) := by
      show c • x = (g : OV I v) • (c • w)
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (RV I v), smul_comm, ← hcw, smul_smul, hcc]
    rw [e]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (Submodule.mem_map_of_mem hw)
  have hjac : Ideal.span {(g : OV I v)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact natCast_mem_max I.F v g hg
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hle hjac
  intro x hx
  have hm : (smulLin I v c) x ∈ (Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))).map (smulLin I v c) :=
    Submodule.mem_map_of_mem hx
  rw [hbot, Submodule.mem_bot] at hm
  exact hm
end PI.UnitaryGroupMassFormula.ScXuExists
