-- Prove2me | solution 1 for PI.FT.stepHomeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:33.246658+00:00
-- url     : https://prove2.me/submissions/e17a30c0-7704-422d-a711-8edb6b70a5e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
import Theorems.Thm_PI_FT_cont_sandwich
import Theorems.Thm_PI_FT_cont_HA_iff
import Theorems.Thm_PI_FT_frame_formulas
import Theorems.Thm_PI_FT_mtI_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}
local notation "ι" => inclR (F := F) (E := E) (AF F)
namespace PI.FT
theorem _root_.solution : StepHomeo F E σ := by
  intro M J J' x β B hH e he
  obtain ⟨fA, fB⟩ := frame_formulas hH e he
  have hid := (cont_HA_iff (AF F) (fun g : HA (AF F) σ J => g)).1 continuous_id
  have hid' := (cont_HA_iff (AF F) (fun g : HA (AF F) σ J' => g)).1 continuous_id
  have hs1 : Continuous (fun g : Hstab (AF F) σ J x => mt (g : HA (AF F) σ J)) :=
    hid.1.comp continuous_subtype_val
  have hs2 : Continuous (fun g : Hstab (AF F) σ J x => mtI (g : HA (AF F) σ J)) :=
    hid.2.comp continuous_subtype_val
  constructor
  · refine (cont_HA_iff (AF F) e).2 ⟨?_, ?_⟩
    · exact (cont_sandwich (AF F) ((Lm σ J J' B).map ι) (B.map ι) hs1).congr fun g => (fA g).symm
    · refine (cont_sandwich (AF F) ((Lm σ J J' B).map ι) (B.map ι) hs2).congr fun g => ?_
      rw [mtI_eq e g, fA g⁻¹]
      rfl
  · have hc : Continuous (fun g' : HA (AF F) σ J' => (e.symm g' : HA (AF F) σ J)) := by
      refine (cont_HA_iff (AF F) _).2 ⟨?_, ?_⟩
      · refine (Continuous.add (continuous_const : Continuous fun _ : HA (AF F) σ J' =>
          (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι)
          (cont_sandwich (AF F) (B.map ι) ((Rm σ J J' B x (algebraMap F E β)).map ι) hid'.1)).congr
          fun g' => ?_
        rw [fB (e.symm g'), MulEquiv.apply_symm_apply]
        rfl
      · refine (Continuous.add (continuous_const : Continuous fun _ : HA (AF F) σ J' =>
          (Xc x).map ι * (qm σ J x (algebraMap F E β)).map ι)
          (cont_sandwich (AF F) (B.map ι) ((Rm σ J J' B x (algebraMap F E β)).map ι) hid'.2)).congr
          fun g' => ?_
        show _ = mt (((e.symm g')⁻¹ : Hstab (AF F) σ J x) : HA (AF F) σ J)
        rw [fB ((e.symm g')⁻¹), map_inv, MulEquiv.apply_symm_apply]
        rfl
    exact hc.subtype_mk (fun g' => (e.symm g').2)
end PI.FT
