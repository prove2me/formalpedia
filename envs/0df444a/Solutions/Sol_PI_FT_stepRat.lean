-- Prove2me | solution 1 for PI.FT.stepRat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:18.871037+00:00
-- url     : https://prove2.me/submissions/c394fe00-d79e-4c95-a535-7305c6c768b1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_InstIsModTopTens
import Theorems.Thm_PI_FT_frame_formulas
import Theorems.Thm_PI_FT_mtI_eq
import Theorems.Thm_PI_FT_inclR_injective
import Theorems.Thm_PI_FT_mem_HFinIn_iff


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
theorem _root_.solution : StepRat F E σ := by
  intro M J J' x β B hH e he g
  obtain ⟨fA, fB⟩ := frame_formulas hH e he
  constructor
  · intro hg
    have h1 : toHR (g : HA (AF F) σ J) ∈ HFinIn (AF F) σ J :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hg)).1
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := (mem_HFinIn_iff σ (AF F) inclR_injective _).1 h1
    refine (mem_HFinIn_iff σ (AF F) inclR_injective _).2
      ⟨⟨Lm σ J J' B * a * B, ?_⟩, ⟨Lm σ J J' B * c * B, ?_⟩⟩
    · show mt (e g) = _
      rw [fA g, show mt (g : HA (AF F) σ J) = a.map ι from ha, Matrix.map_mul, Matrix.map_mul]
    · show mtI (e g) = _
      rw [mtI_eq e g, fA g⁻¹]
      show (Lm σ J J' B).map ι * mtI (g : HA (AF F) σ J) * B.map ι = _
      rw [show mtI (g : HA (AF F) σ J) = c.map ι from hc, Matrix.map_mul, Matrix.map_mul]
  · intro hg
    obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := (mem_HFinIn_iff σ (AF F) inclR_injective _).1 hg
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, g.2⟩)
    refine (mem_HFinIn_iff σ (AF F) inclR_injective _).2
      ⟨⟨Xc x * qm σ J x (algebraMap F E β) + B * a * Rm σ J J' B x (algebraMap F E β), ?_⟩,
        ⟨Xc x * qm σ J x (algebraMap F E β) + B * c * Rm σ J J' B x (algebraMap F E β), ?_⟩⟩
    · show mt (g : HA (AF F) σ J) = _
      rw [fB g, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      rw [show mt (e g) = a.map ι from ha]
    · show mt ((g⁻¹ : Hstab (AF F) σ J x) : HA (AF F) σ J) = _
      rw [fB g⁻¹, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
        ← mtI_eq e g]
      rw [show mtI (e g) = c.map ι from hc]
end PI.FT
