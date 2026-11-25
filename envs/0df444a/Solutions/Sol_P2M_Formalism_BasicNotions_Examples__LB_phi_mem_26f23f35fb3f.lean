-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_phi_mem_26f23f35fb3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:50:27.355709+00:00
-- url     : https://prove2.me/submissions/ff568ea8-02d5-4e07-8853-5aa414fc66d1

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ Kphi φ := by
  have hx := (Module.finBasis ℚ F).sum_repr x
  rw [← hx, map_sum]
  refine sum_mem (fun i _ => ?_)
  rw [map_rat_smul, Rat.smul_def]
  refine mul_mem ?_ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  first
  | exact SubfieldClass.ratCast_mem _ _
  | exact ratCast_mem _ _
  | exact (Kphi φ).toSubfield.ratCast_mem _
  | simp
end Formalism.BasicNotions.Examples₂.LB
