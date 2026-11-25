-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_hdeg_equiv_bba7c94c79f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:20:41.599478+00:00
-- url     : https://prove2.me/submissions/f9802a44-4f00-4b4d-9b29-d3ce463e2cfb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_mem_bdry_iff_553059c77656
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_Stair_DblData_equiv_a3e28b94663a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.CechDouble
open Cech
variable {S : Type u} [CommRing S] {E : Type v} [AddCommGroup E] [Module S E] {m : ℕ} {U : Finset (Fin m)}
namespace GroundTheory.Heights₂.Heights.Kleiman.CechDouble
theorem _root_.solution (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) (n : ℕ) :
    Nonempty (Cech.Hdeg (fun _ : Cell U => E) G (Cech.idRes S E U) n ≃ₗ[S] Stair.H (dRes G hG) n) := by
  let e : LinearMap.ker (dRes G hG n) ≃ₗ[S] Cech.cocyDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n :=
    { toFun := fun z => ⟨z.1.1, LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp z.2)), z.1.2⟩
      invFun := fun z => ⟨⟨z.1, z.2.2⟩, LinearMap.mem_ker.mpr (Subtype.ext (LinearMap.mem_ker.mp z.2.1))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨(Submodule.Quotient.equiv _ _ e ?_).symm⟩
  ext z
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  exact mem_bdry_iff G hG n _
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble
