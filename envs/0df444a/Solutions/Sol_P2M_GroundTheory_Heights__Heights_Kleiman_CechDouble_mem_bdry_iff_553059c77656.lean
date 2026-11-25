-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_CechDouble_mem_bdry_iff_553059c77656
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:10:25.845554+00:00
-- url     : https://prove2.me/submissions/dfaf8c38-e81e-4da2-a957-90e41c512f7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDoubleSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDoubleStair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDouble

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
theorem _root_.solution (G : Cell U → Submodule S E) (hG : ∀ I J : Cell U, I.1 ⊆ J.1 → G I ≤ G J) :
    ∀ (n : ℕ) (z : Cdeg (fun _ : Cell U => E) G n),
      z ∈ Stair.bdry (dRes G hG) n ↔ (z : Cochain (fun _ : Cell U => E) n) ∈
        Cech.bdryDeg (fun _ : Cell U => E) G (Cech.idRes S E U) n
  | 0, z => by
      change z ∈ (⊥ : Submodule S _) ↔ (z : Cochain (fun _ : Cell U => E) 0) ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot, Submodule.mem_bot]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  | n + 1, z => by
      change z ∈ LinearMap.range (dRes G hG n) ↔
        (z : Cochain (fun _ : Cell U => E) (n + 1)) ∈ (Cdeg (fun _ : Cell U => E) G n).map (dE S E U n)
      rw [LinearMap.mem_range, Submodule.mem_map]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.2, rfl⟩
      · rintro ⟨t, ht, hty⟩
        exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
end GroundTheory.Heights₂.Heights.Kleiman.CechDouble
