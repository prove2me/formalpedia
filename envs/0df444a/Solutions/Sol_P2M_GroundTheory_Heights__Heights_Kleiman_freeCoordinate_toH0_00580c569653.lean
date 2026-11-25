-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_freeCoordinate_toH0_00580c569653
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:50.518395+00:00
-- url     : https://prove2.me/submissions/3ccf25a2-08a8-4971-a769-6bb2b436041f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca

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
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (c : ℤ) (j : Fin r) (m : 𝓜.piece c) :
    freeCoord 𝓜 b d hb 0 c j (toH0 𝓜 c m) =
      toH0 (polyGraded S N) (c - d j) ⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ := by
  obtain ⟨w, hw, hw'⟩ := cohomMapShift_mk (𝓜 := 𝓜) (𝓜' := polyGraded S N) (b.coord j) (-d j)
    (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) 0
    (show c - d j = c + -d j by ring) ⟨constCochain (m : M), constCochain_mem _ _ _ m.2⟩
  refine hw.trans ?_
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun I => (hw' I).trans (locMap_mk _ _ _ _)))
end GroundTheory.Heights₂.Heights.Kleiman
