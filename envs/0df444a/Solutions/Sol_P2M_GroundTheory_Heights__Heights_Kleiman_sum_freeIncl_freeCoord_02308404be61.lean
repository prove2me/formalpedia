-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sum_freeIncl_freeCoord_02308404be61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:30.689835+00:00
-- url     : https://prove2.me/submissions/809103e4-6631-4764-b820-75a6d62d0a5a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cohomMapShift_mk_088a57e319ca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_sum_locMap_basis_bd6d991ae90c

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
theorem _root_.solution (i : ℕ) (c : ℤ) (x : cohom 𝓜 i c) :
    ∑ j, freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have e : ∀ j, ∃ w : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i,
        freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j (Submodule.Quotient.mk z)) =
          (Submodule.Quotient.mk w : cohom 𝓜 i c) ∧
        ∀ I, w.1 I = locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I.1.1
          (locMap (b.coord j) I.1.1 (z.1 I)) := by
      intro j
      obtain ⟨z1, h1, h1'⟩ := cohomMapShift_mk (𝓜 := 𝓜) (𝓜' := polyGraded S N) (b.coord j) (-d j)
        (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) i
        (show c - d j = c + -d j by ring) z
      obtain ⟨z2, h2, h2'⟩ := cohomMapShift_mk (𝓜 := polyGraded S N) (𝓜' := 𝓜)
        (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
        (fun _ _ hp => by
          rw [LinearMap.toSpanSingleton_apply, add_comm]
          exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) i (show c = c - d j + d j by ring) z1
      refine ⟨z2, ?_, fun I => by rw [h2', h1']⟩
      change cohomMapShift _ _ _ i _ (cohomMapShift _ _ _ i _ _) = _
      rw [h1, h2]
    choose w hw hw' using e
    have hz : ∑ j, w j = z := by
      apply Subtype.ext
      funext I
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hw']
      exact sum_locMap_basis b I.1.1 (z.1 I)
    refine (Finset.sum_congr rfl fun j _ => hw j).trans ?_
    exact (map_sum (Submodule.mkQ _) w Finset.univ).symm.trans (congrArg _ hz)
end GroundTheory.Heights₂.Heights.Kleiman
