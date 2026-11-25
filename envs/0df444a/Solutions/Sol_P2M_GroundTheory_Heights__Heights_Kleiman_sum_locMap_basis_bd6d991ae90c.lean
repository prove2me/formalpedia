-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_sum_locMap_basis_bd6d991ae90c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:27.649986+00:00
-- url     : https://prove2.me/submissions/9cddfb44-7f67-4c90-bcae-830b1581299d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree

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
omit [Module S M] [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (I : Finset (Fin (N + 1))) (y : LocMod S N M I) :
    ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) = y := by
  have h1 : ∀ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) =
      locMap ((LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y := fun j => by
    simp only [locMap]
    rw [IsLocalizedModule.map_comp' (monos (S := S) I) (LocalizedModule.mkLinearMap (monos (S := S) I) M)
      (LocalizedModule.mkLinearMap (monos (S := S) I) (Poly S N))
      (LocalizedModule.mkLinearMap (monos (S := S) I) M)]
    rfl
  have h2 : ∑ j, (LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j) = LinearMap.id := by
    ext m
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply, LinearMap.id_apply]
    exact b.sum_repr m
  calc ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y)
      = ∑ j, locMap ((LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y :=
        Finset.sum_congr rfl fun j _ => h1 j
    _ = locMap (∑ j, (LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y := by
        simp only [locMap, map_sum]
        exact (LinearMap.sum_apply Finset.univ _ y).symm
    _ = y := by
        rw [h2]
        simp only [locMap, IsLocalizedModule.map_id]
        rfl
end GroundTheory.Heights₂.Heights.Kleiman
