-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_hdeg_subsingleton_d600335fc570
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:13:47.888014+00:00
-- url     : https://prove2.me/submissions/3b19e756-d6cb-453b-a4aa-8c3163c87471

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_surjective_68748e93ef42


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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
theorem _root_.solution {R' : Type*} [CommRing R'] [∀ I, Module R' (G I)] (deg : ∀ I, Submodule R' (G I))
    (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R'] G J) (i : ℕ) [IsEmpty (Cech.Idx U i)] :
    Subsingleton (Cech.Hdeg G deg ρ' i) := by
  have : Subsingleton (Cech.cocyDeg G deg ρ' i) :=
    ⟨fun a b => Subtype.ext (funext fun I => isEmptyElim I)⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, rfl⟩ := Cech.Hdeg_mk_surjective a
  obtain ⟨z', rfl⟩ := Cech.Hdeg_mk_surjective b
  rw [Subsingleton.elim z z']
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
