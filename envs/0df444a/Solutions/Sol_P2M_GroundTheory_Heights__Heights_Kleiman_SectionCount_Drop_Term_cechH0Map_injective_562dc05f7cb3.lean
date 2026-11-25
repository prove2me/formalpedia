-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_cechH0Map_injective_562dc05f7cb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:51.119643+00:00
-- url     : https://prove2.me/submissions/3420e445-5127-42ee-acac-6cefa9463b95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R]
  {G G' : Cell U → Type*} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
theorem _root_.solution (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m))
    (hinj : ∀ I : Cech.Idx U 0, Function.Injective (φ I.1)) : Function.Injective (cechH0Map φ hφ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hz' : cechZeroCocycleMap φ hφ s ∈ (Cech.bdry G' ρ' 0).comap (LinearMap.ker (Cech.d G' ρ' 0)).subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  change _ = (0 : Cech.H G ρ 0)
  rw [show (0 : Cech.H G ρ 0) = Submodule.Quotient.mk 0 from rfl]
  apply congrArg
  apply Subtype.ext
  change (Cech.mapC φ 0 (s : Cech.Cochain G 0)) ∈ (⊥ : Submodule R (Cech.Cochain G' 0)) at hz'
  change (s : Cech.Cochain G 0) = 0
  change (s : Cech.Cochain G 0) ∈ (⊥ : Submodule R (Cech.Cochain G 0))
  rw [Submodule.mem_bot] at hz'
  funext I
  have h1 := congrFun hz' I
  change φ I.1 ((s : Cech.Cochain G 0) I) = 0 at h1
  exact hinj I (h1.trans (map_zero _).symm)
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
