-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_iInf_dc81a4ab244c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:20.136728+00:00
-- url     : https://prove2.me/submissions/ceadb1f0-26de-4528-9594-0b21ac64fc7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_EquivAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace HeightOneIntersection
theorem _root_.solution :
    ((⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) : Submodule A K) : Set K) =
      ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by
  ext x
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Set.mem_iInter]
  have key : ∀ (p : Ideal A) [p.IsPrime],
      x ∈ GroundTheory.Heights₂.Heights.Model.localizedIn p
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K)) ↔ x ∈ locIn A K p := by
    intro p _
    change (∃ s : A, s ∉ p ∧ s • x ∈ (⊥ : Subalgebra A K)) ↔
      ∃ a s : A, s ∉ p ∧ algebraMap A K s * x = algebraMap A K a
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hsx
      exact ⟨a, s, hs, by rw [ha, Algebra.smul_def]⟩
    · rintro ⟨a, s, hs, h⟩
      refine ⟨s, hs, Algebra.mem_bot.mpr ⟨a, ?_⟩⟩
      rw [Algebra.smul_def, h]
  constructor
  · intro h p hp h1
    exact (key p).mp (h ⟨p, hp⟩ h1)
  · intro h p h1
    exact (key p.asIdeal).mpr (h p.asIdeal p.isPrime h1)
end HeightOneIntersection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
