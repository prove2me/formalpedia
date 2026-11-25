-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SurjectiveClosed_mem_bdry_of_subsingleton_9fd4ef684c7c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:37.352165+00:00
-- url     : https://prove2.me/submissions/ea869015-3897-4abe-9fde-d6193d9e3241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeVanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSurjectiveClosed

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
open GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
namespace GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
theorem _root_.solution {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
    {G : Cell U → Type w} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {i : ℕ} (h : Subsingleton (Cech.H G ρ i))
    (z : Cech.Cochain G i) (hz : z ∈ LinearMap.ker (Cech.d G ρ i)) : z ∈ Cech.bdry G ρ i :=
  Submodule.mem_comap.mp <| (Submodule.Quotient.mk_eq_zero
    ((Cech.bdry G ρ i).comap (LinearMap.ker (Cech.d G ρ i)).subtype)).mp
    (@Subsingleton.elim _ h (Submodule.Quotient.mk ⟨z, hz⟩ : Cech.H G ρ i) 0)
end GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed
