-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_eq_3d2fa305b23b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:52:04.464902+00:00
-- url     : https://prove2.me/submissions/8f0ebd36-a8fb-42d4-94a7-41dff9f52985

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeVanishLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locConeE_mk_f17973bed795
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bijective_smul_of_isHomogeneous_7a9bef9a2abe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) {m : M.coneSubE}
    {s : monos (S := S) I} {w : ConeE S x E} (h : (s : Poly S N) • w = m) :
    locConeE M I hI (LocalizedModule.mk m s) = w := by
  obtain ⟨e, he⟩ := monos_isHomogeneous s.2
  exact (bijective_smul_of_isHomogeneous he (aeval_ne_zero_of_mem_monos_support hI s.2)).1
    ((locConeE_mk M I hI m s).trans h.symm)
end GroundTheory.Heights₂.Heights.Kleiman
