-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_gam_089b125b1417
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:59.869776+00:00
-- url     : https://prove2.me/submissions/5479527a-05a6-45de-a62e-7346d1897506

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_gam_550215db2da5

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
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
theorem _root_.solution (F : SubSystem S x E) {f : Poly S N} {d : ℕ} (hf : f.IsHomogeneous d) {c : ℤ}
    {m : E} (hm : m ∈ F.gam c) : aeval x f • m ∈ F.gam (c + d) := by
  rw [mem_gam] at hm ⊢
  intro J
  have h := smul_mem_twist F (J := J) (s := 1) (e := 0) (d := d) (one_mem _) hf
    (isHomogeneous_one _ _) (by simp) (hm J)
  rwa [map_one, div_one] at h
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
