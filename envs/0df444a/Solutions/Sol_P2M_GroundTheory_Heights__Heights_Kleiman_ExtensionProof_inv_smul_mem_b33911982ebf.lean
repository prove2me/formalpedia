-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_inv_smul_mem_b33911982ebf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:22:08.528163+00:00
-- url     : https://prove2.me/submissions/74979638-6595-4303-94ba-a4f07b720e66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mem_of_mem_twist_zero_2b5c0ee4a651

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
theorem _root_.solution (F : SubSystem S x E) {I : Chart x} {c : ℤ} {m : E}
    (hm : m ∈ (F.twist (twistSys S x c)).sub I) {s : Poly S N} {e : ℕ} (hs : s ∈ monos I.1)
    (hse : s.IsHomogeneous e) (hec : (e : ℤ) = c) : (aeval x s)⁻¹ • m ∈ F.sub I := by
  have h := smul_mem_twist F (f := 1) (e' := 0) (d := -(e : ℤ)) hs (isHomogeneous_one _ _) hse
    (by simp) hm
  rw [show c + -(e : ℤ) = 0 by omega, map_one, one_div] at h
  exact mem_of_mem_twist_zero F h
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
