-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_smul_mem_twist_52f704e931ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:37:37.735976+00:00
-- url     : https://prove2.me/submissions/c33fb36c-c76e-4b37-9a03-034d8c06775c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mul_mem_twistMod_274474b12649

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
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
theorem _root_.solution (F : SubSystem S x E) {J : Chart x} {f s : Poly S N} {e e' : ℕ} {d c : ℤ}
    (hs : s ∈ monos J.1) (hf : f.IsHomogeneous e') (hse : s.IsHomogeneous e) (hd : (e' : ℤ) = e + d)
    {m : E} (hm : m ∈ (F.twist (twistSys S x c)).sub J) :
    (aeval x f / aeval x s) • m ∈ (F.twist (twistSys S x (c + d))).sub J := by
  refine Submodule.span_induction (p := fun m _ =>
    (aeval x f / aeval x s) • m ∈ (F.twist (twistSys S x (c + d))).sub J) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.subset_span ⟨_, mul_mem_twistMod hs hf hse hd hq, y, hy, ?_⟩
    rw [smul_smul]
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a m _ hm
    have h : (aeval x f / aeval x s) • (a • m) = a • ((aeval x f / aeval x s) • m) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [h]
    exact Submodule.smul_mem _ a hm
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
