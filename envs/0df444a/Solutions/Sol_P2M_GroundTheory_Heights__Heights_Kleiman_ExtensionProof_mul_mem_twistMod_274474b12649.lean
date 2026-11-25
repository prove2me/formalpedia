-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_mul_mem_twistMod_274474b12649
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:01:23.164078+00:00
-- url     : https://prove2.me/submissions/22034cdf-d6e5-4191-9275-a49a79b519ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension

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
theorem _root_.solution {J : Chart x} {f s : Poly S N} {e e' : ℕ} {d c : ℤ} (hs : s ∈ monos J.1)
    (hf : f.IsHomogeneous e') (hse : s.IsHomogeneous e) (hd : (e' : ℤ) = e + d) {q : Ω}
    (hq : q ∈ twistMod S x c J) : aeval x f / aeval x s * q ∈ twistMod S x (c + d) J := by
  refine Submodule.span_induction
    (p := fun q _ => aeval x f / aeval x s * q ∈ twistMod S x (c + d) J) ?_ ?_ ?_ ?_ hq
  · rintro _ ⟨g, t, k, k', ht, hg, hkt, hk, rfl⟩
    refine Submodule.subset_span ⟨f * g, s * t, e + k, e' + k', mul_mem hs ht, hf.mul hg,
      hse.mul hkt, by push_cast; omega, ?_⟩
    rw [map_mul, map_mul, div_mul_div_comm]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
  · intro a q _ hq
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hq
end GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
