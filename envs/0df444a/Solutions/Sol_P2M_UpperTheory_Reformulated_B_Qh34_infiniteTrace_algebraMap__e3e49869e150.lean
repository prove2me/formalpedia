-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qh34_infiniteTrace_algebraMap__e3e49869e150
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:22:23.639556+00:00
-- url     : https://prove2.me/submissions/46ce026e-8979-4bc4-9824-b68bf1f506f3

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteTraceAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap
theorem _root_.solution.{u_1} :
    ∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (k : K),
      (UpperTheory.Reformulated.B.Qh34.infiniteTrace K : NumberField.InfiniteAdeleRing K → ℝ)
          ((Algebra.algebraMap K (NumberField.InfiniteAdeleRing K) : K → NumberField.InfiniteAdeleRing K) k) =
        (↑((Algebra.trace ℚ K : K → ℚ) k) : ℝ) := by
  classical
  intro K _ _ k
  have h1 : ((Algebra.trace ℚ K k : ℚ) : ℝ) = ∑ φ : K →+* ℂ, (φ k).re := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := k)
    have h' : ∑ φ : K →+* ℂ, φ k = ∑ σ : K →ₐ[ℚ] ℂ, σ k :=
      Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun _ => rfl)
    rw [← Complex.re_sum, h', ← h]
    simp
  rw [h1, ← Finset.sum_fiberwise Finset.univ NumberField.InfinitePlace.mk]
  change ∑ w : NumberField.InfinitePlace K, (↑w.mult : ℝ) *
    (NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w)).re = _
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w
      (algebraMap K (NumberField.InfiniteAdeleRing K) k w) = w.embedding k := by
    simp
  have h3 : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => NumberField.InfinitePlace.mk φ = w),
      (φ k).re = (w.embedding k).re := by
    intro φ hφ
    rw [← (Finset.mem_filter.1 hφ).2]
    rcases NumberField.InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, NumberField.ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [h2, Finset.sum_congr rfl h3, Finset.sum_const, NumberField.InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]
end UpperTheory.Reformulated.B.Qh34.infiniteTrace_algebraMap
