-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_mem_minimalPrimes_6f9a6b133d70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:13:40.571304+00:00
-- url     : https://prove2.me/submissions/fccbd05a-3fa2-4107-bc3c-62a310dbfa54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_dim_add_one_le_1001d893a53e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_isRelevant_of_le_ea828c116e8a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
theorem _root_.solution {J Q : Ideal (MRing ι)} {n : ℕ} (hQ : IsArithVar Q n) (hJQ : J ≤ Q)
    (hdim : ∀ M ∈ J.minimalPrimes, IsRelevant M → IsHorizontal M → IsArithVar M n) :
    Q ∈ J.minimalPrimes := by
  have hQp : Q.IsPrime := hQ.2.1.1
  refine ⟨⟨hQp, hJQ⟩, fun q hq hqQ => ?_⟩
  have : q.IsPrime := hq.1
  obtain ⟨M, hM, hMq⟩ := Ideal.exists_minimalPrimes_le hq.2
  have hMQ : M ≤ Q := hMq.trans hqQ
  have hQh : Q.comap (C : ℤ →+* MRing ι) = ⊥ := hQ.2.2.1
  have hMh : IsHorizontal M := by
    show M.comap (C : ℤ →+* MRing ι) = ⊥
    rw [eq_bot_iff, ← hQh]
    exact Ideal.comap_mono hMQ
  have hMn := hdim M hM (isRelevant_of_le hQ.2.1.2.2 hMQ) hMh
  have : M.IsPrime := hM.1.1
  refine le_trans ?_ hMq
  by_contra hQM
  obtain ⟨x, hxQ, hxM⟩ := Set.not_subset.1 hQM
  have h := dim_add_one_le hMQ hxQ hxM
  rw [hQ.2.2.2, hMn.2.2.2] at h
  have h2 : n + Fintype.card K + 1 ≤ n + Fintype.card K := by exact_mod_cast h
  omega
end GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
