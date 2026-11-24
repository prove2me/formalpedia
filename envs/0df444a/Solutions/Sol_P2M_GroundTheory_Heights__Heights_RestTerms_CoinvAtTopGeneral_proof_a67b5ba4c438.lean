-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTopGeneral_proof_a67b5ba4c438
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:09:45.884926+00:00
-- url     : https://prove2.me/submissions/d94edff5-2aff-43f6-bc72-9a25a86f4fb8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAtTopGeneral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Coinv
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CoinvAtTopGeneral
theorem _root_.solution (h1 : CoinvAtTop.Statement) : CoinvAtTopGeneral.Statement := by
  intro K _ _ β ι _ _ _ _ o H hH
  let ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) :=
    (Fintype.equivFin β).prodCongr o
  have hR : (rename ψ H).IsHomogeneous (coinvTop (Fintype.card β) (Fintype.card ι)) :=
    hH.rename_isHomogeneous
  obtain ⟨c, hc⟩ := h1 K _ _ (rename ψ H) hR
  refine ⟨c, ?_⟩
  set I : Ideal (MvPolynomial (β × ι) K) := Ideal.span {P | ∃ (m : ℕ) (b : β), 1 ≤ m ∧
    m ≤ Fintype.card ι ∧ P = ∑ i : ι, X (b, i) ^ m} with hI
  have hle : psumIdeal K (Fintype.card β) (Fintype.card ι) ≤
      I.comap (rename ψ.symm : MvPolynomial _ K →ₐ[K] MvPolynomial (β × ι) K) := by
    refine Ideal.span_le.mpr ?_
    rintro P ⟨m, b, hm1, hm2, rfl⟩
    refine Ideal.subset_span ⟨m, (Fintype.equivFin β).symm b, hm1, hm2, ?_⟩
    simp only [bps, map_sum, map_pow, rename_X]
    refine Fintype.sum_equiv o.symm _ _ (fun i => ?_)
    simp [ψ]
  have hH' : rename ψ.symm (rename ψ H) = H := by
    rw [rename_rename]
    simp
  have hst : rename ψ.symm (monomial (staircase (Fintype.card β) (Fintype.card ι)) (1 : K)) =
      ∏ b : β, ∏ i : ι, X (b, i) ^ (o i : ℕ) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [map_one, one_mul, map_prod, map_pow, rename_X]
    rw [← Fintype.prod_prod_type']
    refine Fintype.prod_equiv ψ.symm _ _ (fun v => ?_)
    simp [staircase, ψ, Prod.map]
  have key := hle hc
  rw [Ideal.mem_comap, map_sub, map_mul, algHom_C, hH', hst] at key
  simpa using key
end CoinvAtTopGeneral
end GroundTheory.Heights₂.Heights.RestTerms
