-- Prove2me | solution 1 for PadicAlgCl.exists_mem_adjoin_padicEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8dd600ac-a20b-523d-8341-104c0235239d

import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_mem_adjoin_padicEmbedding

set_option autoImplicit false
open scoped IntermediateField
open Polynomial
open scoped Pointwise

private theorem exists_padicEmbedding_eq_of_isIntegral_A (q : ℕ) [Fact q.Prime] {β : PadicAlgCl q}
    (hβ : IsIntegral ℚ β) : ∃ b : AlgebraicClosure ℚ, padicEmbedding q b = β := by
  classical
  set p : ℚ[X] := minpoly ℚ β with hp
  have hpm : p.Monic := minpoly.monic hβ
  set pQ : (AlgebraicClosure ℚ)[X] := p.map (algebraMap ℚ (AlgebraicClosure ℚ)) with hpQ
  have hsplit : pQ.Splits := IsAlgClosed.splits _
  have hcard : pQ.roots.card = pQ.natDegree := hsplit.natDegree_eq_card_roots.symm
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (f := (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q))
    (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q).injective hcard
  have hpL : pQ.map (padicEmbedding q : AlgebraicClosure ℚ →+* PadicAlgCl q)
      = p.map (algebraMap ℚ (PadicAlgCl q)) := by
    rw [hpQ, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  have hβroot : β ∈ (p.map (algebraMap ℚ (PadicAlgCl q))).roots := by
    rw [Polynomial.mem_roots (hpm.map _).ne_zero, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ β
  rw [← hpL, ← hmap, Multiset.mem_map] at hβroot
  obtain ⟨b, -, hb⟩ := hβroot
  exact ⟨b, hb⟩

theorem solution
    (q : ℕ) [Fact q.Prime] (α : PadicAlgCl q) :
    ∃ b : AlgebraicClosure ℚ, α ∈ ℚ_[q]⟮padicEmbedding q b⟯ := by
  classical
  haveI : IsKrasner ℚ_[q] (PadicAlgCl q) := IsKrasner.of_completeSpace _ _
  have hαi : IsIntegral ℚ_[q] α := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[q]) α).isIntegral
  set f : ℚ_[q][X] := minpoly ℚ_[q] α with hf
  have hfm : f.Monic := minpoly.monic hαi
  have hfα : aeval α f = 0 := minpoly.aeval _ _

  set S : Finset (PadicAlgCl q) := ((f.aroots (PadicAlgCl q)).toFinset).erase α with hS
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ ≤ ‖α - x‖ := by
    by_cases hS0 : S.Nonempty
    · obtain ⟨x, hx, hmin⟩ := S.exists_min_image (fun x => ‖α - x‖) hS0
      have hxα : x ≠ α := (Finset.mem_erase.mp hx).1
      exact ⟨‖α - x‖, norm_pos_iff.mpr (sub_ne_zero.mpr hxα.symm), hmin⟩
    · exact ⟨1, one_pos, fun x hx => (hS0 ⟨x, hx⟩).elim⟩

  have hn0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hαi).ne'
  have hC0 : 0 < max ‖α‖ 1 := lt_max_of_lt_right one_pos
  have hC0' : max ‖α‖ 1 ≠ 0 := hC0.ne'
  obtain ⟨ε, hε0, hbound⟩ : ∃ ε : ℝ, 0 < ε ∧
      ((f.natDegree + 1 : ℝ) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖α‖ 1 < δ := by
    refine ⟨(δ / (2 * max ‖α‖ 1)) ^ f.natDegree / (f.natDegree + 1), by positivity, ?_⟩
    rw [mul_div_cancel₀ _ (by positivity : (f.natDegree + 1 : ℝ) ≠ 0),
      Real.pow_rpow_inv_natCast (by positivity) hn0]
    have : δ / (2 * max ‖α‖ 1) * max ‖α‖ 1 = δ / 2 := by
      field_simp
    rw [this]
    linarith

  have hd : DenseRange (algebraMap ℚ ℚ_[q]) := Padic.denseRange_ratCast q
  obtain ⟨g, hgm, hgdeg, hgc⟩ :=
    Polynomial.exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt
      (K := ℚ) (L := ℚ_[q]) hd hfm hε0
  have hg'm : (g.map (algebraMap ℚ ℚ_[q])).Monic := hgm.map _
  have hg'deg : (g.map (algebraMap ℚ ℚ_[q])).natDegree = f.natDegree := by
    rw [hgm.natDegree_map, hgdeg]

  obtain ⟨β, hβ, hαβ⟩ := Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
    (K := ℚ_[q]) (L := PadicAlgCl q) hε0 hfα hfm hg'm hg'deg hgc (IsAlgClosed.splits _)
  have hαβ' : ‖α - β‖ < δ := hαβ.trans hbound

  have hβg : aeval β g = 0 := by
    have h := (Polynomial.mem_aroots'.mp hβ).2
    rwa [Polynomial.aeval_map_algebraMap] at h
  have hβi : IsIntegral ℚ β := ⟨g, hgm, by rwa [← Polynomial.aeval_def]⟩
  obtain ⟨b, hb⟩ := exists_padicEmbedding_eq_of_isIntegral_A q hβi
  refine ⟨b, ?_⟩
  rw [hb]

  refine IsKrasner.krasner (K := ℚ_[q]) (minpoly.irreducible hαi).separable (IsAlgClosed.splits _)
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[q]) β).isIntegral ?_
  intro x' hx' hne
  refine hαβ'.trans_le (hδ x' ?_)
  rw [hS, Finset.mem_erase, Multiset.mem_toFinset, Polynomial.mem_aroots']
  exact ⟨fun h => hne h.symm, (hfm.map _).ne_zero, hx'.aeval_eq_zero⟩

end S_PadicAlgCl_exists_mem_adjoin_padicEmbedding
end P2MW
export P2MW.S_PadicAlgCl_exists_mem_adjoin_padicEmbedding (solution)
