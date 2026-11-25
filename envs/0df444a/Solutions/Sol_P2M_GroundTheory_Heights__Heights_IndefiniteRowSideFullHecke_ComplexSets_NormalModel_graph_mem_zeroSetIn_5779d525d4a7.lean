-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_graph_mem_zeroSetIn_5779d525d4a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:08.670049+00:00
-- url     : https://prove2.me/submissions/48f990e3-f9a5-4537-a70c-c7e5c2fe1358

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelGraph
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModel_exists_clear_denominators_7fad8e9ba6f2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace NormalModel
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : NormalModel J) (a b : Fin M.m → MvPolynomial (Fin n) ℂ)
    (hab : ∀ i, rename Sum.inl (b i) * X (Sum.inr i) - rename Sum.inl (a i) ∈ M.ideal)
    (x : Fin n → ℂ) (hx : x ∈ zeroSetIn J) (hb : ∀ i, eval x (b i) ≠ 0) :
    (Sum.elim x fun i => eval x (a i) / eval x (b i)) ∈ zeroSetIn M.ideal := by
  intro q hq
  obtain ⟨N, r, h, e⟩ := M.exists_clear_denominators a b hab x hb q
  have hr : rename Sum.inl r ∈ M.ideal := by
    have := M.ideal.sub_mem (M.ideal.mul_mem_left (rename Sum.inl ((∏ i, b i) ^ N)) hq) h
    simpa using this
  have hrJ : r ∈ J := by
    rw [← M.comap_eq]
    exact hr
  have hBx : eval x (∏ i, b i) ^ N ≠ 0 := by
    rw [map_prod]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => hb i)
  have h0 : eval x (∏ i, b i) ^ N * eval (Sum.elim x fun i => eval x (a i) / eval x (b i)) q = 0 := by
    rw [← e]
    exact hx r hrJ
  exact (mul_eq_zero.1 h0).resolve_left hBx
end NormalModel
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
