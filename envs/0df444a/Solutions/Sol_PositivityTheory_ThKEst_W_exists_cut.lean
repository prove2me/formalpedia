-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.exists_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:59.474804+00:00
-- url     : https://prove2.me/submissions/d30a46c8-7904-47d7-a638-7ab86d16c81d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight
import Theorems.Thm_PositivityTheory_ThKEst_W_rank_iff_right
import Theorems.Thm_PositivityTheory_ThKEst_W_isOpen_rank
import Theorems.Thm_PositivityTheory_ThKEst_W_exists_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.W
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {n d : ℕ}
namespace PositivityTheory.ThKEst.W
theorem _root_.solution [CharZero k] (O : ValuationSubring k) (hO : IsCompact (O : Set k))
    (hne : ∀ U ∈ 𝓝 (0 : k), ∃ a ≠ 0, a ∈ U) (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {b : k} (hb : ψ b ≠ 1)
    {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h0 : ∀ Y, Y.rank ≠ n → f Y = 0) :
    ∃ (m : ℕ) (g : Fin m → Matrix (Fin n) (Fin d) k → ℂ), f = ∑ i, g i ∧ ∀ i, g i ∈ SB _ ∧ (∀ Y, f Y = 0 → g i Y = 0) ∧
      ∃ Y₀, ∀ Z : Matrix (Fin n) (Fin d) k, Z.rank ≠ n → ∃ U : Matrix (Fin n) (Fin d) k,
        (∀ Y, g i Y ≠ 0 → ψ (trace (Y * Uᵀ)) = ψ (trace (Y₀ * Uᵀ))) ∧ ψ (trace ((Z - (Y₀ + Y₀)) * Uᵀ)) ≠ 1 := by
  classical
  have hS : IsCompact {Y | f Y ≠ 0} :=
    hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber 0).isOpen.isClosed_compl (subset_tsupport _)
  obtain ⟨V, hV, hVS⟩ := compact_open_separated_add_right (hS.image (f := fun Y => Y + Y) (by fun_prop))
    (isOpen_rank (k := k) (n := n) (d := d)) (by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨C, hC⟩ := (rank_iff_right Y).1 (by by_contra h; exact hY (h0 Y h))
      refine (rank_iff_right _).2 ⟨(2⁻¹ : k) • C, ?_⟩
      rw [Matrix.mul_smul, Matrix.add_mul, hC, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul])
  obtain ⟨K, Λ, hΛ, hΛV⟩ := exists_dual O hO hne ψ hψ hb hV
  let Q := Matrix (Fin n) (Fin d) k ⧸ Λ.toAddSubgroup
  haveI : DiscreteTopology Q := QuotientAddGroup.discreteTopology Λ.isOpen
  let p : Matrix (Fin n) (Fin d) k → Q := QuotientAddGroup.mk
  have hp : Continuous p := QuotientAddGroup.continuous_mk
  have hT : (p '' {Y | f Y ≠ 0}).Finite := (hS.image hp).finite_of_discrete
  let T := hT.toFinset
  let q : Fin T.card → Q := fun i => (T.equivFin.symm i).1
  refine ⟨T.card, fun i Y => if p Y = q i then f Y else 0, ?_, fun i => ⟨⟨?_, ?_⟩, fun Y hY => by simp [hY], ?_⟩⟩
  · funext Y
    rw [Finset.sum_apply, T.equivFin.symm.sum_comp (fun s => if p Y = s.1 then f Y else 0),
      Finset.sum_coe_sort T (fun s => if p Y = s then f Y else 0), Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra h'
      exact h (hT.mem_toFinset.2 ⟨Y, h', rfl⟩)
  · exact (((IsLocallyConstant.iff_continuous p).2 hp).prodMk hf.1).comp fun z => if z.1 = q i then z.2 else 0
  · exact HasCompactSupport.intro hS fun Y hY => by simp [not_not.1 hY]
  · obtain ⟨Y₀, hY₀, e⟩ := hT.mem_toFinset.1 (T.equivFin.symm i).2
    refine ⟨Y₀, fun Z hZ => ?_⟩
    have : Z - (Y₀ + Y₀) ∉ Λ := fun h => hZ (hVS ⟨Y₀ + Y₀, ⟨Y₀, hY₀, rfl⟩, _, hΛV h, add_sub_cancel _ _⟩)
    rw [hΛ] at this
    push Not at this
    obtain ⟨U, hU, h⟩ := this
    refine ⟨U, fun Y hY => ?_, h⟩
    have h1 : p Y₀ = p Y := by
      by_contra h'
      exact hY (if_neg fun h'' => h' (e.trans h''.symm))
    have h2 := (hΛ _).1 (QuotientAddGroup.eq.1 h1) U hU
    rw [show Y = Y₀ + (-Y₀ + Y) by abel, Matrix.add_mul, trace_add, AddChar.map_add_eq_mul, h2, mul_one]
end PositivityTheory.ThKEst.W
