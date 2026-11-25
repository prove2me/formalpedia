-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:31.664475+00:00
-- url     : https://prove2.me/submissions/08589f5e-2960-492d-bc8a-1420a9db2a0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight

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
theorem _root_.solution (O : ValuationSubring k) (hO : IsCompact (O : Set k)) (hne : ∀ U ∈ 𝓝 (0 : k), ∃ a ≠ 0, a ∈ U)
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {b : k} (hb : ψ b ≠ 1) {V : Set (Matrix (Fin n) (Fin d) k)}
    (hV : V ∈ 𝓝 0) : ∃ (K : Set (Matrix (Fin n) (Fin d) k)) (Λ : OpenAddSubgroup (Matrix (Fin n) (Fin d) k)),
      (∀ Y, Y ∈ Λ ↔ ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1) ∧ (Λ : Set _) ⊆ V := by
  classical
  have hM : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ O} := by
    have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin d => hO
    simp only [Set.pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq] at this
    exact this
  have h1 : ∀ᶠ a in 𝓝 (0 : k), ∀ Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ O}, a • Y ∈ V :=
    hM.eventually_forall_of_forall_eventually fun Y _ =>
      (continuous_smul (M := k) (X := Matrix (Fin n) (Fin d) k)).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨a, ha0, ha⟩ := hne _ h1
  let K := (fun Y : Matrix (Fin n) (Fin d) k => (b / a) • Y) '' {Y | ∀ i j, Y i j ∈ O}
  have hK : IsCompact K := hM.image (continuous_const_smul _)
  let Λ : AddSubgroup (Matrix (Fin n) (Fin d) k) :=
    { carrier := {Y | ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1}
      add_mem' := fun h h' U hU => by rw [Matrix.add_mul, trace_add, AddChar.map_add_eq_mul, h U hU, h' U hU, one_mul]
      zero_mem' := fun U _ => by simp
      neg_mem' := fun h U hU => by rw [Matrix.neg_mul, trace_neg, AddChar.map_neg_eq_inv, h U hU, inv_one] }
  have h2 : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1 :=
    hK.eventually_forall_of_forall_eventually fun U _ => by
      have hc : Continuous fun z : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => trace (z.1 * z.2ᵀ) :=
        (continuous_fst.matrix_mul continuous_snd.matrix_transpose).matrix_trace
      simpa using (hψ.comp_continuous hc).eventually_eq (0, U)
  refine ⟨K, ⟨Λ, Λ.isOpen_of_mem_nhds h2⟩, fun _ => Iff.rfl, fun Y hY => ?_⟩
  have : ∀ i j, (a⁻¹ • Y) i j ∈ O := fun i j => by
    by_contra hn
    have h3 := (O.mem_or_inv_mem _).resolve_left hn
    have hy : Y i j ≠ 0 := fun h => hn (by simp [h])
    have h4 := hY _ ⟨Matrix.single i j ((a⁻¹ • Y) i j)⁻¹, fun i' j' => by
      rw [Matrix.single_apply]; split_ifs
      · exact h3
      · exact zero_mem _, rfl⟩
    apply hb
    rw [← h4]
    congr 1
    simp only [transpose_smul, Matrix.mul_smul, transpose_single, trace_smul, trace_mul_single, smul_eq_mul,
      Matrix.smul_apply, op_smul_eq_mul]
    field_simp
  have := ha _ this
  rwa [smul_smul, mul_inv_cancel₀ ha0, one_smul] at this
end PositivityTheory.ThKEst.W
