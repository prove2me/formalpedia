-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.repr_centralizer_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:52.782262+00:00
-- url     : https://prove2.me/submissions/b300e404-96d6-4e9b-ab18-50271f3b2367

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_IsChain
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainA
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_chain_repr_Npow
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_chain_repr_of_ker
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_chain_Npow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution (N : W →ₗ[E] W) {ι : Type} [Fintype ι] (l : ι → ℕ)
    (B : Module.Basis (Σ a, Fin (l a)) E W) (hB : IsChain N l B) (s : ι → ℕ) (_hs : ∀ a, s a ≤ l a)
    (hC : ∀ a b, s a ≤ s b + (l a - l b)) (v : W) (hv : v = ∑ a, if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0)
    (A : W →ₗ[E] W) (hA : A ∘ₗ N = N ∘ₗ A) (a : ι) (i : Fin (l a)) (hi : (i : ℕ) < s a) :
    B.repr (A v) ⟨a, i⟩ = 0 := by
  have hc : Commute A N := hA
  rw [hv, map_sum, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : s b < l b
  · rw [dif_pos hb]
    have hlb : 0 < l b := by omega
    have h1 : B ⟨b, ⟨s b, hb⟩⟩ = (N ^ s b) (B ⟨b, ⟨0, hlb⟩⟩) := by
      rw [chain_Npow_zero hB b hlb, dif_pos hb]
    have hcomm : ∀ m : ℕ, ∀ x, A ((N ^ m) x) = (N ^ m) (A x) := fun m x =>
      LinearMap.congr_fun (hc.pow_right m).eq x
    rw [h1, hcomm, chain_repr_Npow hB]
    split_ifs with h2
    · refine chain_repr_of_ker hB (l b) _ ?_ a _ ?_
      · rw [← hcomm, chain_Npow_zero hB b hlb, dif_neg (lt_irrefl _), map_zero]
      · have := hC a b
        show (i : ℕ) - s b + l b < l a
        omega
    · rfl
  · rw [dif_neg hb, map_zero, map_zero, Finsupp.zero_apply]
end PositivityTheory.RgUd.T.Nil.Orb.BReps
