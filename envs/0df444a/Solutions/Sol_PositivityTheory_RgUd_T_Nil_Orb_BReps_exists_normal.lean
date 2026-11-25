-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:22.477863+00:00
-- url     : https://prove2.me/submissions/12a18336-5694-44a6-aeb8-c193fe9f436c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_ChainB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_CentralizerRepresentatives_Normal
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_exists_good
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Orb_BReps_repr_centralizer_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps
variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]
namespace PositivityTheory.RgUd.T.Nil.Orb.BReps
theorem _root_.solution [FiniteDimensional E W] (N : W →ₗ[E] W) (hN : IsNilpotent N) (v : W) :
    ∃ (ι : Type) (_ : Fintype ι) (l s : ι → ℕ) (B : Module.Basis (Σ a, Fin (l a)) E W), IsChain N l B ∧
      (∀ a, 0 < l a) ∧ (∀ a, s a ≤ l a) ∧ v = ∑ a, (if h : s a < l a then B ⟨a, ⟨s a, h⟩⟩ else 0) ∧
      ∀ A : W →ₗ[E] W, A ∘ₗ N = N ∘ₗ A → ∀ (a : ι) (i : Fin (l a)), (i : ℕ) < s a → B.repr (A v) ⟨a, i⟩ = 0 := by
  obtain ⟨ι, _, l, s, B, hB, hl, hs, hC, hv⟩ := exists_good N hN v
  exact ⟨ι, inferInstance, l, s, B, hB, hl, hs, hv, fun A hA a i hi =>
    repr_centralizer_eq_zero N l B hB s hs hC v hv A hA a i hi⟩
end PositivityTheory.RgUd.T.Nil.Orb.BReps
