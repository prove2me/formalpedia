-- Prove2me | solution 1 for PositivityTheory.KReal.extreme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:13.2562+00:00
-- url     : https://prove2.me/submissions/fc1245fb-036a-475b-9fd7-c276b7745b6d

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasW
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreComb
import Theorems.Thm_PositivityTheory_KReal_top_idx
import Theorems.Thm_PositivityTheory_KReal_bot_idx
import Theorems.Thm_PositivityTheory_KReal_cw_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {r s : ℕ} {ν La : Ix r s → ℚ} (hD : Dom ν) :
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inr j) (.inl i) La →
      (∀ i', i' < i → La (.inl i') = La (.inl i)) → (∀ j', j < j' → La (.inr j') = La (.inr j)) →
      0 < La (.inl i) - La (.inr j) →
      (r : ℚ) + s < 2 * (La (.inl i) - La (.inr j)) + 2 + (rho2 (.inl i : Ix r s) - rho2 (.inr j : Ix r s))) ∧
    (∀ (i : Fin r) (j : Fin s), RootTo ν (.inl i) (.inr j) La →
      (∀ j', j' < j → La (.inr j') = La (.inr j)) → (∀ i', i < i' → La (.inl i') = La (.inl i)) →
      0 < La (.inr j) - La (.inl i) →
      (r : ℚ) + s < 2 * (La (.inr j) - La (.inl i)) + 2 + (rho2 (.inr j : Ix r s) - rho2 (.inl i : Ix r s))) := by
  constructor
  · intro i j hR hi hj hpos
    have hne : (Sum.inr j : Ix r s) ≠ Sum.inl i := Sum.inr_ne_inl
    obtain ⟨ea, eb, eo⟩ := cw_root hne hR
    have h0 : (i : ℕ) = 0 := by
      refine top_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ eb ?_ hi
      · intro i' hi'
        exact hD (.inl i') (.inl i) hi'
      · intro i' hi'
        exact eo _ Sum.inl_ne_inr (fun e => hi' (Sum.inl_injective e))
    have h1 : (j : ℕ) + 1 = s := by
      refine bot_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ ea ?_ hj
      · intro j' hj'
        exact hD (.inr j) (.inr j') hj'
      · intro j' hj'
        exact eo _ (fun e => hj' (Sum.inr_injective e)) Sum.inr_ne_inl
    have h0' : ((i : ℕ) : ℚ) = 0 := by exact_mod_cast h0
    have h1' : ((j : ℕ) : ℚ) + 1 = s := by exact_mod_cast h1
    simp only [rho2]
    linarith
  · intro i j hR hj hi hpos
    have hne : (Sum.inl i : Ix r s) ≠ Sum.inr j := Sum.inl_ne_inr
    obtain ⟨ea, eb, eo⟩ := cw_root hne hR
    have h0 : (j : ℕ) = 0 := by
      refine top_idx (fun k => La (.inr k)) (fun k => ν (.inr k)) j ?_ eb ?_ hj
      · intro j' hj'
        exact hD (.inr j') (.inr j) hj'
      · intro j' hj'
        exact eo _ Sum.inr_ne_inl (fun e => hj' (Sum.inr_injective e))
    have h1 : (i : ℕ) + 1 = r := by
      refine bot_idx (fun k => La (.inl k)) (fun k => ν (.inl k)) i ?_ ea ?_ hi
      · intro i' hi'
        exact hD (.inl i) (.inl i') hi'
      · intro i' hi'
        exact eo _ (fun e => hi' (Sum.inl_injective e)) Sum.inl_ne_inr
    have h0' : ((j : ℕ) : ℚ) = 0 := by exact_mod_cast h0
    have h1' : ((i : ℕ) : ℚ) + 1 = r := by exact_mod_cast h1
    simp only [rho2]
    linarith
end PositivityTheory.KReal
