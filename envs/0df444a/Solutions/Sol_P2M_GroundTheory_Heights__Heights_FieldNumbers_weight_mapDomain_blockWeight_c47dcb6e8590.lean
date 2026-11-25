-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_blockWeight_c47dcb6e8590
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:28.397047+00:00
-- url     : https://prove2.me/submissions/466a83cc-b74c-4119-a6b6-1466d53a0d43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k'))
    (hg : ∀ v, (g v).1 = j v.1) (u : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g u) =
      Function.extend j (Finsupp.weight (blockWeight ι) u) 0 := by
  have key : (Finsupp.weight (R := ℕ) (blockWeight ι')).comp
        (Finsupp.mapDomain.addMonoidHom (M := ℕ) g) =
      (extendAddHom j).comp (Finsupp.weight (R := ℕ) (blockWeight ι)) := by
    ext v
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, Finsupp.weight_single,
      one_smul]
    show blockWeight ι' (g v) _ = Function.extend j (blockWeight ι v) 0 _
    rename_i k'
    simp only [blockWeight, hg v]
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      rw [j.injective.extend_apply]
      by_cases hav : a = v.1
      · subst hav; simp
      · rw [Pi.single_eq_of_ne (fun e => hav (j.injective e)), Pi.single_eq_of_ne hav]
    · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun e => h ⟨v.1, e.symm⟩)]
      rfl
  exact DFunLike.congr_fun key u
end GroundTheory.Heights₂.Heights.FieldNumbers
