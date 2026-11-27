-- Prove2me | solution 1 for UpperTheory.Lit.Mix.multiProd_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:23.066653+00:00
-- url     : https://prove2.me/submissions/698a3601-a227-4472-8761-883f1a00aa55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
import Definitions.Def_Development_AutomorphicArithmetic_ThetaCorrespondence_GeneralLinearGroups_MultiAt
import Theorems.Thm_P2M_UpperTheory_Lit_Mix_ind__at_8cfc4edaf794
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_iff_of_equiv
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_isIrreducible_multiProd_zero
import Theorems.Thm_GlobalTheory_SmGL_MultiIrr_multiProd_succ_equiv
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_isUnitarisable_multiProd
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_parInd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr ValuativeRel Matrix
open scoped TensorProduct
open UpperTheory UpperTheory.Lit UpperTheory.Lit.Mix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace UpperTheory.Lit.Mix
theorem _root_.solution (H : TwoAt k) {s : ℕ} :
    ∀ {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {n : Type} [Fintype n] [DecidableEq n]
    (e : (Σ i, m i) ≃ n) {X : Fin s → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {σ : ∀ i, Representation ℂ (GL (m i) k) (X i)}, (∀ i, IsSmooth (σ i)) → (∀ i, (σ i).IsIrreducible) →
    (∀ i, IsUnitarisable (σ i)) → (multiProd e σ).IsIrreducible := by
  induction s with
  | zero => exact fun e _ _ _ σ _ _ _ => isIrreducible_multiProd_zero e σ
  | succ s ih =>
    intro m _ _ n _ _ e X _ _ σ hs hi hu
    obtain ⟨E⟩ := multiProd_succ_equiv e σ
    exact (isIrreducible_iff_of_equiv E).1 (ind₂_at H _ (hs 0) (hi 0) (hu 0) (isSmooth_parInd _ _)
      (ih _ (fun i => hs i.succ) (fun i => hi i.succ) fun i => hu i.succ)
      (UnitInd.isUnitarisable_multiProd _ fun i => hu i.succ))
end UpperTheory.Lit.Mix
