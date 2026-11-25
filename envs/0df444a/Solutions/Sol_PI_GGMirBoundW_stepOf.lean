-- Prove2me | solution 1 for PI.GGMirBoundW.stepOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:33.832611+00:00
-- url     : https://prove2.me/submissions/09b5eacb-7a85-4ca1-be15-85c115cf3d37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_LastRowMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CardNonzero
import Theorems.Thm_PI_GGMirBoundW_card_nonzero
import Theorems.Thm_PI_GGMirBoundW_blkM_cc
import Theorems.Thm_PI_GGMirBoundW_blkM_cl
import Theorems.Thm_PI_GGMirBoundW_blkM_lc
import Theorems.Thm_PI_GGMirBoundW_blkM_ll
import Theorems.Thm_PI_GGMirBoundW_colM_cc
import Theorems.Thm_PI_GGMirBoundW_colM_cl
import Theorems.Thm_PI_GGMirBoundW_colM_lc
import Theorems.Thm_PI_GGMirBoundW_colM_ll
import Theorems.Thm_PI_GGMirBoundW_lastRowE_E
import Theorems.Thm_PI_GGMirBoundW_lastRow_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.GGMirBoundW.blkM_cc
attribute [local simp] PI.GGMirBoundW.blkM_cl
attribute [local simp] PI.GGMirBoundW.blkM_lc
attribute [local simp] PI.GGMirBoundW.blkM_ll
attribute [local simp] PI.GGMirBoundW.colM_cc
attribute [local simp] PI.GGMirBoundW.colM_cl
attribute [local simp] PI.GGMirBoundW.colM_lc
attribute [local simp] PI.GGMirBoundW.colM_ll



set_option autoImplicit false
open PI PI.GGMirBoundW
open Finset Matrix Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution : StepOf := by
  intro hB hC hJ hR hO hS F _ _ n IH ψ₀ hψ V _ _ π ℓ hℓ hW

  let π' : Representation ℂ (GL (Fin (n + 1)) F) V := π.comp (E F (n + 1))
  have hW' : IsWhit ψ₀ π' ℓ := by
    intro u hu v
    have h := hW (E F (n + 1) u) (hB F (n + 1) u hu).1 v
    simp only [psiU] at h ⊢
    rw [(hB F (n + 1) u hu).2] at h
    exact h
  obtain ⟨p, hpL, hpI⟩ := IH ψ₀ hψ V π' ℓ hℓ hW'
  let R := {r : Fin (n + 1) → F // r ≠ 0}
  choose g hg using fun r : R => hR F n r.1 r.2
  let A : R × Fin (D F (n + 1)) → GL (Fin (n + 1)) F := fun q => p q.2 * g q.1
  have hArow : ∀ q j, (A q : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j := by
    intro q j
    show ((p q.2 * g q.1 : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j = q.1.1 j
    rw [lastRow_mul (hpL q.2), hg]
  let f : R × Fin (D F (n + 1)) → Module.Dual ℂ V := fun q => ℓ ∘ₗ π (E F (n + 1) (A q))

  have hf : ∀ (x : Fin (n + 1) → F) (r : R) (i : Fin (D F (n + 1))),
      (π (col x)).dualMap (f (r, i)) = (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x • f (r, i) := by
    intro x r i
    ext v
    show ℓ (π (E F (n + 1) (A (r, i))) (π (col x) v)) = ψ₀ (r.1 ⬝ᵥ x) * ℓ (π (E F (n + 1) (A (r, i))) v)
    rw [← Module.End.mul_apply, ← map_mul, hJ F (n + 1) (A (r, i)) x, map_mul, Module.End.mul_apply,
      hW _ (hC F n _).1, psiU, (hC F n _).2]
    congr 2
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hArow]

  have hblock : ∀ r : R, LinearIndependent ℂ (fun i => f (r, i)) := by
    intro r
    have he : (fun i => f (r, i)) = (π (E F (n + 1) (g r))).dualMap ∘ (fun i => ℓ ∘ₗ π' (p i)) := by
      funext i
      ext v
      show ℓ (π (E F (n + 1) (p i * g r)) v) = ℓ (π (E F (n + 1) (p i)) (π (E F (n + 1) (g r)) v))
      rw [map_mul, map_mul, Module.End.mul_apply]
    rw [he]
    refine hpI.map' _ (LinearMap.ker_eq_bot.mpr (LinearMap.dualMap_injective_of_surjective ?_))
    intro v
    refine ⟨π (E F (n + 1) (g r))⁻¹ v, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hN : ((Fintype.card F : ℂ) ^ (n + 1)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
  have horth : ∀ r s : R, ∑ x : Fin (n + 1) → F, (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) r x *
      (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x))) s x = if r = s then (Fintype.card F : ℂ) ^ (n + 1) else 0 := by
    intro r s
    rw [hO F (n + 1) ψ₀ hψ r.1 s.1]
    exact if_congr Subtype.val_inj rfl rfl
  have hind := hS (Module.Dual ℂ V) (Fin (n + 1) → F) R (Fin (D F (n + 1)))
    (fun x => (π (col x)).dualMap) (fun (r : R) x => ψ₀ (r.1 ⬝ᵥ x)) (fun (s : R) x => ψ₀ (-(s.1 ⬝ᵥ x)))
    _ hN (fun r s => by convert horth r s) f hf hblock
  have hcard : Fintype.card (Fin (D F (n + 1 + 1))) = Fintype.card (R × Fin (D F (n + 1))) := by
    rw [Fintype.card_fin, Fintype.card_prod, card_nonzero, Fintype.card_fin, D, D,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1), mul_comm]
  let e : Fin (D F (n + 1 + 1)) ≃ R × Fin (D F (n + 1)) := Fintype.equivOfCardEq hcard
  refine ⟨fun k => E F (n + 1) (A (e k)), fun k => lastRowE_E _, ?_⟩
  exact hind.comp e e.injective
end PI.GGMirBoundW
