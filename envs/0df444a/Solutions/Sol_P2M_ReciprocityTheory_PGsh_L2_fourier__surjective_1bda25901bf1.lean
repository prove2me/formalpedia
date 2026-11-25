-- Prove2me | solution 1 for P2M_ReciprocityTheory_PGsh_L2_fourier__surjective_1bda25901bf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:42.294962+00:00
-- url     : https://prove2.me/submissions/fa40589a-9be4-4a79-bd17-9549d9d822c3

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_tableM_isUnit
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (σ : H ≃ N) (f : N → C) :
    ∃ w, fourier (R := R) (fun a h => e h a) w = f := by
  have hM := tableM_isUnit e σ
  refine ⟨fun h => ((tableM e σ)⁻¹ *ᵥ f) (σ h), ?_⟩
  funext a
  simp only [fourier_apply']
  calc ∑ x, ((tableM e σ)⁻¹ *ᵥ f) (σ x) * e x a
      = ∑ j, tableM e σ a j * ((tableM e σ)⁻¹ *ᵥ f) j :=
        Fintype.sum_equiv σ _ _ fun x => by
          simp only [tableM, Matrix.of_apply, Equiv.symm_apply_apply]
          ring
    _ = (tableM e σ *ᵥ ((tableM e σ)⁻¹ *ᵥ f)) a := rfl
    _ = f a := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
end ReciprocityTheory.PGsh.L2
