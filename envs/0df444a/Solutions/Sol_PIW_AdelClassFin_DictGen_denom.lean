-- Prove2me | solution 1 for PIW.AdelClassFin.DictGen.denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:47.471009+00:00
-- url     : https://prove2.me/submissions/97059e8a-baf5-42b8-b55f-92a8a7ff211a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_natSmul_mem
import Theorems.Thm_PIW_AdelClassFin_DictGen_mulVec_mem_of_le
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace DictGen
variable (I : AutInst)
private theorem smul_mulVec_lemma {A : Type} [CommRing A] {n : ℕ} (c : A)
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) : (c • M) *ᵥ y = c • (M *ᵥ y) := by
  first
    | exact Matrix.smul_mulVec c M y
    | exact Matrix.smul_mulVec_assoc c M y
    | (ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc])
end DictGen
end PIW.AdelClassFin
end
end

set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
open PIW.AdelClassFin.DictGen
variable (I : AutInst)
namespace PIW.AdelClassFin.DictGen
theorem _root_.solution (hD : LDenom) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y ∈ I.Lf, (N : I.E ⊗[I.F] Af I.F) • (M *ᵥ y) ∈ I.Lf := by
  classical
  obtain ⟨s, hs⟩ := I.L_fg
  choose m hm0 hm using fun v : Fin I.n → I.E => hD I (M *ᵥ iv I v)
  refine ⟨∏ j ∈ s, m j, Finset.prod_pos fun j _ => hm0 j, ?_⟩
  have hle : I.L ≤ lamM I (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) := by
    rw [← hs, Submodule.span_le]
    intro v hv
    show (((∏ j ∈ s, m j : ℕ) : (I.E ⊗[I.F] Af I.F)) • M) *ᵥ iv I v ∈ I.Lf
    rw [smul_mulVec_lemma, ← Finset.prod_erase_mul s m hv, Nat.cast_mul, mul_smul]
    exact natSmul_mem I _ (hm v)
  intro y hy
  have h2 := mulVec_mem_of_le I hle y hy
  rwa [smul_mulVec_lemma] at h2
end PIW.AdelClassFin.DictGen
