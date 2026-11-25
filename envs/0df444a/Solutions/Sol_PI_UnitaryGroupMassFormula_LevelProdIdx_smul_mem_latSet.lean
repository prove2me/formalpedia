-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LevelProdIdx.smul_mem_latSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:53:45.614704+00:00
-- url     : https://prove2.me/submissions/6d19f84b-b827-4b46-93f0-48ebd65f0dbe

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_LevelProdIdx_zero_mem_latSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_LevelProdIdx_add_mem_latSet
import Theorems.Thm_PI_UnitaryGroupMassFormula_LevelProdIdx_neg_mem_latSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LevelProdIdx
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}
variable {R : Type} [CommRing R] [Algebra F R] {O : Subring R} {k : ℕ} {G : Fin k → (Fin n → E)}
namespace PI.UnitaryGroupMassFormula.LevelProdIdx
theorem _root_.solution [NumberField E]
    (hG : ∀ i (o : 𝓞 E), ∃ z : Fin k → ℤ, ∀ l, (o : E) * G i l = ∑ j, z j • G j l)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) :
    ∀ y : Fin n → E ⊗[F] R, y ∈ latSet R O G → s • y ∈ latSet R O G := by
  induction hs using Subring.closure_induction with
  | mem x hx =>
    rintro y ⟨c, hc, rfl⟩
    rcases hx with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨d, hd⟩, rfl⟩
    · obtain ⟨o, rfl⟩ := he
      choose z hz using fun i => hG i o
      refine ⟨fun j => ∑ i, z i j • c i, fun j => sum_mem fun i _ => zsmul_mem (hc i) _, ?_⟩
      ext l
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, hz, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
      exact Finset.sum_comm
    · refine ⟨fun i => d * c i, fun i => mul_mem hd (hc i), ?_⟩
      ext l
      simp [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => intro y _; rw [zero_smul]; exact zero_mem_latSet
  | one => intro y hy; rwa [one_smul]
  | add a b _ _ ha hb => intro y hy; rw [add_smul]; exact add_mem_latSet (ha y hy) (hb y hy)
  | neg a _ ha => intro y hy; rw [neg_smul]; exact neg_mem_latSet (ha y hy)
  | mul a b _ _ ha hb => intro y hy; rw [mul_smul]; exact ha _ (hb y hy)
end PI.UnitaryGroupMassFormula.LevelProdIdx
