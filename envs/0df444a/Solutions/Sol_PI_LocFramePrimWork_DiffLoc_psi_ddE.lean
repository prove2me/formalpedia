-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_psi_ddE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:03.049475+00:00
-- url     : https://prove2.me/submissions/f3ad085c-f2c6-403d-8489-7c0cb43daa6c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_mul_mem
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_span_le
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_frac_closed
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_range_closed
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_isDiffVal
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_sc_eq
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_sc_mul
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_inclR_alg
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_ddE_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution :
    DiffLoc_psi v ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} * DiffLoc_P (E := E) v := by
  obtain ⟨hδ, hle, d0, hd0mem, heq⟩ := DiffLoc_isDiffVal v
  have hvδ : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 hδ
  apply le_antisymm
  · rw [DiffLoc_ddE_eq]
    apply DiffLoc_span_le
    · intro o y hy
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_span_singleton_mul.1 hy
      rw [mul_left_comm]
      exact Submodule.mem_span_singleton_mul.2 ⟨_, DiffLoc_psi_mul_mem v _ DiffLoc_range_closed hp o, rfl⟩
    · rintro _ ⟨d, hd, rfl⟩
      show inclR (F := F) (Fv F v) (algebraMap F E (d : F)) ∈ _
      set t := algebraMap F (Fv F v) (d : F) * (dV v)⁻¹ with ht_def
      have ht : t ∈ v.adicCompletionIntegers F := by
        show Valued.v t ≤ 1
        rw [ht_def, map_mul, map_inv₀]
        calc Valued.v (algebraMap F (Fv F v) (d : F)) * (Valued.v (dV v))⁻¹
            ≤ Valued.v (dV v) * (Valued.v (dV v))⁻¹ := mul_le_mul_left (hle d hd) _
          _ = 1 := mul_inv_cancel₀ hvδ
      have hsplit : algebraMap F (Fv F v) (d : F) = dV v * t := by
        rw [ht_def, mul_comm (algebraMap F (Fv F v) (d : F)), ← mul_assoc, mul_inv_cancel₀ hδ, one_mul]
      have h1 : inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) = 1 := by simp
      have htP : sc (E := E) v t ∈ DiffLoc_P (E := E) v := by
        have : sc (E := E) v t =
            (⟨t, ht⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) ((1 : 𝓞 E) : E) := by
          rw [h1]; exact Algebra.algebraMap_eq_smul_one t
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨1, rfl⟩, rfl⟩)
      rw [DiffLoc_inclR_alg, hsplit, DiffLoc_sc_mul]
      exact Submodule.mem_span_singleton_mul.2 ⟨_, htP, rfl⟩
  · refine Submodule.mul_le.2 (fun m hm p hp => ?_)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hm
    rw [smul_mul_assoc]
    refine Submodule.smul_mem _ a ?_
    have hd0v : Valued.v (algebraMap F (Fv F v) (d0 : F)) ≠ 0 := heq ▸ hvδ
    have hd0 : algebraMap F (Fv F v) (d0 : F) ≠ 0 := (Valuation.ne_zero_iff _).1 hd0v
    set u := dV v * (algebraMap F (Fv F v) (d0 : F))⁻¹ with hu_def
    have hu : u ∈ v.adicCompletionIntegers F := by
      show Valued.v u ≤ 1
      rw [hu_def, map_mul, map_inv₀, ← heq, mul_inv_cancel₀ hd0v]
    have hmemδ : sc (E := E) v (dV v) ∈
        DiffLoc_psi v ((ddE (E := E) F : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
      have h1 : sc (E := E) v (dV v) =
          (⟨u, hu⟩ : v.adicCompletionIntegers F) • inclR (F := F) (Fv F v) (algebraMap F E (d0 : F)) := by
        rw [DiffLoc_inclR_alg]
        show sc (E := E) v (dV v) = u • sc (E := E) v (algebraMap F (Fv F v) (d0 : F))
        rw [Algebra.smul_def, ← DiffLoc_sc_eq, ← DiffLoc_sc_mul, hu_def, mul_assoc, inv_mul_cancel₀ hd0,
          mul_one]
      rw [h1]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [DiffLoc_ddE_eq]
      exact Submodule.subset_span ⟨d0, hd0mem, rfl⟩
    unfold DiffLoc_P DiffLoc_psi at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨_, ⟨o, rfl⟩, rfl⟩ := hx
      rw [mul_comm]
      exact DiffLoc_psi_mul_mem v _ (DiffLoc_frac_closed (ddE F)) hmemδ o
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul t x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ t hx
end PI.LocFramePrimWork
