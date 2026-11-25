-- Prove2me | solution 1 for PI.LocLatEq.W.core_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:14.07798+00:00
-- url     : https://prove2.me/submissions/5a5ebe26-00fe-4ff0-b924-053d2a0c3ca2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_CoreGenIdeal
import Theorems.Thm_PI_LocLatEq_W_core_gen_ideal
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.LocLatEq.W
theorem _root_.solution (hA : AvoidP) (p : HeightOneSpectrum (𝓞 F)) (I : Submodule (𝓞 E) E)
    (hI : I.FG) : ∃ a ∈ I, ∀ b ∈ I, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ ∃ r : 𝓞 E,
      algebraMap (𝓞 F) (𝓞 E) d • b = r • a := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) S
  have hc0 : algebraMap (𝓞 E) E (c : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero c)
  have hint : ∀ x ∈ Submodule.span (𝓞 E) (S : Set E),
      ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (c : 𝓞 E) • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hc x hx
      exact ⟨y, hy⟩
    | zero => exact ⟨0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨y1, h1⟩ := hx
      obtain ⟨y2, h2⟩ := hz
      exact ⟨y1 + y2, by rw [map_add, h1, h2, smul_add]⟩
    | smul r x _ hx =>
      obtain ⟨y, h⟩ := hx
      refine ⟨r * y, ?_⟩
      rw [map_mul, h]
      simp only [Algebra.smul_def]
      ring
  obtain ⟨a0, ha0, hgen⟩ := core_gen_ideal (F := F) hA p
    ((Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹))
  rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply] at ha0
  refine ⟨a0 • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹, ha0, fun b hb => ?_⟩
  obtain ⟨y, hy⟩ := hint b hb
  have hyb : y • (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹ = b := by
    rw [Algebra.smul_def, hy, Algebra.smul_def, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0,
      one_mul]
  have hy𝔞 : y ∈ (Submodule.span (𝓞 E) (S : Set E)).comap
      (LinearMap.toSpanSingleton (𝓞 E) E (algebraMap (𝓞 E) E (c : 𝓞 E))⁻¹) := by
    rw [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hyb]
    exact hb
  obtain ⟨d, hd, r, hr⟩ := hgen y hy𝔞
  refine ⟨d, hd, r, ?_⟩
  rw [← hyb, smul_smul, smul_smul, hr]
end PI.LocLatEq.W
