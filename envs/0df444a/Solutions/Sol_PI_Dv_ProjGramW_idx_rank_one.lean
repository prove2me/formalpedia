-- Prove2me | solution 1 for PI.Dv.ProjGramW.idx_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:56.029449+00:00
-- url     : https://prove2.me/submissions/39e1cf40-9751-498d-a647-893838e72753

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet
import Theorems.Thm_PI_Dv_ProjGramW_idx_add
import Theorems.Thm_PI_Dv_ProjGramW_vAdd_mul
import Theorems.Thm_PI_Dv_ProjGramW_algebraMap_eq_zero
import Theorems.Thm_PI_Dv_ProjGramW_span_top_of_mem
import Theorems.Thm_PI_Dv_ProjGramW_idx_int
import Theorems.Thm_PI_Dv_ProjGramW_idxAt_antisymm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {c : K} (hc : c ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {(1 : K)}) (Submodule.span (𝓞 K) {c}) = vAdd w c := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := fun h => hb0 (algebraMap_eq_zero h)
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hc; rw [← hab, h, zero_div]
  have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
  have hα : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * c := by
    rw [← hab]; field_simp
  have h1 := idx_int hI w one_ne_zero ha0
  rw [mul_one] at h1
  have h2 := idx_int hI w hc hb0
  rw [← hα] at h2
  have hsp : ∀ z : K, z ≠ 0 → Submodule.span K ((Submodule.span (𝓞 K) {z} : Submodule (𝓞 K) K) : Set K) = ⊤ :=
    fun z hz => span_top_of_mem (Submodule.mem_span_singleton_self z) hz
  have hadd := idx_add hI w (M := Submodule.span (𝓞 K) {(1 : K)})
    (N := Submodule.span (𝓞 K) {algebraMap (𝓞 K) K a}) (P := Submodule.span (𝓞 K) {c})
    (Submodule.fg_span (Set.finite_singleton _)) (Submodule.fg_span (Set.finite_singleton _))
    (Submodule.fg_span (Set.finite_singleton _)) ((hsp 1 one_ne_zero).trans (hsp _ haK).symm)
    ((hsp c hc).trans (hsp _ haK).symm)
  rw [hadd, h1, idxAt_antisymm w (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K a}), h2, hα,
    vAdd_mul w hbK hc]
  ring
end PI.Dv.ProjGramW
