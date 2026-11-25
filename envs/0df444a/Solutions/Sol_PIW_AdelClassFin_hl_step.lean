-- Prove2me | solution 1 for PIW.AdelClassFin.hl_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:46.460232+00:00
-- url     : https://prove2.me/submissions/a81ddb02-5c01-4188-b545-2686be384f2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Theorems.Thm_PIW_AdelClassFin_FinCl_mono
import Theorems.Thm_PIW_AdelClassFin_FinCl_union
import Theorems.Thm_PIW_AdelClassFin_hform_smul
import Theorems.Thm_PIW_AdelClassFin_hform_self_star
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



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (m : ℕ) (hm : 1 ≤ m) (ih : ∀ k < m, HL E k) : HL E m := by
  intro d hd
  obtain ⟨C, hC⟩ := hS F E hc m d hm hd
  obtain ⟨R, hR, hR0, hRu⟩ := hU F E hc C
  obtain ⟨G2, hG2, hG2det, hiso⟩ := hI F E hc m d hd
  have hG1 : ((fun r : E => Matrix.of fun (_ _ : Fin 1) => r) '' R).Finite := hR.image _
  have hG1det : ∀ Γ ∈ (fun r : E => Matrix.of fun (_ _ : Fin 1) => r) '' R, Γ.det ≠ 0 := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Matrix.det_unique]
    show r ≠ 0
    rintro rfl
    exact hR0 hr
  refine FinCl.mono (FinCl.union (hP F E hc m 1 le_rfl ih d hd _ hG1 hG1det)
    (hP F E hc m 2 (by norm_num) ih d hd G2 hG2 hG2det)) ?_
  intro p hp
  obtain ⟨x, hx, hx0, hxC⟩ := hC p hp
  by_cases hiso0 : hform (starRingEnd E) p.1 x x = 0
  · refine Or.inr ?_
    simp only [SplitSet, Set.mem_setOf_eq]
    exact ⟨hp, hiso p hp x hx hx0 hiso0⟩
  · refine Or.inl ?_
    have hint : hform (starRingEnd E) p.1 x x ∈ (algebraMap (𝓞 E) E).range := hp.2.2.2.2.1 x hx x hx
    obtain ⟨u, r, hr, hur⟩ := hRu _ hint (hform_self_star p.1 hp.1 x) hiso0 hxC
    set c : E := algebraMap (𝓞 E) E ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) with hcdef
    have hca : c * algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
      rw [hcdef, ← map_mul, Units.inv_mul, map_one]
    have hsca : star c * star (algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E)) = 1 := by
      rw [← star_mul', hca, star_one]
    simp only [SplitSet, Set.mem_setOf_eq]
    refine ⟨hp, fun _ => c • x, fun _ => ?_, ⟨r, hr, ?_⟩⟩
    · show c • x ∈ p.2
      rw [hcdef, algebraMap_smul]
      exact p.2.smul_mem _ hx
    · ext i j
      simp only [gram, Matrix.of_apply]
      rw [hform_smul, hur]
      rw [show star c * c * (star (algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E)) *
          algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E) * r) =
          (star c * star (algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E))) *
          (c * algebraMap (𝓞 E) E ((u : (𝓞 E)ˣ) : 𝓞 E)) * r by ring, hsca, hca, one_mul, one_mul]
end PIW.AdelClassFin
