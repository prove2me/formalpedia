-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ProdUnitInert.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:16:47.182214+00:00
-- url     : https://prove2.me/submissions/045fd832-08f6-4692-9507-cafaa8aebe3e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdUnitInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_NatCastNormLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_ExistsRatCoords
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertUnitProduct_MemQbar
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_mem_Qbar
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_conic_of_norm_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_exists_rat_coords
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_norm_conic_eq_one
import Theorems.Thm_PI_UnitaryGroupMassFormula_ProdUnitInert_prod_emb_eq_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ProdUnitInert
open PI.ProdUnitInert
namespace PI.UnitaryGroupMassFormula.ProdUnitInert
theorem _root_.solution : PI.ProdUnitInert := by
  intro E _ _ K c φ₀ S _ emb hinj hagree hcard hc hK d p _ b hb hjac lam z hz
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h0 : jacobiSym 0 p = 0 := jacobiSym.zero_left (Fact.out : p.Prime).one_lt
    simp [h0] at hjac
  have hns : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p)) :=
    (legendreSym.eq_neg_one_iff (p := p)).mp (by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hjac)
  have hP := prod_emb_eq_norm K φ₀ S emb hinj hagree hcard z
  obtain ⟨x, y, hw⟩ := exists_rat_coords K hK d hd0 b hb (Algebra.norm K z)
  have hβ : (φ₀ (b : E)) ^ 2 = -(d : ℂ) := by
    have h := congrArg (fun t : K => φ₀ (t : E)) hb
    simpa using h
  have hPxy : ∏ s, emb s z = (x : ℂ) + y * φ₀ (b : E) := by
    rw [hP, hw]
    simp
  have hPP : (∏ s, emb s z) * (starRingEnd ℂ) (∏ s, emb s z) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun s _ => by rw [← hc, ← map_mul, hz, map_one])
  rw [hPxy] at hPP
  have hconic := conic_of_norm_one d _ hβ x y hPP
  have hβmem : φ₀ (b : E) ∈ Qbar := mem_Qbar φ₀ _
  have hPmem : (∏ s, emb s z) ∈ Qbar := by rw [hP]; exact mem_Qbar φ₀ _
  unfold PI.ProdUnitInert.lamC
  rw [dif_pos hPmem]
  have hsub : (⟨∏ s, emb s z, hPmem⟩ : Qbar) = (x : Qbar) + (y : Qbar) * ⟨φ₀ (b : E), hβmem⟩ := by
    apply Subtype.ext
    simp [hPxy]
  rw [hsub, map_add, map_mul, map_ratCast, map_ratCast]
  apply norm_conic_eq_one d hns x y hconic
  have hsq : (⟨φ₀ (b : E), hβmem⟩ : Qbar) ^ 2 = -(d : Qbar) := by
    apply Subtype.ext
    simp [hβ]
  rw [← map_pow, hsq, map_neg, map_natCast]
end PI.UnitaryGroupMassFormula.ProdUnitInert
