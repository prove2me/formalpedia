-- Prove2me | solution 1 for PIW.AdelClassFin.stH_of_hl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:30.891213+00:00
-- url     : https://prove2.me/submissions/f417ca1b-a637-41db-b798-f40d7b3068a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
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
theorem _root_.solution (hHL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ m, HL E m) : StH := by
  intro F E _ _ _ _ _ _ hc n J hJ hdet
  classical
  obtain ⟨T0, hT0, hcl⟩ := hHL F E hc n 1 le_rfl
  let pick : Matrix (Fin n) (Fin n) E × Submodule (𝓞 E) (Fin n → E) → Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E := fun q =>
    if h : ∃ M : Submodule (𝓞 E) (Fin n → E), ∃ A : GL (Fin n) E,
        cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E) = q.1 ∧ IsImg A q.2 M then
      (Classical.choose h, Classical.choose (Classical.choose_spec h)) else (⊥, 1)
  have hpick : ∀ q : Matrix (Fin n) (Fin n) E × Submodule (𝓞 E) (Fin n → E), (∃ M : Submodule (𝓞 E) (Fin n → E), ∃ A : GL (Fin n) E,
      cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E) = q.1 ∧ IsImg A q.2 M) →
      cT (starRingEnd E) ((pick q).2 : Matrix (Fin n) (Fin n) E) * J * ((pick q).2 : Matrix (Fin n) (Fin n) E) = q.1 ∧
        IsImg (pick q).2 q.2 (pick q).1 := by
    intro q h
    show cT (starRingEnd E) ((dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).2 : Matrix (Fin n) (Fin n) E) * J *
        ((dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).2 : Matrix (Fin n) (Fin n) E) = q.1 ∧
      IsImg (dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).2 q.2 (dite _ _ _ : Submodule (𝓞 E) (Fin n → E) × GL (Fin n) E).1
    rw [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec h)
  refine ⟨(hT0.image (fun q => (pick q).1)).toFinset, fun M hfg hspan hsd => ?_⟩
  have hLat : (J, M) ∈ Lat E n 1 := by
    simp only [Lat, Set.mem_setOf_eq]
    refine ⟨hJ, hdet, hfg, hspan, fun x hx y hy => (hsd y).1 hy x hx, fun w hw => ?_⟩
    rw [Nat.cast_one, one_smul]
    exact (hsd w).2 hw
  obtain ⟨q, hq, A, hA1, hA2⟩ := hcl (J, M) hLat
  dsimp only at hA1 hA2
  obtain ⟨hq1, hq2⟩ := hpick q ⟨M, A, hA1, hA2⟩
  have key : cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E) =
      cT (starRingEnd E) ((pick q).2 : Matrix (Fin n) (Fin n) E) * J * ((pick q).2 : Matrix (Fin n) (Fin n) E) := hA1.trans hq1.symm
  refine ⟨A * (pick q).2⁻¹, ?_, (pick q).1, ?_, ?_⟩
  · show cT (starRingEnd E) ((A * (pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * J *
      ((A * (pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = J
    rw [Units.val_mul, cT_mul]
    calc cT (starRingEnd E) (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J *
          ((A : Matrix (Fin n) (Fin n) E) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E))
        = cT (starRingEnd E) (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            (cT (starRingEnd E) (A : Matrix (Fin n) (Fin n) E) * J * (A : Matrix (Fin n) (Fin n) E)) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
          simp only [Matrix.mul_assoc]
      _ = cT (starRingEnd E) (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
            (cT (starRingEnd E) ((pick q).2 : Matrix (Fin n) (Fin n) E) * J * ((pick q).2 : Matrix (Fin n) (Fin n) E)) *
            (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by rw [key]
      _ = cT (starRingEnd E) (((pick q).2 : Matrix (Fin n) (Fin n) E) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) * J *
            (((pick q).2 : Matrix (Fin n) (Fin n) E) * (((pick q).2⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) := by
          rw [cT_mul]
          simp only [Matrix.mul_assoc]
      _ = J := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]
  · exact (Set.Finite.mem_toFinset _).mpr ⟨q, hq, rfl⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨w0, hw0, rfl⟩ := (hA2 v).1 hv
      refine ⟨((pick q).2 : Matrix (Fin n) (Fin n) E) *ᵥ w0, (hq2 _).2 ⟨w0, hw0, rfl⟩, ?_⟩
      rw [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul (pick q).2⁻¹,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨w0, hw0, rfl⟩ := (hq2 w).1 hw
      refine (hA2 _).2 ⟨w0, hw0, ?_⟩
      rw [Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Units.val_mul (pick q).2⁻¹,
        inv_mul_cancel, Units.val_one, Matrix.mul_one]
end PIW.AdelClassFin
