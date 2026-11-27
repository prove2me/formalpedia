-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_proof_c1792c9c7dad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:24.12635+00:00
-- url     : https://prove2.me/submissions/fe005843-b652-4e1b-8792-fb9110f273f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue___apply_01e9e3406336
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocResidue_inv_mem_df30a667553b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
set_option synthInstance.maxHeartbeats 400000
open GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
variable {F : Type u} [Field F] {K : Type} [DecidableEq K] {ι : K → Type}
local notation "fr" Q:max h:max =>
  algebraMap (_ ⧸ Q) (FractionRing (_ ⧸ Q)) (Ideal.Quotient.mk Q h)
variable {P W : Ideal (MRing ι F)} [P.IsPrime] [W.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
theorem _root_.solution : DegZeroLocResidue.Statement := by
  intro F _ K _ ι P _ W _ hPW
  refine ⟨ρ hPW, fun x b f g _ _ hg hx => res_eq hPW hg hx, fun x => ⟨?_, ?_⟩, fun z => ⟨?_, ?_⟩⟩
  · rintro h0 ⟨y, hy, hxy⟩
    have h1 : ρ hPW (x * ⟨y, hy⟩) = 1 := by rw [show x * ⟨y, hy⟩ = 1 from Subtype.ext hxy, map_one]
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro hn
    by_contra h0
    obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
    rw [ρ_apply, res_eq hPW hgW hx] at h0
    have hfW : f ∉ W := fun h => h0 (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_div])
    refine hn ⟨_, inv_mem hPW hf hg hfW, ?_⟩
    rw [hx, div_mul_div_comm, mul_comm (fr P f), div_self (mul_ne_zero
      (fr_ne_zero P fun h => hgW (hPW h)) (fr_ne_zero P fun h => hfW (hPW h)))]
  · intro hz
    let E : IntermediateField F (FractionRing (MRing ι F ⧸ W)) :=
      { carrier := Set.range (ρ hPW)
        mul_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩
        add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add _ _ _⟩
        one_mem' := ⟨1, map_one _⟩
        zero_mem' := ⟨0, map_zero _⟩
        algebraMap_mem' := fun c => ⟨algebraMap F _ c, by
          rw [ρ_apply, res_eq hPW (f := C c) (g := 1) ((Ideal.ne_top_iff_one W).mp
            Ideal.IsPrime.ne_top') (by
              show algebraMap F (FractionRing (MRing ι F ⧸ P)) c = _
              rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P),
                ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq])]
          rw [map_one, map_one, div_one, IsScalarTower.algebraMap_apply F (MRing ι F ⧸ W),
            ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]⟩
        inv_mem' := by
          rintro _ ⟨x, rfl⟩
          by_cases h0 : ρ hPW x = 0
          · rw [h0, inv_zero]; exact ⟨0, map_zero _⟩
          obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
          rw [ρ_apply, res_eq hPW hgW hx] at h0 ⊢
          have hfW : f ∉ W := fun h => h0 (by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_div])
          exact ⟨⟨_, inv_mem hPW hf hg hfW⟩, by rw [ρ_apply, res_eq hPW hfW rfl, inv_div]⟩ }
    have hle : homFracDegZero W ≤ E := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
      exact ⟨⟨_, div_mem_degZeroLoc P {W} hf hg (fun h => hgW (hPW h)) (by rintro _ rfl; exact hgW)⟩,
        res_eq hPW hgW rfl⟩
    exact hle hz
  · rintro ⟨x, rfl⟩
    obtain ⟨b, f, g, hf, hg, hgW, hx⟩ := exists_rep x
    rw [ρ_apply, res_eq hPW hgW hx]
    exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgW, rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.DegZeroLocResidue
