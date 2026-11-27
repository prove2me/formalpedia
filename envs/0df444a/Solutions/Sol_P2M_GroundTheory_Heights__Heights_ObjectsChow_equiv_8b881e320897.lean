-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_equiv_8b881e320897
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:34.582577+00:00
-- url     : https://prove2.me/submissions/4019d727-4785-4328-af36-408e303668b8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_IsMultiHomogOfIsChowForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_rename_linForm_a19ea48e2376
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_linForm_mem_finIdeal_f754094b0af3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_specFirst_eq_27ac14c10d3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_map_specFirst_60810c1809b7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_iff_0f52654b96e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isMultiHomog_of_isChowForm_129f76209172
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isRelevant_finIdeal_iff_f29f08675567
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowFormCycle_iff_a7991db0b825
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_isChowForm_C_mul_941588753c43
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_chowDegree_eq_573b7e6f4160

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc IsMultihomog)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow
theorem _root_.solution :
    (∀ (n : ℕ) (u : Fin n → ℤ), rename (blk n) (linForm u) = IndefiniteRowSideFullHecke.ArithBezout.linForm u) ∧
    (∀ (n : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
      linForm u ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P ↔ IndefiniteRowSideFullHecke.ArithBezout.linForm u ∈ P) ∧
    (∀ (R : Type) [CommRing R] (n e : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R)
      (u : Fin n → R), specFirst f u = IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) ∧
    (∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (n e : ℕ)
      (f : MvPolynomial (Fin (e + 1) × Fin n) R) (u : Fin n → R),
      map φ (IndefiniteRowSideFullHecke.ArithBezout.specFirst u f) = IndefiniteRowSideFullHecke.ArithBezout.specFirst (φ ∘ u) (map φ f)) ∧
    (∀ (R : Type) [CommSemiring R] (n e δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) R),
      IsMultiHomog δ f ↔ IsMultihomog f δ) ∧
    (∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f) → IsMultiHomog δ f) ∧
    (∀ (n : ℕ) (W : Ideal (MRing (PBlk n))),
      IsRelevant (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (Z : ProjCycle F n) (f : MvPolynomial (Fin k × Fin n) F),
      IsChowFormCycle Z k f ↔ ∃ c : F, c ≠ 0 ∧
        ∃ g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F,
          (∀ W ∈ Z.support, IsChowForm W k (g W)) ∧ f = C c * IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z g) ∧
    (∀ (F : Type) [Field F] (n k : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F) (c : F),
      IsChowForm I k f → c ≠ 0 → IsChowForm I k (C c * f)) ∧
    (∀ (F : Type) [Field F] (n k δ : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
      (f : MvPolynomial (Fin k × Fin n) F),
      0 < k → IsChowForm I k f → IsMultiHomog δ f → chowDegree I k = δ) :=
  ⟨fun _ => rename_linForm, fun _ => linForm_mem_finIdeal, fun _ _ _ _ => specFirst_eq,
    fun _ _ _ _ φ _ _ => map_specFirst φ, fun _ _ _ _ _ => isMultiHomog_iff,
    fun _ _ _ _ _ => isMultiHomog_of_isChowForm, fun _ => isRelevant_finIdeal_iff,
    fun _ _ _ _ => isChowFormCycle_iff, fun _ _ _ _ _ _ _ hf hc => isChowForm_C_mul hf hc,
    fun _ _ _ _ _ _ _ hk hf hδ => chowDegree_eq hk hf hδ⟩
end GroundTheory.Heights₂.Heights.ObjectsChow
