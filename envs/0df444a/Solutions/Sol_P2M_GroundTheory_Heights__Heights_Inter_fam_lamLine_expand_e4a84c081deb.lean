-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_fam_lamLine_expand_e4a84c081deb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:51.014101+00:00
-- url     : https://prove2.me/submissions/6469eafd-8425-4f90-9372-42749e5c5e77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_SymExp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_basis_49b303483717
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_famExt_symm_a3acaa354a3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_eq_famExt_551d8170ff5e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_symm_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {A X : HermLine ι}
    (hA : IsSmoothHerm A) (hX : IsSmoothHerm X) (c : ℤ) :
    I P (n + 1) (fun _ => lamLine A X c) =
      2 ^ (n + 1) * ∑ j ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose j : ℝ) * (-(c : ℝ) / 2) ^ j * I P (n + 1) (mix j X A) := by
  have hsm : ∀ i, IsSmoothHerm (![X, A] i) := Fin.forall_fin_two.mpr ⟨hX, hA⟩
  have h := fam_eq_famExt hI hP hA hX c Finset.univ (fun _ => 0)
  simp only [Finset.mem_univ, if_true] at h
  rw [h]
  have hw : (fun _ : Fin (n + 1) => (![-(c : ℝ), 2] : Fin 2 → ℝ)) =
      fun _ => (2 : ℝ) • ((Pi.single 1 1 : Fin 2 → ℝ) + (-(c : ℝ) / 2) • Pi.single 0 1) := by
    funext i k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      simp
      ring
    · simp
  rw [hw, MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    symm_expand _ (famExt_symm hI hP ![X, A] hsm)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hm : (mix j (Pi.single 0 1) (Pi.single 1 1) : Fin (n + 1) → Fin 2 → ℝ) =
      fun i => Pi.single ((fun i : Fin (n + 1) => if (i : ℕ) < j then (0 : Fin 2) else 1) i) 1 := by
    funext i
    simp only [mix]
    split_ifs <;> rfl
  rw [hm, famExt_basis]
  congr 2
  funext i
  simp only [mix, Function.comp]
  split_ifs <;> rfl
end GroundTheory.Heights₂.Heights.Inter
