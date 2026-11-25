-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HeightAsIntersection_proof_9d47be4786fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:53.62904+00:00
-- url     : https://prove2.me/submissions/d2a33677-c36e-438c-9ede-d118886b0e21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_mul_d6ec3c0c69a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermLine_toGeo_mul_7fcfddae2adf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HeightAsIntersection
theorem _root_.solution (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement) : HeightAsIntersection.Statement := by
  intro ι _ _ _ n II hII A x hx
  obtain ⟨-, hAdd, hR⟩ := hII
  have hW : Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) (0 + 1) := h₁ ι n x hx
  have hdeg : (0 : ℝ) < Geo.degC (ι := blockIdx n) (orbitIdeal x) := by
    exact_mod_cast h₂ ι n x hx
  obtain ⟨c, hc⟩ := exists_chart hx
  have hsnoc : ∀ B : Geo.HermLine (blockIdx n),
      (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) B : Fin 1 → _) = ![B] := by
    intro B
    funext i
    fin_cases i
    rfl
  have hL : ∀ j : Fin 0, Geo.IsSmoothHerm ((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j) :=
    fun j ↦ j.elim0
  have key : ∀ (B : HermLine n) (d : ι → ℕ), (∀ k, B.deg k = d k) →
      II (orbitIdeal x) 1 ![B.toGeo] = Geo.degC (ι := blockIdx n) (orbitIdeal x) * height B x := by
    intro B d hd
    have h := hR (orbitIdeal x) 0 Fin.elim0 B.toGeo (chartMonomial c d) d hW hL
      B.isSmoothHerm_toGeo hd ((geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d))
      (chartMonomial_notMem_orbitIdeal x c hc d)
    rw [hsnoc] at h
    exact h.trans (h₃ ι n II B x _ hx (isSectionOn_chartMonomial B x c hc d hd))
  let m : ι → ℕ := fun k ↦ (A.deg k).natAbs
  have hB := key (HermLine.standardPow m) m fun k ↦ rfl
  have hAB := key (A.mul (HermLine.standardPow m)) (fun k ↦ (A.deg k + m k).toNat) fun k ↦ by
    simp only [HermLine.mul, HermLine.standardPow, Pi.add_apply, m]
    omega
  have hadd := hAdd (orbitIdeal x) 0 Fin.elim0 A.toGeo (HermLine.standardPow m).toGeo hW hL
    A.isSmoothHerm_toGeo (HermLine.standardPow m).isSmoothHerm_toGeo
  rw [hsnoc, hsnoc, hsnoc, ← HermLine.toGeo_mul] at hadd
  have hadd' : II (orbitIdeal x) 1 ![(A.mul (HermLine.standardPow m)).toGeo] =
      II (orbitIdeal x) 1 ![A.toGeo] + II (orbitIdeal x) 1 ![(HermLine.standardPow m).toGeo] :=
    hadd
  rw [hAB, hB, height_mul A _ hx] at hadd'
  rw [eq_div_iff hdeg.ne']
  linarith
end HeightAsIntersection
end GroundTheory.Heights₂.Heights
