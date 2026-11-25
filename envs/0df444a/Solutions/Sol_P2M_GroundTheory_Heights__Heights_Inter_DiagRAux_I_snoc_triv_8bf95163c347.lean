-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_I_snoc_triv_8bf95163c347
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:12.458797+00:00
-- url     : https://prove2.me/submissions/21168270-1677-42d0-83cb-78fc3d5b4efd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_congr_mcPts_6069163e8079
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_ptsIntegral_zero_8b7095af3bb6

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι} (hP : IsArithVar P (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A) (ha : A.a = 0) (h1 : ∀ z ∈ mcPts P, A.h z = 1) :
    I P (n + 1) (Fin.snoc L A) = 0 := by
  have hhom : IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  rw [hI.2.2 P n L A 1 0 hP hL hA (fun k => by simp [ha]) hhom hnot]
  have hsupp : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    refine ⟨fun hW => ?_, fun h => h.elim⟩
    have h1 : P ⊔ Ideal.span {(1 : MRing ι)} = ⊤ := by simp
    have hp : W.IsPrime := hW.1.1.1
    have hle : P ⊔ Ideal.span {(1 : MRing ι)} ≤ W := hW.1.1.2
    rw [h1] at hle
    exact hp.ne_top (top_le_iff.1 hle)
  unfold recR arInt
  simp only [hsupp, finsum_mem_empty, zero_sub, neg_eq_zero]
  rw [ptsIntegral_congr_mcPts P (φ' := fun j z => Real.log ((L j).h z)) (g' := fun _ => 0)
    (fun _ _ _ => rfl) (fun z hz => by simp [logNorm, h1 z hz])]
  exact ptsIntegral_zero P _
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
