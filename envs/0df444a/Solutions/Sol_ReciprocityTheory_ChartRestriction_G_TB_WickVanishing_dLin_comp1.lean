-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.dLin_comp1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:39.504302+00:00
-- url     : https://prove2.me/submissions/e63e7a7a-24eb-4944-b6ac-39938ae10701

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_single_point_family
import Theorems.Thm_Formalism_FG_SolveVAux_degree_eq_one
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
open Formalism.FG.SolveVAux
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {d : ℕ} (φ ψ : Pt k 1 d) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  classical
  refine Matrix.ext fun i j => ?_
  simp only [dLin, Matrix.mul_apply]
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![ψ] (φ i)) = _
  unfold ev
  rw [subst_single_point_family]
  have hs : HasSubst (fun p : Fin 1 × Fin d => ψ p.2) := hasSubst_of_constantCoeff_zero fun p => hψ p.2
  have hlow : ∀ p : Fin 1 × Fin d, Low 1 (ψ p.2) := fun p => (low_one_iff _).2 (hψ p.2)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _
    (s := Finset.univ.image (fun p : Fin 1 × Fin d => Finsupp.single p 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h), Fintype.sum_prod_type,
      Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun j' _ => ?_
    dsimp only
    rw [Finsupp.prod_single_index (h := fun (s : Fin 1 × Fin d) (e : ℕ) => ψ s.2 ^ e) (pow_zero _), pow_one,
      smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single ((0 : Fin 1), j) 1) (e.prod fun s n => (fun p : Fin 1 × Fin d => ψ p.2) s ^ n) =
        0 := by
      rcases Nat.lt_or_ge e.degree 2 with hd | hd
      · rcases Nat.lt_or_ge e.degree 1 with hd1 | hd1
        · have he0 : e = 0 := by
            have : e.degree = 0 := by omega
            exact (Finsupp.degree_eq_zero_iff e).1 this
          rw [he0, Finsupp.prod_zero_index, coeff_one, if_neg]
          exact Finsupp.single_ne_zero.2 one_ne_zero
        · obtain ⟨p, rfl⟩ := degree_eq_one e (by omega)
          exact absurd (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ p))) hne
      · have hl := low_P hlow e
        exact hl _ (by rw [Finsupp.degree_single]; omega)
    rw [hz, smul_zero]
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
