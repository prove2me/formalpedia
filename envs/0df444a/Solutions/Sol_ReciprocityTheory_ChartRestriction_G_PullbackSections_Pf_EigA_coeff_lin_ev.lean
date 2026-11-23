-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.coeff_lin_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:54.266407+00:00
-- url     : https://prove2.me/submissions/2457c310-bb54-4fbc-8526-8f0a5f55f016

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EigenLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {R : Type} [CommRing R] {d : ℕ}
open Formalism.FG.SolveVAux
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d)
    (q : Fin n × Fin d) :
    coeff (Finsupp.single q 1) (ev a f) =
      ∑ p : Fin m × Fin d, coeff (Finsupp.single p 1) f * coeff (Finsupp.single q 1) (a p.1 p.2) := by
  classical
  unfold ev
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2
  have hlow : ∀ p : Fin m × Fin d, Low 1 (a p.1 p.2) := fun p => (low_one_iff _).2 (ha p.1 p.2)
  rw [coeff_subst hs, finsum_eq_sum_of_support_subset _
    (s := Finset.univ.image (fun p : Fin m × Fin d => Finsupp.single p 1))]
  · rw [Finset.sum_image (fun p _ q _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun p _ => ?_
    dsimp only
    rw [Finsupp.prod_single_index (h := fun (s : Fin m × Fin d) (e : ℕ) => a s.1 s.2 ^ e) (pow_zero _), pow_one,
      smul_eq_mul]
  · intro e he
    rw [Function.mem_support] at he
    by_contra hne
    apply he
    have hz : coeff (Finsupp.single q 1) (e.prod fun s n => (fun p : Fin m × Fin d => a p.1 p.2) s ^ n) = 0 := by
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
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
