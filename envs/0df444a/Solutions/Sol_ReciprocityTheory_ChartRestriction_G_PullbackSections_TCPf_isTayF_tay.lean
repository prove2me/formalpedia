-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_tay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:03.201344+00:00
-- url     : https://prove2.me/submissions/3dc6c6c7-961e-4880-bd77-3a17a2e54fc3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_family

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) :
    IsTayF θ (fun p : Fin 1 × Fin g => (Pi.single p.2 1 : Fin g → ℂ)) (tay θ 0) := by
  have hc : ∀ (s : Multiset (Fin g → ℂ)) (k : Fin 1 × Fin g →₀ ℕ),
      coeff k (tay θ s) = mD θ 0 (dirs k + s) / fct k := fun _ _ => rfl
  have hd : ∀ (k : Fin 1 × Fin g →₀ ℕ) (q : Fin 1 × Fin g),
      dirs (k + Finsupp.single q 1) = (Pi.single q.2 1 : Fin g → ℂ) ::ₘ dirs k := by
    intro k q
    unfold dirs
    first
      | (rw [map_add, Finsupp.toMultiset_single, Multiset.map_add, one_nsmul, Multiset.map_singleton, add_comm,
          Multiset.singleton_add])
      | (simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_comm, Multiset.singleton_add])
      | (simp [map_add, Finsupp.toMultiset_single]; rw [add_comm, Multiset.singleton_add])
  have hf : ∀ (k : Fin 1 × Fin g →₀ ℕ) (q : Fin 1 × Fin g),
      fct (k + Finsupp.single q 1) = fct k * ((k q : ℂ) + 1) := by
    intro k q
    have h : ∀ p, (((k + Finsupp.single q 1 : Fin 1 × Fin g →₀ ℕ) p).factorial : ℂ) =
        ((k p).factorial : ℂ) * (if p = q then ((k q : ℂ) + 1) else 1) := by
      intro p
      by_cases hp : p = q
      · subst hp
        rw [if_pos rfl, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hp, Finsupp.add_apply, mul_one]
        simp [Finsupp.single_apply, Ne.symm hp]
    unfold fct
    rw [Finset.prod_congr rfl (fun p _ => h p), Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  have hf0 : ∀ k : Fin 1 × Fin g →₀ ℕ, fct k ≠ 0 := by
    intro k
    unfold fct
    exact Finset.prod_ne_zero_iff.mpr fun p _ => by exact_mod_cast Nat.factorial_ne_zero _
  refine isTayF_family θ _ (tay θ) (fun q s => ?_) (fun s => ?_)
  · ext k
    have h1 : ((k q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
    have h2 := hf0 k
    beta_reduce
    rw [MvPowerSeries.coeff_pderiv, hc, hc, hd, hf, Multiset.cons_add, ← Multiset.add_cons]
    field_simp
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hc]
    simp [dirs, fct]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
