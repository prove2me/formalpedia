-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.isTayF_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:21.794615+00:00
-- url     : https://prove2.me/submissions/13d689eb-201e-4e75-b998-7b3bad6a337f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_isTayF_family
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_cc_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_mD_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
section Chain
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
end Chain
section Uniq
variable {σ : Type}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
end Uniq
section Fam
variable {g : ℕ}
variable {n : ℕ}
private theorem pderiv_tay_eq_tay_cons_single (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) (q : Fin 1 × Fin g) :
    pderiv ℂ q (tay θ s) = tay θ ((Pi.single q.2 1 : Fin g → ℂ) ::ₘ s) := by
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
  ext k
  have h1 : ((k q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  have h2 := hf0 k
  rw [MvPowerSeries.coeff_pderiv, hc, hc, hd, hf, Multiset.cons_add, ← Multiset.add_cons]
  field_simp
end Fam
section Main
variable {g : ℕ}
end Main
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
theorem _root_.solution {τ : Type} [Fintype τ] (f : (Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω f 0)
    (L : Fin 1 × Fin g → MvPowerSeries τ ℂ) (a : Fin 1 × Fin g → τ → ℂ) (hL0 : ∀ p, constantCoeff (L p) = 0)
    (hLd : ∀ p q, pderiv ℂ q (L p) = C (a p q)) :
    IsTayF f (fun q => ∑ p, a p q • (Pi.single p.2 1 : Fin g → ℂ)) (subst L (tay f 0)) := by
  have hL : MvPowerSeries.HasSubst L := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hL0
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hL0
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [hL0 p]; exact IsNilpotent.zero)
  have hcf : ∀ (s : Multiset (Fin g → ℂ)) (k : Fin 1 × Fin g →₀ ℕ),
      coeff k (tay f s) = mD f 0 (dirs k + s) / fct k := fun _ _ => rfl
  have lin : ∀ (c : Fin 1 × Fin g → ℂ) (T : Multiset (Fin g → ℂ)),
      mD f 0 ((∑ p, c p • (Pi.single p.2 1 : Fin g → ℂ)) ::ₘ T) =
        ∑ p, c p * mD f 0 ((Pi.single p.2 1 : Fin g → ℂ) ::ₘ T) := by
    intro c T
    simp only [mD_cons hf, map_sum, map_smul, ContinuousMultilinearMap.sum_apply,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  refine isTayF_family f _ (fun s => subst L (tay f s)) (fun q s => ?_) (fun s => ?_)
  · beta_reduce
    have htay : tay f ((∑ p, a p q • (Pi.single p.2 1 : Fin g → ℂ)) ::ₘ s) =
        ∑ p, a p q • tay f ((Pi.single p.2 1 : Fin g → ℂ) ::ₘ s) := by
      ext k
      simp only [map_sum, map_smul, hcf, smul_eq_mul, Multiset.add_cons, lin, Finset.sum_div, mul_div_assoc]
    rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hL0]
    simp only [hLd]
    rw [htay, ← MvPowerSeries.coe_substAlgHom hL, map_sum]
    simp only [map_smul]
    rw [MvPowerSeries.coe_substAlgHom hL]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [pderiv_tay_eq_tay_cons_single, MvPowerSeries.smul_eq_C_mul, mul_comm]
  · beta_reduce
    rw [cc_subst hL0, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcf]
    simp [dirs, fct]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
