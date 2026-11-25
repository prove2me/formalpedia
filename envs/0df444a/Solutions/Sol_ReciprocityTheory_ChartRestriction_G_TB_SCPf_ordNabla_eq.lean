-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.ordNabla_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:51:15.835112+00:00
-- url     : https://prove2.me/submissions/5eed0f92-9955-4139-b885-ea754a390553

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_foldr_eq_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_perm_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_perm_inr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_prod_perm_comm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (hc : ∀ l l', s l = s l' → Commute (nablaL B h m (ξ l).1 (ξ l).2) (nablaL B h m (ξ l').1 (ξ l').2))
    (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s ξ P G =
      PI.WickFormula.ordEval (opL B h m s ξ) (opR B h m s ξ) (MvPolynomial.rename (sideE s) P) G := by
  classical
  set F : ι → Module.End k (AA k d) := fun l => nablaL B h m (ξ l).1 (ξ l).2 with hFdef
  unfold ordNabla PI.WickFormula.ordEval
  rw [LinearMap.sum_apply, MvPolynomial.support_rename_of_injective (sideE s).injective,
    Finset.sum_image (fun x _ y _ hxy => Finsupp.mapDomain_injective (sideE s).injective hxy)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ (sideE s).injective, LinearMap.smul_apply, smul_eq_C_mul,
    Module.End.mul_apply]
  congr 1
  rw [foldr_eq_prod (fun l => nabla k B h m (ξ l).1 (ξ l).2) F (fun _ => rfl) n,
    foldr_eq_prod (fun l => nabla k B h m (ξ l).1 (ξ l).2) F (fun _ => rfl) n]
  simp only [Finsupp.mapDomain_equiv_apply]
  have hS : (((Finset.univ : Finset ι).toList.filter (fun l => s l)).map fun l => F l ^ n l).prod =
      (List.ofFn fun i => opL B h m s ξ i ^ n ((sideE s).symm (Sum.inl i))).prod := by
    rw [show (fun i => opL B h m s ξ i ^ n ((sideE s).symm (Sum.inl i))) =
      (fun l => F l ^ n l) ∘ (fun i => (sideE s).symm (Sum.inl i)) from rfl, ← List.map_ofFn]
    refine prod_perm_comm ((perm_inl s).map _) ?_
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
    have e : s l = s l' := by
      rw [(List.mem_filter.mp hl).2, (List.mem_filter.mp hl').2]
    exact (hc l l' e).pow_pow _ _
  have hC : (((Finset.univ : Finset ι).toList.filter (fun l => !s l)).map fun l => F l ^ n l).prod =
      (List.ofFn fun j => opR B h m s ξ j ^ n ((sideE s).symm (Sum.inr j))).prod := by
    rw [show (fun j => opR B h m s ξ j ^ n ((sideE s).symm (Sum.inr j))) =
      (fun l => F l ^ n l) ∘ (fun j => (sideE s).symm (Sum.inr j)) from rfl, ← List.map_ofFn]
    refine prod_perm_comm ((perm_inr s).map _) ?_
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
    have e : s l = s l' := by
      have a := (List.mem_filter.mp hl).2
      have b := (List.mem_filter.mp hl').2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at a b
      rw [a, b]
    exact (hc l l' e).pow_pow _ _
  rw [hS, hC]
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
