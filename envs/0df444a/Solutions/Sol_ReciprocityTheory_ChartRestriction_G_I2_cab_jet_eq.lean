-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.cab_jet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:05.326252+00:00
-- url     : https://prove2.me/submissions/462a9561-543b-42ad-b80d-c06436cf9b84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_perm_of_ofFn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_iter_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℕ} {β P : EuclideanSpace ℂ ι → ℂ}
    (hβ : ContDiff ℂ (⊤ : WithTop ℕ∞) β) (hP : ContDiff ℂ (⊤ : WithTop ℕ∞) P)
    (h : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) P 0) :
    iteratedFDeriv ℂ c β 0 = iteratedFDeriv ℂ c P 0 := by
  have hbasis : ∀ l : Fin c → ι, iteratedFDeriv ℂ c β 0 (fun k => EuclideanSpace.single (l k) 1) =
      iteratedFDeriv ℂ c P 0 (fun k => EuclideanSpace.single (l k) 1) := by
    intro l
    set m : Multiset ι := (List.ofFn l : Multiset ι) with hm
    set α := Multiset.toFinsupp m with hα
    have hαm : Finsupp.toMultiset α = m := Multiset.toFinsupp_toMultiset m
    have hn : Multiset.card (Finsupp.toMultiset α) = c := by
      rw [hαm, hm, Multiset.coe_card, List.length_ofFn]
    have hdeg : α.degree ≤ c := by
      have : Multiset.card (Finsupp.toMultiset α) = α.degree := by
        simp only [Finsupp.card_toMultiset]
        rfl
      omega
    have h1 := h α hdeg
    unfold polyDeriv at h1
    simp only [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_true, one_mul] at h1
    rw [cab_iter_cast β 0 hn, cab_iter_cast P 0 hn] at h1
    set g : Fin c → ι := fun k => (Finsupp.toMultiset α).toList.get
      ((Fin.cast hn.symm k).cast (Multiset.length_toList _).symm) with hg
    have hperm : List.Perm (List.ofFn l) (List.ofFn g) := by
      have e1 : List.ofFn g = (Finsupp.toMultiset α).toList := by
        apply List.ext_get (by simp [hn])
        intro k h1 h2; simp [hg]
      rw [e1, ← Multiset.coe_eq_coe, Multiset.coe_toList, hαm]
    obtain ⟨σ, hσ⟩ := cab_perm_of_ofFn l g hperm
    have hv : ((fun k => EuclideanSpace.single
        ((Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) (1 : ℂ)) ∘
          Fin.cast hn.symm) = (fun k => EuclideanSpace.single (l k) (1 : ℂ)) ∘ σ := by
      funext k
      have := congrFun hσ k
      simp only [Function.comp_apply] at this ⊢
      rw [← this]
    rw [hv, (hβ.contDiffAt).iteratedFDeriv_comp_perm, (hP.contDiffAt).iteratedFDeriv_comp_perm] at h1
    simpa using h1
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun ι ℂ).toBasis)
  intro l
  simpa [EuclideanSpace.basisFun_apply] using hbasis l
end ReciprocityTheory.ChartRestriction.G.I2
