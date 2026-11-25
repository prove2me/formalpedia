-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_mem_map_fd3a6c454df1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:11.161679+00:00
-- url     : https://prove2.me/submissions/c53279fe-69ab-4a69-983d-90282b2e31a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_monomial_mem_monos_9116ec3eae2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt_3adccb6b246c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_sum_expToInt__cfbcd9438ae1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_localizationToLaurent_mk_monomial_dc51169fa57e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (c : ℤ) (I : StdCell N) (x : Fin (N + 1) → ℤ) (hx : x ∈ laurentExps N c I.1) :
    Finsupp.single x (1 : S) ∈ (degLoc (polyGraded S N) c I).map (iota I) := by
  obtain ⟨hsum, hnn⟩ := hx
  set dp : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (x j).toNat
  set dm : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (-x j).toNat
  have hdm : ∀ j ∉ I.1, dm j = 0 := fun j hj => by
    simp [dm, Int.toNat_eq_zero, hnn j hj]
  have hx' : -expToInt N dm + expToInt N dp = x := by
    funext j
    have h1 : ((dp j : ℕ) : ℤ) = ((x j).toNat : ℤ) := by simp [dp]
    have h2 : ((dm j : ℕ) : ℤ) = ((-x j).toNat : ℤ) := by simp [dm]
    have := Int.toNat_sub_toNat_neg (x j)
    simp only [Pi.add_apply, Pi.neg_apply, expToInt]
    omega
  let s : monos (S := S) I.1 := ⟨monomial dm 1, monomial_mem_monos dm hdm⟩
  refine ⟨LocalizedModule.mk (monomial dp 1) s, Submodule.subset_span
    ⟨monomial dp 1, s, Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) dp, dm.degree, ?_, ?_, ?_, rfl⟩, ?_⟩
  · exact isWeightedHomogeneous_monomial _ _ _ rfl
  · exact isHomogeneous_monomial _ rfl
  · have h2 : ((dm.degree : ℕ) : ℤ) = ∑ j, expToInt N dm j := by
      rw [sum_expToInt', Finsupp.degree_eq_weight_one]; rfl
    rw [← sum_expToInt, h2, ← Finset.sum_sub_distrib, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← congrFun hx' j]
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  · change (iotaP I.1 (LocalizedModule.mk (monomial dp 1) s)).coeff = _
    rw [localizationToLaurent_mk_monomial I.1 _ s dm rfl, toL_monomial, AddMonoidAlgebra.single_mul_single, mul_one, hx']
    rfl
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
