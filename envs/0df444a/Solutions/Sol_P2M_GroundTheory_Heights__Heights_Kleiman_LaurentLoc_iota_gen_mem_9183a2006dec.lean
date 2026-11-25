-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_gen_mem_9183a2006dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:39.973843+00:00
-- url     : https://prove2.me/submissions/c38ee1e1-b67a-47e0-9018-d507c6b40c6a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_coeff_toL_50d5c86175e2
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
theorem _root_.solution (c : ℤ) (I : StdCell N) (m : Poly S N) (s : monos (S := S) I.1) (a : ℤ) (e : ℕ)
    (hm : m ∈ (polyGraded S N).piece a) (hs : (s : Poly S N).IsHomogeneous e) (hc : a - e = c) :
    iota I (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) (Poly S N)) ∈
      laurentDeg S N c I := by
  obtain ⟨f, hfI, hf⟩ := mem_monos_iff s.2
  change ((iotaP I.1 (LocalizedModule.mk m s)).coeff.support : Set _) ⊆ laurentExps N c I.1
  rw [localizationToLaurent_mk_monomial I.1 m s f hf]
  intro y hy
  rw [Finset.mem_coe, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_single_mul_apply, one_mul,
    neg_neg, coeff_toL] at hy
  have hy2 : expToInt N f + y ∈ (Finsupp.mapDomain (expToInt N) (AddMonoidAlgebra.coeff m)).support :=
    Finsupp.mem_support_iff.mpr hy
  obtain ⟨d, hd, hdy⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hy2)
  have : Nontrivial S := nontrivial_of_ne _ _ hy
  have hwd : Finsupp.weight (fun _ : Fin (N + 1) => (1 : ℤ)) d = a :=
    hm (Finsupp.mem_support_iff.mp hd)
  have hwf : Finsupp.weight (1 : Fin (N + 1) → ℕ) f = e := by
    refine hs ?_
    rw [hf, coeff_monomial, if_pos rfl]
    exact one_ne_zero
  have hy' : y = expToInt N d - expToInt N f := by rw [hdy]; abel
  refine ⟨?_, fun j hj => ?_⟩
  · have h1 := sum_expToInt d
    have h2 : ∑ j, expToInt N f j = (e : ℤ) := by rw [sum_expToInt', ← hwf]
    rw [hy']
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, h1, h2, hwd, hc]
  · rw [hy']
    simp [expToInt, hfI j hj]
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
