-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.CG.pi_iterated_integral_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:22.680956+00:00
-- url     : https://prove2.me/submissions/ceb92994-640b-4ee1-b589-cdf46772c4fa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_self
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_ne
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_splitY_self
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_splitY_ne
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_one
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_continuous_splitY_left
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_continuous_splitY_right
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_self
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_ne
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_apply_self
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_psa_self
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_psa_ne
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitM_symm
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitM_mp
import Theorems.Thm_PositivityTheory_Rg_BcB_CG_pi_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
variable [One X]
namespace PositivityTheory.Rg.BcB.CG
theorem _root_.solution (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
      (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v),
      Fintype.card ι = n →
      (∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b)) → (∀ J, Continuous (u J)) →
      (∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
        val v * u J (Function.update y v 1)) →
      ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 := by
  induction n with
  | zero =>
    intro ι _ _ Idx _ _ e val u I hn he hu hloc
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    rw [Measure.pi_of_empty (fun _ : ι => μ) (1 : ι → X), integral_dirac, Fintype.sum_unique,
      Subsingleton.elim (default : ∀ v, Idx v) I]
    simp
  | succ n ih =>
    intro ι _ _ Idx _ _ e val u I hn he hu hloc
    obtain ⟨w⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hn' : Fintype.card {v // v ≠ w} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    have hmp := splitM_mp μ w
    have hF := pi_integrable μ e u I he hu

    have hsplit : ∀ (t : X) (z : {v // v ≠ w} → X),
        (∑ J, (∏ v, e v (splitY w t z v) (I v) (J v)) * u J (splitY w t z)) =
          ∑ j, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            (e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) := by
      intro t z
      rw [← Fintype.sum_equiv (Equiv.piSplitAt w Idx).symm
        (fun p => (∏ v, e v (splitY w t z v) (I v) ((Equiv.piSplitAt w Idx).symm p v)) *
          u ((Equiv.piSplitAt w Idx).symm p) (splitY w t z)) _ (fun _ => rfl), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J' _ => ?_
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ w, splitY_self, psa_symm_self]
      simp only [splitY_ne, psa_symm_ne]
      ring
    have hint : ∀ (z : {v // v ≠ w} → X) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v),
        Integrable (fun t => e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) μ :=
      fun z j J' => ((he w (I w) j).1.mul ((hu _).comp (continuous_splitY_left w z))).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right (he w (I w) j).2)
    let u' : (∀ v : {v // v ≠ w}, Idx v) → ({v // v ≠ w} → X) → ℂ :=
      fun J' z => val w * u ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
    have hinner : ∀ z : {v // v ≠ w} → X,
        ∫ t, (∑ J, (∏ v, e v ((splitM w).symm (t, z) v) (I v) (J v)) * u J ((splitM w).symm (t, z))) ∂μ =
          ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) * u' J' z := by
      intro z
      simp only [splitM_symm, hsplit]
      rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun J' _ => (hint z j J').const_mul _]
      have hj : ∀ j : Idx w, ∫ t, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            (e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) ∂μ =
          ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            ∫ t, e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z) ∂μ := fun j => by
        rw [integral_finset_sum _ fun J' _ => (hint z j J').const_mul _]
        simp only [integral_const_mul]
      rw [Finset.sum_congr rfl fun j _ => hj j]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J' _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      have h1 := hloc w ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
      rw [psa_symm_self] at h1
      simp only [update_psa_self, update_splitY_self] at h1
      exact h1
    have he' : ∀ (v : {v // v ≠ w}) a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b) :=
      fun v => he v
    have hu' : ∀ J', Continuous (u' J') :=
      fun J' => continuous_const.mul ((hu _).comp (continuous_splitY_right w 1))
    have hloc' : ∀ (v : {v // v ≠ w}) (J' : ∀ v : {v // v ≠ w}, Idx v) (z : {v // v ≠ w} → X),
        ∑ j, ∫ t, e v t (J' v) j * u' (Function.update J' v j) (Function.update z v t) ∂μ =
          val v * u' J' (Function.update z v 1) := by
      intro v J' z
      have h1 := hloc v ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
      rw [psa_symm_ne] at h1
      simp only [update_psa_ne, update_splitY_ne] at h1
      simp only [u']
      calc _ = val w * ∑ j, ∫ t, e v t (J' v) j *
              u ((Equiv.piSplitAt w Idx).symm (I w, Function.update J' v j)) (splitY w 1 (Function.update z v t)) ∂μ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← integral_const_mul]
            congr 1
            funext t
            ring
        _ = _ := by rw [h1]; ring
    have hIH := ih {v // v ≠ w} (fun v => Idx v) (fun v => e v) (fun v => val v) u' (fun v => I v) hn' he' hu' hloc'
    calc ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ)
        = ∫ q, (fun y => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ((splitM w).symm q)
            ∂(μ.prod (Measure.pi fun _ : {v // v ≠ w} => μ)) :=
          ((MeasurePreserving.symm _ hmp).integral_comp' _).symm
      _ = ∫ z, ∫ t, (fun y => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ((splitM w).symm (t, z)) ∂μ
            ∂(Measure.pi fun _ : {v // v ≠ w} => μ) :=
          integral_prod_symm _ (((MeasurePreserving.symm _ hmp).integrable_comp_emb
            (splitM w).symm.measurableEmbedding).2 hF)
      _ = ∫ z, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) * u' J' z
            ∂(Measure.pi fun _ : {v // v ≠ w} => μ) :=
          integral_congr_ae (ae_of_all _ hinner)
      _ = (∏ v : {v // v ≠ w}, val v) * u' (fun v => I v) 1 := hIH
      _ = (∏ v, val v) * u I 1 := by
          simp only [u', psa_symm_apply_self, splitY_one]
          rw [Fintype.prod_eq_mul_prod_subtype_ne _ w]
          ring
end PositivityTheory.Rg.BcB.CG
