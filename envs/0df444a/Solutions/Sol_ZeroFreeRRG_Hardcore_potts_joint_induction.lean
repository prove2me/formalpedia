-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_joint_induction
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.701935+00:00
-- url     : https://prove2.me/submissions/822282f3-ed47-4154-8df5-d2163f0c6888

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsInduction
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_sector_induction_step
import Theorems.Thm_ZeroFreeRRG_Hardcore_potts_weighted_full_assignment_nonzero
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q)
    (V : Type) [Fintype V] (G : SimpleGraph V) (β : ℂ) (hβ : ‖β-1‖ < 0.35/(d:ℝ))
    (phaseStep : ∀ S : Finset V,
      (∀ T : Finset V, S ⊂ T → pottsNonzeroAt q G β T ∧ pottsCoherentAt q G β T) →
      pottsCoherentAt q G β S) :
    ∀ S : Finset V, pottsNonzeroAt q G β S ∧ pottsCoherentAt q G β S := by
  classical
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0:ℝ) < d := by linarith
  have hrad : (0.35:ℝ)/(d:ℝ) < 1 := by apply (div_lt_one₀ hdp).2; linarith
  have hβ1 : ‖β-1‖ < 1 := hβ.trans hrad
  have hwbound (W : Sym2 V → Fin q → Fin q → ℂ) (hseg : pottsSegmentWeights q G β W) :
      ∀ e ∈ G.edgeFinset, ∀ i j, ‖W e i j-1‖ < 1 := by
    intro e he i j
    obtain ⟨t,ht,heq⟩ := hseg e he i j
    rw [heq]
    have hh : (1+(t:ℂ)*(β-1))-1 = (t:ℂ)*(β-1) := by ring
    rw [hh,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    have hm : t*‖β-1‖ ≤ ‖β-1‖ := by
      nlinarith [mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (norm_nonneg (β-1))]
    exact hm.trans_lt hβ1
  have main (T : Finset V) : pottsNonzeroAt q G β (Finset.univ \ T) ∧
      pottsCoherentAt q G β (Finset.univ \ T) := by
    induction T using Finset.strongInduction with
    | H T ih =>
      have hbig : ∀ U : Finset V, (Finset.univ \ T) ⊂ U →
          pottsNonzeroAt q G β U ∧ pottsCoherentAt q G β U := by
        intro U hU
        have hc : Uᶜ ⊂ (Finset.univ \ T)ᶜ := Finset.compl_ssubset_compl.mpr hU
        have hc' : (Finset.univ \ U) ⊂ T := by simpa [Finset.compl_eq_univ_sdiff] using hc
        have hh := ih (Finset.univ \ U) hc'
        simpa using hh
      have hcoh := phaseStep (Finset.univ \ T) hbig
      constructor
      · intro W hW hseg τ
        by_cases hT : T = ∅
        · subst T
          simp only [Finset.sdiff_empty]
          exact potts_weighted_full_assignment_nonzero q G W hW τ (hwbound W hseg)
        · obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr hT
          have hvS : v ∉ (Finset.univ \ T) := by simp [hv]
          have hset : insert v (Finset.univ \ T) = Finset.univ \ T.erase v := by
            ext x
            simp only [Finset.mem_insert,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_erase]
            tauto
          have hchild : ∀ c : Fin q, pottsWeightedPartial q G W hW (insert v (Finset.univ \ T))
              (Function.update τ v c) ≠ 0 := by
            intro c
            rw [hset]
            exact (ih (T.erase v) (Finset.erase_ssubset hv)).1 W hW hseg (Function.update τ v c)
          obtain ⟨u,hu,hclose⟩ := hcoh W hW hseg τ v hvS
          exact potts_sector_induction_step q (by omega) G W hW (Finset.univ \ T) τ v hvS u hu hchild hclose
      · exact hcoh
  intro S
  have hh := main (Finset.univ \ S)
  simpa using hh
