-- Prove2me | solution 1 for ReciprocityTheory.Cheb.PE_cyclotomicField_le_mul_Pcl_add_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:14.678822+00:00
-- url     : https://prove2.me/submissions/ee4aaa5f-c4ca-443b-855b-b4bee092b9db

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB
import Theorems.Thm_ReciprocityTheory_Cheb_csb_nrm_pos
import Theorems.Thm_ReciprocityTheory_Cheb_csb_pow_le
import Theorems.Thm_ReciprocityTheory_Cheb_affine_proper_base_change
import Theorems.Thm_ReciprocityTheory_Cheb_fibre_sum_le
import Theorems.Thm_ReciprocityTheory_Cheb_splitA_fibre
import Theorems.Thm_ReciprocityTheory_Cheb_splitA_finite_not_coprime
import Theorems.Thm_ReciprocityTheory_Cheb_splitA_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * Pcl E l 1 s + C := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hfin := splitA_finite_not_coprime E l hl0
  set A : ℝ := ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)
  set B : ℝ := ∑' q : Prm E, (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)
  refine ⟨((l - 1 : ℕ) : ℝ) * (A + B), fun s hs => ?_⟩
  have hA : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)) := affine_proper_base_change.2.2 E 2 (by norm_num)
  have hB : Summable (fun q : Prm E => (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)) := by
    apply summable_of_ne_finset_zero (s := hfin.toFinset)
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    simp only [Set.mem_ofPred_eq, not_not] at hq
    simp [hq]
  have hP1 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) (affine_proper_base_change.2.2 E s hs)
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  let h : Prm E → ℝ := fun q =>
    ((if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) + ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)) +
      (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)
  have hh0 : ∀ q, 0 ≤ h q := by
    intro q
    simp only [h]
    have : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ) := by positivity
    split_ifs <;> positivity
  have hhs : Summable h := (hP1.add hA).add hB
  have hfh : ∀ P : Prm (CyclotomicField l E), ((Nrm P : ℕ) : ℝ) ^ (-s) ≤ h (under P) := by
    intro P
    set q := under (E := E) P with hq
    have hq1 := csb_nrm_pos q
    have hP1' := csb_nrm_pos P
    have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ) := by positivity
    have hPs : 0 ≤ ((Nrm P : ℕ) : ℝ) ^ (-s) := by positivity
    simp only [h]
    by_cases hc : Nat.Coprime (Nrm q) l
    · have hnd : ¬ l ∣ Nrm q := by
        rw [← Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
        exact hc.symm
      rw [if_pos hc, add_zero]
      rcases splitA_norm E l q P hq.symm hnd with ⟨he, h1⟩ | hsq
      · rw [if_pos h1, he]
        linarith
      · have := csb_pow_le _ _ hq1 hsq s hs
        have : 0 ≤ (if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
          split_ifs <;> positivity
        linarith
    · rw [if_neg hc]
      have : ((Nrm P : ℕ) : ℝ) ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hP1') (by linarith)
      have : 0 ≤ (if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
        split_ifs <;> positivity
      linarith
  have key := fibre_sum_le (under (E := E)) (fun P : Prm (CyclotomicField l E) => ((Nrm P : ℕ) : ℝ) ^ (-s)) h
    (l - 1) (fun P => by positivity) hfh hh0 hhs (fun q => splitA_fibre E l hirr q)
  have hsum : ∑' q, h q = Pcl E l 1 s + A + B := by
    simp only [h]
    rw [(hP1.add hA).tsum_add hB, hP1.tsum_add hA]
    rfl
  have : PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * ∑' q, h q := key.2
  rw [hsum] at this
  linarith
end ReciprocityTheory.Cheb
