-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:04.165045+00:00
-- url     : https://prove2.me/submissions/fb31e2f0-d028-4ccd-9f9b-ea5f95ac4bbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_of_mem_minimalPrimes_1a5a33e9bb16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomogIdeal_sup_span_33355a37f805
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_killStable_2361f4b4da88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_contractPrime_isRelevant_e828c0104b5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_eventualValue_eq_zero_9297a58f17ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_sub_b0db39314222
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_rename_monoSmall_5eb05c0d4637
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isMultiHomog_rename_monoSmall_f35f3b836806
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
variable {F K K' j ι'}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ D D0 : ℕ,
      ringKrullDim (MRing ι' F ⧸ P') = D → D ≤ n + Fintype.card K' →
      ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') = D0 →
      D0 < n + Fintype.card K →
      ∀ bs : Fin n → K → ℤ, intNum F P' (fun i => pullDeg j (bs i)) = 0 := by
  intro n
  induction n with
  | zero =>
    intro P' hP' D D0 _ _ hD0 hlt bs
    have := hP'.isPrime
    obtain ⟨D1, hc, hD1⟩ := exists_ringKrullDim_eq
      (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
    rw [hD0] at hD1
    have : D0 = D1 := by exact_mod_cast hD1
    omega
  | succ k ih =>
    intro P' hP' D D0 hD hDle hD0 hlt bs
    have := hP'.isPrime
    obtain ⟨D', hc', hD'⟩ := exists_ringKrullDim_eq
      (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
    rw [hD] at hD'
    have hDD : D = D' := by exact_mod_cast hD'
    subst hDD
    by_cases hlow : D - Fintype.card K' < k + 1
    · have hrel : relDim P' = ((D - Fintype.card K' : ℕ) : WithBot (WithTop ℤ)) := by
        rw [relDim_eq_int hD, natCast_withBot_withTop]
        congr 2
        omega
      exact eventualValue_eq_zero
        ((h1 F K' ι' P' hP'.multiHomog hP'.relevant _ hrel).2 (k + 1) hlow _)
    · have hrel : relDim P' = ((k + 1 : ℕ) : WithBot (WithTop ℤ)) := by
        rw [relDim_eq_int hD, natCast_withBot_withTop]
        congr 2
        omega
      choose i hi using hP'.relevant
      set b := bs (Fin.last k)
      set ep : K → ℕ := fun κ => (b κ).toNat
      set em : K → ℕ := fun κ => (-b κ).toNat
      have hnotmem : ∀ e : K → ℕ, rename (blockIncl j ι') (monoSmall (F := F) i e) ∉ P' := by
        intro e hmem
        rw [rename_monoSmall] at hmem
        obtain ⟨κ, -, hκ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP'.isPrime)).mp hmem
        exact hi (j κ) (hP'.isPrime.mem_of_pow_mem _ hκ)

      have hzero : ∀ (e : K → ℕ) (W : Ideal (MRing ι' F)),
          W ∈ (P' ⊔ Ideal.span {rename (blockIncl j ι') (monoSmall (F := F) i e)}).minimalPrimes →
          IsRelevant W → intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by
        intro e W hmin hWrel
        have hWp : W.IsPrime := hmin.1.1
        have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes
          (isMultiHomogIdeal_sup_span hP'.multiHomog (isMultiHomog_rename_monoSmall i e)) hmin
        have hPW : P' ≤ W := le_sup_left.trans hmin.1.2
        have hfW : rename (blockIncl j ι') (monoSmall (F := F) i e) ∈ W :=
          (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
        obtain ⟨DW, -, hDW⟩ := exists_ringKrullDim_eq
          (fun T q hq => killBlocks_mem_of_isMultiHomogIdeal hWh T hq) hWrel
        obtain ⟨DW0, -, hDW0⟩ := exists_ringKrullDim_eq
          (contractPrime_killStable j ι' hWh) (contractPrime_isRelevant j ι' hWrel)
        have hdrop := ringKrullDim_add_one_le hPW (hnotmem e) hfW
        rw [hDW, hD] at hdrop
        have hdrop' : DW + 1 ≤ D := by exact_mod_cast hdrop
        have hdrop0 := ringKrullDim_add_one_le (P := contractPrime j P') (Q := contractPrime j W)
          (Ideal.comap_mono hPW) (f := monoSmall i e) (hnotmem e) hfW
        rw [hDW0, hD0] at hdrop0
        have hdrop0' : DW0 + 1 ≤ D0 := by exact_mod_cast hdrop0
        exact ih W ⟨hWp, hWh, hWrel⟩ DW DW0 hDW (by omega) hDW0 (by omega) _
      have hsupp : ∀ (g : MRing ι' F) (W : Ideal (MRing ι' F)), divCycle P' g W ≠ 0 →
          W ∈ (P' ⊔ Ideal.span {g}).minimalPrimes ∧ IsRelevant W := by
        intro g W h
        unfold divCycle at h
        split_ifs at h with hc
        · exact hc
        · exact absurd rfl h
      have hcut := h2 F K' ι' P' hP' k hrel _ _ _ _ (isMultiHomog_rename_monoSmall i ep)
        (isMultiHomog_rename_monoSmall i em) (hnotmem ep) (hnotmem em)
        (fun x : Fin k => pullDeg j (bs x.castSucc))
      rw [pullNat_sub] at hcut
      have hsplit : (fun x => pullDeg j (bs x)) = Fin.snoc (α := fun _ => K' → ℤ)
          (fun x : Fin k => pullDeg j (bs x.castSucc)) (pullDeg j b) := by
        funext x
        refine Fin.lastCases ?_ (fun y => ?_) x
        · simp [b]
        · simp
      rw [hsplit, hcut]
      have hterm : ∀ W, ratDiv P' (rename (blockIncl j ι') (monoSmall (F := F) i ep))
          (rename (blockIncl j ι') (monoSmall (F := F) i em)) W *
            intNum F W (fun x : Fin k => pullDeg j (bs x.castSucc)) = 0 := by
        intro W
        by_cases hA : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i ep)) W = 0
        · by_cases hB : divCycle P' (rename (blockIncl j ι') (monoSmall (F := F) i em)) W = 0
          · simp [ratDiv, hA, hB]
          · obtain ⟨hm, hr⟩ := hsupp _ W hB
            rw [hzero em W hm hr, mul_zero]
        · obtain ⟨hm, hr⟩ := hsupp _ W hA
          rw [hzero ep W hm hr, mul_zero]
      simp only [cycEval, hterm, finsum_zero]
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
