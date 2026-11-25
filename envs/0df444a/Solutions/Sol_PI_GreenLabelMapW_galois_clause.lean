-- Prove2me | solution 1 for PI.GreenLabelMapW.galois_clause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:20.013779+00:00
-- url     : https://prove2.me/submissions/3bfb2842-0bc0-4c71-aa80-52eb90f1c25c

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_GaloisClause
import Theorems.Thm_PI_GreenLabelMapW_aroots_eq_map
import Theorems.Thm_PI_GreenLabelMapW_conj_roots
import Theorems.Thm_PI_GreenLabelMapW_greenLab_eq
import Theorems.Thm_PI_GreenLabelMapW_greenLab_spec
import Theorems.Thm_PI_GreenLabelMapW_natDegree_minpoly_eq
import Theorems.Thm_PI_GreenLabelMapW_root_ne_zero
import Theorems.Thm_PI_GreenLabelMapW_root_pow_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ) (α : ℂ ≃+* ℂ) (a : ℕ)
    (hα : ∀ ζ : ℂ, ζ ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 → α ζ = ζ ^ a)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (hd : 1 ≤ d) (hs : Simple τ) (hc : IsCuspidal K τ)
    (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = α (LinearMap.trace ℂ τ (τ.ρ γ))) :
    rootsBar K (greenLab Cv d τ') = (rootsBar K (greenLab Cv d τ)).map (· ^ a) := by
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := greenLab_spec Cv hC hd hs hc
  rw [Fintype.card_fin] at hdeg
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg]; exact_mod_cast (show d ≠ 0 by omega))
  have hunit : ∀ r, aeval r (greenLab Cv d τ) = 0 →
      Cv.ι r ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 := by
    intro r hr
    have h1 := root_pow_card hm hi hX hr
    rw [hdeg] at h1
    obtain ⟨k, hk⟩ : (q K ^ d - 1) ∣ ∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1) :=
      Finset.dvd_prod_of_mem (fun e => q K ^ e - 1) (Finset.mem_Icc.2 ⟨hd, le_rfl⟩)
    rw [hk, pow_mul, ← map_pow, h1, map_one, one_pow]
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁ ^ a = r₂ ^ a → r₁ = r₂ := by
    intro r₁ r₂ h₁ h₂ h
    apply Cv.ι_inj r₁ r₂ (root_ne_zero hm hi hX h₁) (root_ne_zero hm hi hX h₂)
    apply α.injective
    rw [hα _ (hunit r₁ h₁), hα _ (hunit r₂ h₂), ← map_pow, ← map_pow, h]
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      (σ x) ^ a = σ (x ^ a) := fun σ x => (map_pow σ x a).symm
  have hint : IsIntegral K (w ^ a) := Algebra.IsIntegral.isIntegral _
  have hlab : HasCuspLabel Cv τ' (minpoly K (w ^ a)) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K (w ^ a)
      rw [h, aeval_X] at h0
      exact pow_ne_zero a (root_ne_zero hm hi hX hw) h0
    · have hdeg' : (minpoly K (w ^ a)).natDegree = (greenLab Cv d τ).natDegree :=
        natDegree_minpoly_eq hm hi hw (fun x => x ^ a) hf hinj
      rw [hdeg', hdeg, Fintype.card_fin]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun x => x ^ a) hf y).1 hy
      rw [htr γ, hval r hr γ hγ z hz m hm', map_mul, map_pow, map_neg, map_one, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hu : (Cv.ι r ^ (m * Fintype.card K ^ i)) ^ (∏ e ∈ Finset.Icc 1 d, (q K ^ e - 1)) = 1 := by
        rw [pow_right_comm, hunit r hr, one_pow]
      rw [hα _ hu, map_pow, ← pow_mul, ← pow_mul]
      congr 1
      ac_rfl
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun x => x ^ a) hf hinj
end PI.GreenLabelMapW
