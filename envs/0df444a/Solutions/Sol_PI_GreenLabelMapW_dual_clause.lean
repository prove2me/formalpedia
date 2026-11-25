-- Prove2me | solution 1 for PI.GreenLabelMapW.dual_clause
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:39.7932+00:00
-- url     : https://prove2.me/submissions/a8d0cdc3-b479-4a9e-8ee6-b9a12b2228e4

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_GaloisClause
import Theorems.Thm_PI_GreenLabelMapW_aroots_eq_map
import Theorems.Thm_PI_GreenLabelMapW_card_pow_sub_one_pos
import Theorems.Thm_PI_GreenLabelMapW_conj_roots
import Theorems.Thm_PI_GreenLabelMapW_gen_ne_zero
import Theorems.Thm_PI_GreenLabelMapW_gen_pow
import Theorems.Thm_PI_GreenLabelMapW_greenLab_eq
import Theorems.Thm_PI_GreenLabelMapW_greenLab_spec
import Theorems.Thm_PI_GreenLabelMapW_irreducible_charpoly_inv
import Theorems.Thm_PI_GreenLabelMapW_natDegree_minpoly_eq
import Theorems.Thm_PI_GreenLabelMapW_root_inv
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
theorem _root_.solution (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (hd : 1 ≤ d) (hs : Simple τ) (hc : IsCuspidal K τ)
    (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) :
    rootsBar K (greenLab Cv d τ') = (rootsBar K (greenLab Cv d τ)).map (·⁻¹) := by
  obtain ⟨hm, hi, hX, hdeg0, hval⟩ := greenLab_spec Cv hC hd hs hc
  have hdeg : (greenLab Cv d τ).natDegree = d := by rw [hdeg0, Fintype.card_fin]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg]; exact_mod_cast (show d ≠ 0 by omega))
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      (σ x)⁻¹ = σ x⁻¹ := fun σ x => (map_inv₀ σ x).symm
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁⁻¹ = r₂⁻¹ → r₁ = r₂ := fun _ _ _ _ h => inv_injective h
  have hint : IsIntegral K w⁻¹ := Algebra.IsIntegral.isIntegral _
  have hlab : HasCuspLabel Cv τ' (minpoly K w⁻¹) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K w⁻¹
      rw [h, aeval_X] at h0
      exact inv_ne_zero (root_ne_zero hm hi hX hw) h0
    · have hdeg' : (minpoly K w⁻¹).natDegree = (greenLab Cv d τ).natDegree :=
        natDegree_minpoly_eq hm hi hw (fun x => x⁻¹) hf hinj
      rw [hdeg', hdeg0]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun x => x⁻¹) hf y).1 hy
      have hD : 1 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
      have hn := card_pow_sub_one_pos (K := K) hD
      have hgen := gen_pow Cv hD
      have hz0 : z ≠ 0 := by rw [← hm']; exact pow_ne_zero _ (gen_ne_zero Cv hD)
      have hzi : Cv.gen (Fintype.card (Fin d)) ^
          (m * (Fintype.card K ^ Fintype.card (Fin d) - 1 - 1)) = z⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← hm', ← pow_add, ← mul_add_one, Nat.sub_add_cancel hn, mul_comm, pow_mul, hgen,
          one_pow]
      have hirr := irreducible_charpoly_inv γ hγ hz0 hz
      have hroot := root_inv γ hz0 hz
      have key := hval r hr γ⁻¹ hirr z⁻¹ hroot _ hzi
      rw [htr γ, key]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hr1 : r ^ (Fintype.card K ^ Fintype.card (Fin d) - 1) = 1 := by
        have h5 := root_pow_card hm hi hX hr
        rwa [hdeg0] at h5
      have hrinv : r⁻¹ = r ^ (Fintype.card K ^ Fintype.card (Fin d) - 1 - 1) := by
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, hr1]
      rw [hrinv, map_pow, ← pow_mul]
      congr 1
      ac_rfl
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun x => x⁻¹) hf hinj
end PI.GreenLabelMapW
