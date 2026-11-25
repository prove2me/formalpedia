-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:07.82736+00:00
-- url     : https://prove2.me/submissions/83a90098-8fe1-45bc-a925-feab49542e36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_vandermondeOf_perm_3aea40e9f6fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockPermute f N w (blockVandermonde f N) = blockSign f N w • blockVandermonde f N := by
  simp only [blockVandermonde, map_prod]
  have h1 : ∀ τ : Fin f, blockPermute f N w (vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N)) =
      (((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : RootRing f N) *
        vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N) := by
    intro τ
    have : blockPermute f N w (vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N)) =
        vandermondeOf fun i : Fin N => (X (τ, w τ i) : RootRing f N) := by
      simp only [vandermondeOf, map_prod, map_sub, blockPermute_X]
    rw [this]
    exact vandermondeOf_perm (fun i : Fin N => (X (τ, i) : RootRing f N)) (w τ)
  rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_mul_distrib, Algebra.smul_def,
    blockSign, map_prod]
  simp
end GroundTheory.Heights₂.Heights.RestTerms.Flag
