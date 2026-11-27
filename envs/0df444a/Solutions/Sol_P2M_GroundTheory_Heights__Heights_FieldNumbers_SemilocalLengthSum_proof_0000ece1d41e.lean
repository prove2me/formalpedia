-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalLengthSum_proof_0000ece1d41e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:55:54.183031+00:00
-- url     : https://prove2.me/submissions/37d42181-cc92-4e6e-b951-225633499593

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFiniteAlgebraLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalLengthSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401


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
set_option synthInstance.maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace SemilocalLengthSum
theorem _root_.solution (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFiniteRank.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : FiniteAlgebraLengthSum.Statement.{u}) (h5 : SemilocalMaxIdeals.Statement.{u}) :
    SemilocalLengthSum.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d hd α hα β hβ
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  refine ⟨hfin, ?_⟩
  have := (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have := (h3 F K (fun k => ι' (j k)) (contractPrime j P') (isMultiProjPrime_contractPrime j ι' hP')
    W hW hPW).1.2
  obtain ⟨𝔪, h𝔪, hinj, hcov, hloc⟩ := h5 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  let alg : ∀ W' : fibrePrimes j P' W,
      Algebra (degZeroLoc P' (fibrePrimes j P' W)) (degZeroLoc P' {W'.1}) :=
    fun W' => degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  rw [h4 _ _ _ 𝔪 h𝔪 hinj hcov (fun W' => degZeroLoc P' {W'.1}) (fun W' => (hloc W').1) α,
    Finset.sum_filter, Finset.sum_subtype hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  refine Finset.sum_congr rfl fun W' _ => ?_
  obtain ⟨hW'p, -, hW'c⟩ := W'.2
  have := hW'p.isPrime
  have hb : algebraMap _ (degZeroLoc P' {W'.1}) (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) α) = β W'.1 :=
    Subtype.ext (hβ W'.1 W'.2).symm
  rw [hb, (hloc W').2, ← hd W'.1 hW'p hW'c]
  split_ifs with haW'
  · rfl
  rw [Ring.ord_of_isUnit, zero_mul]
  have hne : ∀ g, g ∉ contractPrime j P' → algebraMap (MRing ι' F ⧸ P')
      (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' (rename (blockIncl j ι') g)) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hhP : h ∉ contractPrime j P' := fun hm => hhW (hPW hm)
  refine IsUnit.of_mul_eq_one ⟨_, div_mem_degZeroLoc P' {W'.1} (isMultiHomog_rename j ι' hh)
    (isMultiHomog_rename j ι' ha) haP (fun W'' hW'' => (Set.mem_singleton_iff.mp hW'') ▸ haW')⟩ ?_
  apply Subtype.ext
  change (β W'.1 : FractionRing (MRing ι' F ⧸ P')) * _ = 1
  rw [hβ W'.1 W'.2, hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  have := hne h hhP
  have := hne a haP
  field_simp
end SemilocalLengthSum
end GroundTheory.Heights₂.Heights.FieldNumbers
