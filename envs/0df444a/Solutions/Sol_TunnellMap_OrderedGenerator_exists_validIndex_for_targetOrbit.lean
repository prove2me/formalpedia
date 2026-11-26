-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.exists_validIndex_for_targetOrbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:18.158714+00:00
-- url     : https://prove2.me/submissions/fc17d8b0-e0b3-402c-82a1-dfb53fd578e6

import Definitions.Def_TunnellMap_GeneratorSoundness
import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_OrderedGenerator
import Theorems.Thm_TunnellMap_OrderedGenerator_alpha_pos
import Theorems.Thm_TunnellMap_OrderedGenerator_q_mem_search_bounds
import Theorems.Thm_TunnellMap_OrderedGenerator_targetOfValid_lift
import Theorems.Thm_TunnellMap_OrderedGenerator_mem_orderedIndexList
import Theorems.Thm_TunnellMap_OrderedGenerator_orbit_preferredTarget
import Theorems.Thm_TunnellMap_OrderedGenerator_representativeEdgeKey_preferredTarget
import Theorems.Thm_TunnellMap_FreeInvolution_orbit_canonicalRepresentative
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
import Theorems.Thm_TunnellMap_assemble_inl
import Theorems.Thm_TunnellMap_assemble_inr
import Theorems.Thm_TunnellMap_directionKey_negTriple
import Theorems.Thm_TunnellMap_directionKey_primitiveDirection
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_exists_preferred_midpoint_record
import Theorems.Thm_TunnellMap_generatorWitness_reconstructs_target
import Theorems.Thm_TunnellMap_generatorWitness_with_frame
import Theorems.Thm_TunnellMap_integer_square_roots
import Theorems.Thm_TunnellMap_minusVector_neg_source
import Theorems.Thm_TunnellMap_minusVector_neg_target
import Theorems.Thm_TunnellMap_plusVector_neg_source
import Theorems.Thm_TunnellMap_plusVector_neg_target
import Theorems.Thm_TunnellMap_polynomialTriple_neg
import Theorems.Thm_TunnellMap_polynomialTriple_triplePolynomial
import Theorems.Thm_TunnellMap_preferredVector_ne_zero
import Theorems.Thm_TunnellMap_primitiveDirection_idem
import Theorems.Thm_TunnellMap_primitiveDirection_negTriple
import Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
import Theorems.Thm_TunnellMap_primitivePartTriple_negTriple
import Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
import Theorems.Thm_TunnellMap_qForm_vsmul
import Theorems.Thm_TunnellMap_representativeEdgeKey_eq_preferred
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_source
import Theorems.Thm_TunnellMap_representativeEdgeKey_neg_target
import Theorems.Thm_TunnellMap_residualSourceLift_neg
import Theorems.Thm_TunnellMap_residualTargetLift_injective
import Theorems.Thm_TunnellMap_residualTargetLift_neg
import Theorems.Thm_TunnellMap_square_le_iff_mem_floorCeilInterval
import Theorems.Thm_TunnellMap_tripleContent_negTriple
import Theorems.Thm_TunnellMap_tripleContent_orientDirection
import Theorems.Thm_TunnellMap_tripleContent_primitiveDirection
import Theorems.Thm_TunnellMap_tripleContent_primitivePartTriple
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_one
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_two
import Theorems.Thm_TunnellMap_triplePolynomial_coeff_zero
import Theorems.Thm_TunnellMap_triplePolynomial_negTriple
import Theorems.Thm_TunnellMap_triplePolynomial_vsmul
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList
attribute [local simp] TunnellMap.assemble_inl
attribute [local simp] TunnellMap.assemble_inr
attribute [local simp] TunnellMap.directionKey_negTriple
attribute [local simp] TunnellMap.directionKey_primitiveDirection
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.minusVector_neg_source
attribute [local simp] TunnellMap.minusVector_neg_target
attribute [local simp] TunnellMap.plusVector_neg_source
attribute [local simp] TunnellMap.plusVector_neg_target
attribute [local simp] TunnellMap.polynomialTriple_neg
attribute [local simp] TunnellMap.polynomialTriple_triplePolynomial
attribute [local simp] TunnellMap.primitiveDirection_idem
attribute [local simp] TunnellMap.primitiveDirection_negTriple
attribute [local simp] TunnellMap.primitiveDirection_two_vsmul
attribute [local simp] TunnellMap.primitivePartTriple_negTriple
attribute [local simp] TunnellMap.primitivePartTriple_two_vsmul
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau
attribute [local simp] TunnellMap.qForm_vsmul
attribute [local simp] TunnellMap.representativeEdgeKey_neg_source
attribute [local simp] TunnellMap.representativeEdgeKey_neg_target
attribute [local simp] TunnellMap.residualSourceLift_neg
attribute [local simp] TunnellMap.residualTargetLift_neg
attribute [local simp] TunnellMap.tripleContent_negTriple
attribute [local simp] TunnellMap.tripleContent_orientDirection
attribute [local simp] TunnellMap.tripleContent_primitiveDirection
attribute [local simp] TunnellMap.tripleContent_primitivePartTriple
attribute [local simp] TunnellMap.triplePolynomial_coeff_one
attribute [local simp] TunnellMap.triplePolynomial_coeff_two
attribute [local simp] TunnellMap.triplePolynomial_coeff_zero
attribute [local simp] TunnellMap.triplePolynomial_negTriple
attribute [local simp] TunnellMap.triplePolynomial_vsmul


attribute [local simp] TunnellMap.OrderedGenerator.mem_orderedIndexList

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {n : ℤ} {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s)))
    (tOrbit : (aResidualInvolution n hnpos).Orbit) :
    ∃ i : {i // i ∈ validIndices s F},
      targetOrbitOfValid hnpos s F i = tOrbit := by
  let t₀ := canonicalAResidualRepresentative hnpos tOrbit
  let R : PreferredMidpointRecord s t₀ :=
    Classical.choice (exists_preferred_midpoint_record hn s t₀)
  obtain ⟨W, hWF⟩ := generatorWitness_with_frame hn hnpos s t₀ R F
  subst F
  let i : GeneratorIndex := ⟨W.A, W.q, W.b, W.u⟩
  have hAupper : W.A ≤ (n - 1) / 2 := by
    apply (Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)).2
    nlinarith [W.A_bound]
  have hAmem : W.A ∈ AValues n := by
    rw [AValues, mem_intIcc]
    exact ⟨by have h := W.A_pos; omega, hAupper⟩
  have hqne : W.q ≠ 0 := by
    intro hq
    apply Int.not_odd_zero
    simpa [hq] using W.q_odd
  have hqbounds := q_mem_search_bounds hnpos W.A_pos W.q_range
  have hqmem : W.q ∈ qValues n W.A := by
    simp [qValues, hqbounds, hqne, W.q_odd, W.q_range]
  have hwindow :
      (n * W.b - W.q * W.A * K W.frame) ^ 2 ≤
        alpha W.frame * M n W.A W.q := by
    simpa [alpha, beta, delta, epsilon, K, M] using W.short_window
  have hAM : 0 ≤ alpha W.frame * M n W.A W.q :=
    (sq_nonneg (n * W.b - W.q * W.A * K W.frame)).trans hwindow
  have hbBounds :=
    (square_le_iff_mem_floorCeilInterval hnpos hAM).mp hwindow
  have hbmem : W.b ∈ bValues n W.frame W.A W.q := by
    rw [bValues, mem_intIcc]
    simpa [bLower, bUpper] using hbBounds
  have huSquare := W.root_certificate.1
  have hrootExists : ∃ x : ℤ, x * x = W.frame.halfDiscriminant W.A W.q W.b := by
    exact ⟨W.u, by simpa [pow_two] using huSquare⟩
  have hsqrtMul := (Int.exists_mul_self _).mp hrootExists
  have hsqrtSquare : (Int.sqrt (W.frame.halfDiscriminant W.A W.q W.b)) ^ 2 =
      W.frame.halfDiscriminant W.A W.q W.b := by
    simpa [pow_two] using hsqrtMul
  have huCases : W.u = Int.sqrt (W.frame.halfDiscriminant W.A W.q W.b) ∨
      W.u = -Int.sqrt (W.frame.halfDiscriminant W.A W.q W.b) :=
    integer_square_roots (huSquare.trans hsqrtSquare.symm)
  have huDiv : alpha W.frame ∣
      -(beta W.frame * W.b + W.q * W.A * delta W.frame) + W.u := by
    refine ⟨W.a, ?_⟩
    simpa [alpha, beta, delta, mul_comm] using W.root_certificate.2.symm
  have humem : W.u ∈ rootValues W.frame W.A W.q W.b := by
    rw [mem_rootValues]
    exact ⟨huCases, huSquare, huDiv⟩
  have hiRaw : i ∈ rawIndices n W.frame := by
    rw [mem_rawIndices]
    exact ⟨hAmem, hqmem, hbmem, humem⟩
  have haValue : aValue W.frame i = W.a := by
    apply mul_left_cancel₀ (ne_of_gt (alpha_pos W.frame))
    calc
      alpha W.frame * aValue W.frame i =
          -(beta W.frame * W.b + W.q * W.A * delta W.frame) + W.u := by
            simpa [i] using
              aValue_linear_of_dvd W.frame i (by simpa [i] using huDiv)
      _ = alpha W.frame * W.a := by
        simpa [alpha, beta, delta] using W.root_certificate.2.symm
  have hrValue : rValue W.frame i = W.r := by
    rw [W.affine_coordinates]
    simp [rValue, i, haValue]
  have hdValue : dValue W.frame i = R.direction := by
    rw [dValue, hrValue, W.r_eq, tauInv_tau]
  have htargetValue : residualTargetLift R.target = targetValue s W.frame i := by
    unfold targetValue
    change residualTargetLift R.target =
      reconstructedTarget (residualSourceLift s) W.q (dValue W.frame i)
    rw [hdValue]
    exact generatorWitness_reconstructs_target W
  have hkey : directionKey (dValue W.frame i) = representativeEdgeKey s R.target := by
    calc
      directionKey (dValue W.frame i) = directionKey R.direction := by rw [hdValue]
      _ = directionKey (preferredVector s t₀) := by
        rw [R.direction_eq,
          directionKey_primitiveDirection (preferredVector_ne_zero s t₀)]
      _ = representativeEdgeKey s t₀ :=
        (representativeEdgeKey_eq_preferred s t₀).symm
      _ = representativeEdgeKey s R.target := by
        rw [R.target_eq, representativeEdgeKey_preferredTarget]
  have hfilters : PassesFilters s W.frame i := by
    refine ⟨?_, ?_, ?_, ?_, R.target, htargetValue, hkey⟩
    · simpa [hrValue] using W.r_tau_parity
    · simp [hdValue, R.direction_eq]
    · simpa [hdValue] using R.direction_oriented
    · simpa [hdValue] using R.direction_third_odd
  have hiValid : i ∈ validIndices s W.frame :=
    (mem_validIndices_iff s W.frame i).2 ⟨hiRaw, hfilters⟩
  let iv : {i // i ∈ validIndices s W.frame} := ⟨i, hiValid⟩
  refine ⟨iv, ?_⟩
  have htSigned : targetOfValid s W.frame iv = R.target := by
    apply residualTargetLift_injective
    exact (targetOfValid_lift s W.frame iv).trans htargetValue.symm
  rw [targetOrbitOfValid, htSigned, R.target_eq, orbit_preferredTarget]
  exact (aResidualInvolution n hnpos).orbit_canonicalRepresentative
    aResidualLexKey aResidualLexKey_injective tOrbit
end TunnellMap.OrderedGenerator
