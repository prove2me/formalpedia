-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NormalModelFibre_exists_mem_fibre_6e8d57f866cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:01.863252+00:00
-- url     : https://prove2.me/submissions/b65ea84c-476c-4571-a564-c78a17b2f618

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelProper_proof_63b250feae60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ModelLocalizationMaximalPoint_proof_1cc86273a304


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
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
namespace GroundTheory.Heights₂.Heights.NormalModelFibre
theorem _root_.solution {q : Fin n → ℂ} (hq : q ∈ zeroSet J) :
    ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q := by
  have : M.ideal.IsPrime := M.isPrime
  have h0 : (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
    intro h
    obtain ⟨f, hf, hf0⟩ := Submonoid.mem_map.1 h
    apply (Ideal.mem_primeCompl_iff).1 hf
    rw [RingHom.mem_ker]
    have h1 : rename Sum.inl f ∈ M.ideal := Ideal.Quotient.eq_zero_iff_mem.1 hf0
    have h2 : f ∈ J := by
      rw [← M.comap_eq]
      exact h1
    exact hq f h2
  have hle := le_nonZeroDivisors_of_noZeroDivisors h0
  have : Nontrivial (Localization (normalModelSubmonoid M q)) :=
    (IsLocalization.injective (M := normalModelSubmonoid M q)
      (S := Localization (normalModelSubmonoid M q)) hle).nontrivial
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (Localization (normalModelSubmonoid M q))
  obtain ⟨w, hw, hwq, -⟩ := ModelLocalizationMaximalPoint.proof n J q M P hP
  exact ⟨w, hw, hwq⟩
end GroundTheory.Heights₂.Heights.NormalModelFibre
