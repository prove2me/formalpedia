-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_proof_f61b21d2b299
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:04.045644+00:00
-- url     : https://prove2.me/submissions/9170f297-2ec9-40e2-b75c-a6fa10e3e9fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_isMultiHomog_3bfdc52c8197
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_algebraMap_mk_ne_zero_5503709ac0c7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_mem_chartIdeal_iff_bfb81604f357
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d


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
open MChartLocDim
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace MChartLocDim
theorem _root_.solution (h₁ : DegZeroLocQuot.Statement.{u}) (h₂ : MChartDehomog.Statement.{u})
    (h₃ : MChartHomog.Statement.{u}) : MChartLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P W _ _ hPW u hu
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hQ⟩ := h₃ F K ι u p
    exact (mem_chartIdeal_iff W u hu (hQ W hu)).2 (hPW ((mem_chartIdeal_iff P u huP (hQ P huP)).1 hp))
  set q := (chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hle)
  let _ := (toLoc P W hPW u hu).toAlgebra
  have hmap : ∀ p, ((algebraMap (MRing ι F ⧸ chartIdeal P u) (degZeroLoc P {W})
      (Ideal.Quotient.mk _ p) : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = chartMap P u p :=
    fun p => rfl
  have hmemq : ∀ p, Ideal.Quotient.mk (chartIdeal P u) p ∈ q ↔ p ∈ chartIdeal W u :=
    fun p => Ideal.mem_quotient_iff_mem hle
  have : IsLocalization.AtPrime (degZeroLoc P {W}) q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hpW : p ∉ chartIdeal W u := fun h => ha ((hmemq p).2 h)
      obtain ⟨b, h, hh, hQ⟩ := h₃ F K ι u p
      have hhW : h ∉ W := fun h' => hpW ((mem_chartIdeal_iff W u hu (hQ W hu)).2 h')
      have hinv := div_mem_degZeroLoc P {W} (chartMonomial_isMultiHomog u b) hh (fun h' => hhW (hPW h'))
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hhW)
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      rw [Subalgebra.coe_mul, hmap, hQ P huP, Subalgebra.coe_one,
        div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b))
        (algebraMap_mk_ne_zero P (fun h' => hhW (hPW h')))
    · rintro ⟨x, hx⟩
      obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := h₁ F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; infer_instance) x hx
      have hgW' : g ∉ W := hgW W rfl
      have hgq : Ideal.Quotient.mk (chartIdeal P u) g ∈ q.primeCompl := fun h' =>
        hgW' ((mem_chartIdeal_iff W u hu (h₂ F K ι W u hu g b hg)).1 ((hmemq g).1 h'))
      refine ⟨(Ideal.Quotient.mk _ f, ⟨_, hgq⟩), Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hmap, hmap, h₂ F K ι P u huP g b hg, h₂ F K ι P u huP f b hf]
      have h1 := algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)
      have h2 := algebraMap_mk_ne_zero P hgP
      field_simp
    · intro a c hac
      refine ⟨1, ?_⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h := congrArg Subtype.val hac
      rw [hmap, hmap, ← sub_eq_zero, ← map_sub] at h
      rw [Submonoid.coe_one, one_mul, one_mul]
      exact Ideal.Quotient.eq.mpr (RingHom.mem_ker.mpr h)
  exact IsLocalization.AtPrime.ringKrullDim_eq_height q (degZeroLoc P {W})
end MChartLocDim
end GroundTheory.Heights₂.Heights.FieldNumbers
