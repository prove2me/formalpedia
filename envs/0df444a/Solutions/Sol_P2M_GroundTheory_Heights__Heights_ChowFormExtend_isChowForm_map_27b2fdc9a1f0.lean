-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExtend_isChowForm_map_27b2fdc9a1f0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:04.916637+00:00
-- url     : https://prove2.me/submissions/306f4578-e1a5-478f-bc51-38b8562b9777

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_vanishes_incidence_iff_796d408552b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_incidenceIdeal_map_8d93a5362789
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_radical_map_eq_9ece7ec07417
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_sum_coordPoly_903079f12110
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_sum_8ff9631ad41f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_coordPoly_mem_of_mem_map_75eab8a0118b

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
namespace GroundTheory.Heights₂.Heights.ChowFormExtend
theorem _root_.solution (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] [Algebra K L] {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (hf : IsChowForm I k f) :
    IsChowForm (I.map (map (algebraMap K L))) k (map (algebraMap K L) f) := by
  obtain ⟨hf0, hf⟩ := hf
  set R := (incidenceIdeal I k).radical
  have hK := fun g => vanishes_incidence_iff I k g
  have hrad : (incidenceIdeal (I.map (map (algebraMap K L))) k).radical = R.map (map (algebraMap K L)) := by
    rw [incidenceIdeal_map, radical_map_eq h]
  have hmapX : ∀ (j : Fin n) (p : MvPolynomial (Fin k × Fin n) K),
      map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl p) =
        X (Sum.inr j) * rename Sum.inl (map (algebraMap K L) p) := by
    intro j p
    rw [map_mul, map_X, map_rename]
  refine ⟨fun h0 => hf0 (map_injective _ (algebraMap K L).injective (by rw [h0, map_zero])), fun g => ?_⟩
  rw [vanishes_incidence_iff, hrad]
  constructor
  · intro hg
    classical
    let b := Module.Basis.ofVectorSpace K L
    set S := coordSupport b g
    set hc := fun c => coordPoly (b.coord c) g
    have hsum : ∑ c ∈ S, C (b c) * map (algebraMap K L) (hc c) = g := sum_coordPoly b g
    have hdiv : ∀ c ∈ S, ∃ q, hc c = f * q := by
      intro c hcS
      refine (hf _).1 ((hK _).2 fun j => ?_)
      have e : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ S,
          C (b c') * map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl (hc c')) := by
        conv_lhs => rw [← hsum]
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul, rename_C, hmapX]
        ring
      have hmem := coordPoly_mem_of_mem_map b R (e ▸ hg j) c
      rwa [coordPoly_sum, if_pos hcS] at hmem
    choose! q hq using hdiv
    refine ⟨∑ c ∈ S, C (b c) * map (algebraMap K L) (q c), ?_⟩
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    rw [hq c hcS, map_mul]
    ring
  · rintro ⟨q, rfl⟩ j
    have hfR : X (Sum.inr j) * rename Sum.inl f ∈ R := (hK f).1 ((hf f).2 dvd_rfl) j
    have hmem := Ideal.mem_map_of_mem (map (algebraMap K L)) hfR
    rw [hmapX] at hmem
    rw [map_mul (rename Sum.inl), ← mul_assoc]
    exact Ideal.mul_mem_right _ _ hmem
end GroundTheory.Heights₂.Heights.ChowFormExtend
