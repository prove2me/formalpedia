-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_proof_2fa9ef6b5246
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:52.084967+00:00
-- url     : https://prove2.me/submissions/26a30f43-45f1-46a7-8ede-b91085f77446

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_isMultiHomog_iff_06eee657011e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mem_5ccd5932e898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_exists_component_not_mem_acd119a4b79d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_right_0c0b5ca4a739
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingPow_component_mul_of_not_le_458ee4a08c44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_pow_d8f8cabc5022


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing
noncomputable section
open LocRingPow
namespace GroundTheory.Heights₂.Heights.Inter
namespace LocRingPow
theorem _root_.solution : LocRingPow.Statement := by
  classical
  intro K _ ι _ P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hy
  have := hPp
  obtain ⟨hWmin, -⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2

  obtain ⟨n, d, hdW, hd⟩ : ∃ n : ℕ, ∃ d ∉ W, d * u ^ n ∈ P ⊔ Ideal.span {s} := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W _ hWmin
    have hu' : algebraMap (MRing ι) (Localization.AtPrime W) u ∈
        ((P ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).radical :=
      hrad ▸ Ideal.mem_map_of_mem _ huW
    obtain ⟨n, hn⟩ := hu'
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at hn
    obtain ⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, he⟩ := hn
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at he
    obtain ⟨⟨e, he'⟩, hee⟩ := he
    refine ⟨n, e * c, W.primeCompl.mul_mem he' hc, ?_⟩
    have : e * c * u ^ n = e * (u ^ n * c) := by ring
    rw [this, hee]
    exact Ideal.mul_mem_left _ _ hi

  obtain ⟨e, he⟩ := exists_component_not_mem hdW
  set ce := weightedHomogeneousComponent (multiDegWeight ι) e d with hce_def
  have hce : IsMultiHomog ce e :=
    isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hd
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hq

  set D : K → ℕ := e + n • b with hD
  have h1 : weightedHomogeneousComponent (multiDegWeight ι) D (d * u ^ n) = ce * u ^ n :=
    component_mul_right (isMultiHomog_iff.mp (isMultiHomog_pow hu n))
  obtain ⟨G, hG, hGs⟩ : ∃ G : MRing ι, IsMultiHomog (G * t) D ∧
      weightedHomogeneousComponent (multiDegWeight ι) D (g * s) = G * s := by
    by_cases hle : a ≤ D
    · refine ⟨weightedHomogeneousComponent (multiDegWeight ι) (D - a) g, ?_, ?_⟩
      · have := isMultiHomog_mul
          (isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - a) g)) ht
        rwa [tsub_add_cancel_of_le hle] at this
      · conv_lhs => rw [← tsub_add_cancel_of_le hle]
        exact component_mul_right (isMultiHomog_iff.mp hs)
    · exact ⟨0, fun m hm => by simp at hm,
        by rw [zero_mul]; exact component_mul_of_not_le (isMultiHomog_iff.mp hs) hle⟩
  have hrel : ce * u ^ n - G * s ∈ P := by
    have := component_mem hPh hp D
    rwa [← add_sub_cancel_right p (g * s), hpq, map_sub, h1, hGs] at this

  have hden : ce * v ^ n ∉ W := fun h =>
    (hWp.mem_or_mem h).elim he fun h => hvW (hWp.mem_of_pow_mem _ h)
  have hdenP : Ideal.Quotient.mk P (ce * v ^ n) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hden (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  refine ⟨n, IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (G * t)) ⟨_, hdenP⟩,
    Subring.subset_closure ⟨G * t, ce * v ^ n, D, hdenP, hden, hG, isMultiHomog_mul hce (isMultiHomog_pow hv n), rfl⟩,
    ?_⟩
  have hne : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (ce * v ^ n)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdenP
  apply mul_right_cancel₀ hne
  rw [mul_assoc x, IsLocalization.mk'_spec]
  have key := congrArg (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))) (Ideal.Quotient.eq.mpr hrel)
  simp only [map_mul, map_pow] at key hx hy ⊢
  calc y ^ n * (algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P v) ^ n)
      = algebraMap _ _ (Ideal.Quotient.mk P ce) * (y * algebraMap _ _ (Ideal.Quotient.mk P v)) ^ n := by ring
    _ = algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P u) ^ n := by rw [hy]
    _ = algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P s) := key
    _ = x * (algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P t)) := by
        rw [← hx]; ring
end LocRingPow
end GroundTheory.Heights₂.Heights.Inter
