-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_algebraicIndependent_6f697c3a467f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:35.947801+00:00
-- url     : https://prove2.me/submissions/2169c991-d77f-4f22-85f2-03fa35ef4c7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_chartMonomial_isMultiHomog_d6818641190c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_6d9831913fb9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_chartMonomial_ne_zero_df5448a8cdab
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul


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
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι F)) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
theorem _root_.solution (hH : MChartHomog.Statement.{u}) (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    AlgebraicIndependent (chartMap P u).range (fun k => algebraMap (MRing ι F ⧸ P)
      (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))) := by
  classical
  set L := FractionRing (MRing ι F ⧸ P)
  set φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P) with hφ
  have hφapp : ∀ f, φ f = algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P f) := fun _ => rfl
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ m, ∃ q, chartMap P u q = ((p.coeff m : (chartMap P u).range) : L) := fun m => (p.coeff m).2
  choose q hq using hq
  choose b h hhom heq using fun m => hH F K ι u (q m)
  have hval : ∀ m, φ (h m) = ((p.coeff m : (chartMap P u).range) : L) * φ (chartMonomial u (b m)) := by
    intro m
    have := heq m P hu
    rw [hq m, eq_div_iff (map_chartMonomial_ne_zero P u hu _)] at this
    rw [hφapp, hφapp]
    exact this.symm
  set s := p.support
  set N : K → ℕ := ∑ m ∈ s, b m
  have hbN : ∀ m ∈ s, ∀ k, b m k ≤ N k := fun m hm =>
    Finset.single_le_sum (f := b) (fun _ _ _ => Nat.zero_le _) hm
  set c : (K →₀ ℕ) → K → ℕ := fun m => N - b m + ⇑m
  have hbc : ∀ m ∈ s, b m + c m = N + ⇑m := by
    intro m hm
    funext k
    have := hbN m hm k
    simp only [c, Pi.add_apply, Pi.sub_apply]
    omega

  set G := ∑ m ∈ s, h m * chartMonomial u (c m)
  have hG : G ∈ P := by
    rw [← map_eq_zero_iff, ← hφapp]
    have hp' := hp
    rw [aeval_def, eval₂_eq'] at hp'
    calc φ G = ∑ m ∈ s, φ (chartMonomial u N) * (algebraMap (chartMap P u).range L (p.coeff m) *
          ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ m k) := by
          simp only [G, map_sum, map_mul, hval]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hφapp (chartMonomial u (b m)), hφapp (chartMonomial u (c m)), hφapp (chartMonomial u N),
            map_chartMonomial, map_chartMonomial, map_chartMonomial]
          have e : ∀ x : K → L, (∏ k, x k ^ b m k) * (∏ k, x k ^ c m k) =
              (∏ k, x k ^ N k) * ∏ k, x k ^ m k := by
            intro x
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [← pow_add, ← pow_add]
            exact congrArg (x k ^ ·) (congrFun (hbc m hm) k)
          rw [mul_assoc, e, mul_left_comm]
          rfl
      _ = 0 := by rw [← Finset.mul_sum, hp', mul_zero]

  have hhomt : ∀ m ∈ s, IsMultiHomog (h m * chartMonomial u (c m)) (N + ⇑m) := by
    intro m hm
    unfold IsMultiHomog
    rw [← hbc m hm]
    exact IsWeightedHomogeneous.mul (hhom m) (chartMonomial_isMultiHomog u (c m))
  have hcomp : ∀ m ∈ s,
      weightedHomogeneousComponent (blockWeight ι) (N + ⇑m) G = h m * chartMonomial u (c m) := by
    intro m hm
    simp only [G, map_sum]
    rw [Finset.sum_eq_single m]
    · exact IsWeightedHomogeneous.weightedHomogeneousComponent_same (hhomt m hm)
    · intro m' hm' hne
      exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne (N + ⇑m) (hhomt m' hm')
        fun e => hne (DFunLike.coe_injective (add_left_cancel e)).symm
    · intro hms
      exact absurd hm hms

  have hzero : ∀ m ∈ s, p.coeff m = 0 := by
    intro m hm
    have hmem : h m * chartMonomial u (c m) ∈ P := hcomp m hm ▸ hP G hG (N + ⇑m)
    have hcm : chartMonomial u (c m) ∉ P := fun h' =>
      map_chartMonomial_ne_zero P u hu (c m) ((map_eq_zero_iff P _).2 h')
    have hh : h m ∈ P := (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hcm
    have h2 := hval m
    rw [hφapp, (map_eq_zero_iff P _).2 hh, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd h2 (map_chartMonomial_ne_zero P u hu (b m))
  ext m
  by_contra hne
  exact hne (by simpa using hzero m (mem_support_iff.2 (by simpa using hne)))
end GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
