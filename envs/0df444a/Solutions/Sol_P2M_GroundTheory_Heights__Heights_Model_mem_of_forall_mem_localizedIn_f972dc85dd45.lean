-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_of_forall_mem_localizedIn_f972dc85dd45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:40.654188+00:00
-- url     : https://prove2.me/submissions/70e38b4f-fd41-4323-814f-e6d799790333

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PLatticesAgree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_ne_zero_smul_mem_of_span_eq_top_cc22f24e7b75
import Theorems.Thm_UpperTheory_Reformulated_B_SmulMemOfSpanEqTop_exists_ne_zero_smul_mem_of_span_eq_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
variable {A : Type} [CommRing A] [IsDomain A]
  {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (hHOI : HeightOneIntersection.Statement)
    [IsNoetherianRing A] [IsIntegrallyClosed A] (M : Submodule A V) [Module.Projective A M]
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V)
    (hv : ∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → v ∈ localizedIn p.asIdeal M) : v ∈ M := by
  obtain ⟨d, hd, hdv⟩ := exists_ne_zero_smul_mem_of_span_eq_top (K := K) M hM v
  obtain ⟨c, hc⟩ := Module.projective_def.mp (inferInstance : Module.Projective A M)
  set x : M := ⟨d • v, hdv⟩ with hx
  have hdK : algebraMap A K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hd

  have hdiv : ∀ y : M, ∃ a : A, c x y = d * a := by
    intro y
    have hq : algebraMap A K (c x y) / algebraMap A K d ∈
        Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
      rw [hHOI A K]
      simp only [Submodule.mem_iInf]
      intro p hp
      obtain ⟨s, hs, hsv⟩ := hv p hp
      refine ⟨s, hs, ?_⟩
      set x' : M := ⟨s • v, hsv⟩
      have hxx : d • x' = s • x := by
        ext; simp only [x', hx, SetLike.val_smul, smul_smul, mul_comm]
      have hcc : d * c x' y = s * c x y := by
        have := congrArg (fun z => c z y) hxx
        simpa [map_smul] using this
      refine Algebra.mem_bot.mpr ⟨c x' y, ?_⟩
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, ← hcc, map_mul,
        mul_div_right_comm, div_self hdK, one_mul]
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hq
    refine ⟨a, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ha, mul_div_cancel₀ _ hdK]
  choose a ha using hdiv
  have hw : (∑ y ∈ (c x).support, a y • (y : V)) ∈ M :=
    M.sum_mem fun y _ => M.smul_mem (a y) y.2
  have hsum : d • v = d • ∑ y ∈ (c x).support, a y • (y : V) := by
    have h1 : ((Finsupp.linearCombination A id (c x) : M) : V) = d • v := by rw [hc x]
    rw [← h1, Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Submodule.coe_smul, id, ha y, mul_smul]
  have hvw : v = ∑ y ∈ (c x).support, a y • (y : V) := by
    rw [← algebraMap_smul K d v, ← algebraMap_smul K d (∑ y ∈ (c x).support, a y • (y : V))]
      at hsum
    exact smul_right_injective V hdK hsum
  rw [hvw]
  exact hw
end GroundTheory.Heights₂.Heights.Model
