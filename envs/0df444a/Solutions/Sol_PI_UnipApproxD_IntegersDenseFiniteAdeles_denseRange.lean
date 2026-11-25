-- Prove2me | solution 1 for PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:18.379792+00:00
-- url     : https://prove2.me/submissions/ff5be6ab-b985-4cb7-bd0e-335011664efb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_MemZeroLocusGLIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentApproximation_AddDense
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_approx
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_approx_adele
import Theorems.Thm_PI_UnipApproxD_IntegersDenseFiniteAdeles_exists_small_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnipApproxD PI.UnipApproxD.IntegersDenseFiniteAdeles
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace PI.UnipApproxD.IntegersDenseFiniteAdeles
theorem _root_.solution : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  classical
  intro x
  rw [mem_closure_iff_nhds]
  intro t ht
  have hc : Continuous (fun y : FiniteAdeleRing R K => x + y) := continuous_const.add continuous_id
  have h1 : (fun y : FiniteAdeleRing R K => x + y) ⁻¹' t ∈ nhds (0 : FiniteAdeleRing R K) :=
    hc.continuousAt.preimage_mem_nhds (by rwa [add_zero])
  have hAopen : ∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let z0 : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨0, (v.adicCompletionIntegers K).zero_mem⟩
  have h1' : ((fun y : FiniteAdeleRing R K => x + y) ⁻¹' t :
        Set (RestrictedProduct (fun v : HeightOneSpectrum R => v.adicCompletion K)
          (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite)) ∈
      nhds (RestrictedProduct.structureMap (fun v : HeightOneSpectrum R => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite z0) := h1
  rw [RestrictedProduct.nhds_eq_map_structureMap hAopen, Filter.mem_map, nhds_pi,
    Filter.mem_pi'] at h1'
  obtain ⟨I, u, hu, hIu⟩ := h1'
  have hW : ∀ v, ∃ W : Set (v.adicCompletion K), W ∈ nhds (0 : v.adicCompletion K) ∧
      ∀ y : v.adicCompletion K, (hy : y ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))) →
        y ∈ W → (⟨y, hy⟩ : (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∈ u v := by
    intro v
    obtain ⟨W, hW, hWu⟩ := (mem_nhds_subtype _ (z0 v) (u v)).mp (hu v)
    exact ⟨W, hW, fun y hy hyW => hWu hyW⟩
  choose W hW0 hWu using hW
  obtain ⟨r, hr, hsmall⟩ := exists_small_finset I W (fun v _ => hW0 v)
  obtain ⟨u0, hu0⟩ := exists_approx_adele x
  obtain ⟨a, ha⟩ := exists_approx _ hu0 r hr
  refine ⟨algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a), ?_, _, rfl⟩
  have ey : ∀ v : HeightOneSpectrum R,
      (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v =
        -((x - algebraMap K (FiniteAdeleRing R K) u0) v -
          algebraMap K (v.adicCompletion K) (algebraMap R K a)) := by
    intro v
    show algebraMap K (v.adicCompletion K) (u0 + algebraMap R K a) - x v =
      -((x v - algebraMap K (v.adicCompletion K) u0) - algebraMap K (v.adicCompletion K) (algebraMap R K a))
    rw [map_add]; ring
  have hval : ∀ v : HeightOneSpectrum R,
      Valued.v ((algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v) ≤ v.intValuation r := by
    intro v
    rw [ey, Valuation.map_neg]
    exact ha v
  have hint : ∀ v : HeightOneSpectrum R,
      (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v ∈
        (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    intro v
    rw [SetLike.mem_coe, mem_adicCompletionIntegers]
    exact (hval v).trans (v.intValuation_le_one r)
  let z : ∀ v : HeightOneSpectrum R, (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    fun v => ⟨(algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) v, hint v⟩
  have hz : z ∈ Set.pi (↑I) u := fun v hv => hWu v _ (hint v) (hsmall v hv _ (hval v))
  have hmem := hIu hz
  have e : x + (algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) - x) =
      algebraMap K (FiniteAdeleRing R K) (u0 + algebraMap R K a) := add_sub_cancel x _
  rw [← e]
  exact hmem
end PI.UnipApproxD.IntegersDenseFiniteAdeles
