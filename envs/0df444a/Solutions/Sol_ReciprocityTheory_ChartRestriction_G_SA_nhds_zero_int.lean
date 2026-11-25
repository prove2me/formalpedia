-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.nhds_zero_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:06.52412+00:00
-- url     : https://prove2.me/submissions/ab308dbf-e408-4f66-8dd7-22eafeda8c4c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_AdeleApproximation_AdeleIntA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_DenseRangeFiniteAdele
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_small_mem_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {N : Set (FiniteAdeleRing R K)} (hN : N ∈ 𝓝 (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v, Valued.v (y v) ≤ v.intValuation r) → y ∈ N := by
  have hBopen : ∀ v : HeightOneSpectrum R,
      IsOpen ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let mk : (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) → FiniteAdeleRing R K :=
    fun y => ⟨fun v => (y v : v.adicCompletion K), Eventually.of_forall fun v => (y v).2⟩
  have hmk : Continuous mk := by
    exact (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
      (A := fun v => ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)))
      (𝓕 := cofinite)).continuous
  have hmk0 : mk 0 = 0 := rfl
  have hpre : mk ⁻¹' N ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) :=
    hmk.continuousAt.preimage_mem_nhds (by rw [hmk0]; exact hN)
  rw [nhds_pi, mem_pi] at hpre
  obtain ⟨T, hT, t, ht, hsub⟩ := hpre
  have hloc : ∀ v, ∃ n : ℕ, ∀ x : v.adicCompletionIntegers K,
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    have hu0 : u ∈ 𝓝 (0 : v.adicCompletion K) := by simpa using hu
    obtain ⟨n, hn⟩ := small_mem_nhds v hu0
    exact ⟨n, fun x hx => hut (hn _ hx)⟩
  choose n hn using hloc
  let I : Ideal R := ∏ v ∈ hT.toFinset, v.asIdeal ^ (n v)
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨r, hr0, fun y hy => ?_⟩
  have hyint : ∀ v, y v ∈ v.adicCompletionIntegers K := fun v => by
    rw [mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  have hy' : y = mk (fun v => ⟨y v, hyint v⟩) := by ext v; rfl
  rw [hy']
  apply hsub
  intro v hv
  apply hn v
  refine (hy v).trans ?_
  rw [intValuation_le_pow_iff_mem]
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 hv)) hrI
end ReciprocityTheory.ChartRestriction.G.SA
