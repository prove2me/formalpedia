-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlacesRingQuot_proof_69e5e1b0483c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:21.576177+00:00
-- url     : https://prove2.me/submissions/c9ae0d38-5103-47b0-85d6-d38071e8883f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRingQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlacesRingQuot

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
open NumberField
namespace GroundTheory.Heights₂.Heights
namespace PlacesRingQuot
theorem _root_.solution : PlacesRingQuot.Statement := by
  intro L _ _ S hS g hg
  classical
  set s := hS.toFinset with hs_def
  have hsS : ∀ w, w ∈ s ↔ w ∈ S := fun w ↦ hS.mem_toFinset
  have hgL : (g : L) ≠ 0 := fun h ↦ hg (Subtype.ext h)

  have hw : ∀ (w : FinitePlace L) (x : L), w x =
      ((WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero w.maximalIdeal)
        (w.maximalIdeal.valuation L x) : NNReal) : ℝ) := by
    intro w x
    rw [← FinitePlace.norm_embedding_eq, FinitePlace.norm_embedding']
  have hle : ∀ (w : FinitePlace L) (x y : L),
      w x ≤ w y ↔ w.maximalIdeal.valuation L x ≤ w.maximalIdeal.valuation L y := by
    intro w x y
    rw [hw, hw, NNReal.coe_le_coe,
      (WithZeroMulInt.toNNReal_strictMono
        (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w.maximalIdeal)).le_iff_le]
  have hle1 : ∀ (w : FinitePlace L) (x : L), w x ≤ 1 ↔ w.maximalIdeal.valuation L x ≤ 1 := by
    intro w x
    rw [← map_one w, hle, map_one]

  have hn : ∀ w : FinitePlace L, ∃ n : ℕ,
      w ∈ S → w.maximalIdeal.valuation L g = WithZero.exp (-(n : ℤ)) := by
    intro w
    by_cases hwS : w ∈ S
    · have h0 : w.maximalIdeal.valuation L g ≠ 0 := (Valuation.ne_zero_iff _).2 hgL
      have h1 : WithZero.log (w.maximalIdeal.valuation L g) ≤ 0 := by
        rw [WithZero.log_le_iff_le_exp h0, WithZero.exp_zero]
        exact (hle1 w g).1 (g.2 w hwS)
      refine ⟨(-WithZero.log (w.maximalIdeal.valuation L g)).toNat, fun _ ↦ ?_⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
    · exact ⟨0, fun h ↦ absurd h hwS⟩
  choose n hn using hn

  have key : ∀ z : placesRing S, z ∈ Ideal.span {g} ↔
      ∀ w ∈ S, w.maximalIdeal.valuation L z ≤ w.maximalIdeal.valuation L g := by
    intro z
    constructor
    · intro h w hwS
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 h
      have hr : w.maximalIdeal.valuation L r ≤ 1 := (hle1 w r).1 (r.2 w hwS)
      rw [Subring.coe_mul, map_mul]
      calc w.maximalIdeal.valuation L r * w.maximalIdeal.valuation L g
          ≤ 1 * w.maximalIdeal.valuation L g := mul_le_mul_left hr _
        _ = w.maximalIdeal.valuation L g := one_mul _
    · intro h
      refine Ideal.mem_span_singleton'.2 ⟨⟨z * (g : L)⁻¹, fun w hwS ↦ ?_⟩, Subtype.ext ?_⟩
      · have h0 : w.maximalIdeal.valuation L g ≠ 0 := (Valuation.ne_zero_iff _).2 hgL
        rw [hle1, map_mul, map_inv₀]
        exact (mul_inv_le_iff₀ (zero_lt_iff.2 h0)).2 (by simpa using h w hwS)
      · simp [hgL]

  let ι : 𝓞 L →+* placesRing S := (algebraMap (𝓞 L) L).codRestrict (placesRing S) fun a w _ ↦ by
    rw [← FinitePlace.norm_embedding_eq]
    exact FinitePlace.norm_le_one _ _ a
  have hι : ∀ a : 𝓞 L, ((ι a : placesRing S) : L) = algebraMap (𝓞 L) L a := fun _ ↦ rfl
  have hprime : ∀ w ∈ s, Prime (w.maximalIdeal.asIdeal) := fun w _ ↦ w.maximalIdeal.prime
  have hcop : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → i.maximalIdeal ≠ j.maximalIdeal :=
    fun i _ j _ hij h ↦ hij (FinitePlace.maximalIdeal_injective h)
  have hcop' : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → i.maximalIdeal.asIdeal ≠ j.maximalIdeal.asIdeal :=
    fun i hi j hj hij h ↦ hcop i hi j hj hij (IsDedekindDomain.HeightOneSpectrum.asIdeal_injective h)
  let φ : 𝓞 L →+* placesRing S ⧸ Ideal.span {g} := (Ideal.Quotient.mk _).comp ι

  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    have ha : ∀ w : s, ∃ a : 𝓞 L, w.1.maximalIdeal.valuation L (algebraMap (𝓞 L) L a - x) <
        w.1.maximalIdeal.valuation L g := fun w ↦ by
      have h0 : w.1.maximalIdeal.valuation L g ≠ 0 := (Valuation.ne_zero_iff _).2 hgL
      simpa using IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
        w.1.maximalIdeal ((hle1 w.1 x).1 (x.2 w.1 ((hsS w.1).1 w.2))) (Units.mk0 _ h0)
    choose a ha using ha
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
      (fun w : FinitePlace L ↦ w.maximalIdeal.asIdeal) n hprime hcop' a
    refine ⟨y, ?_⟩
    show Ideal.Quotient.mk _ (ι y) = _
    rw [Ideal.Quotient.eq, key]
    intro w hwS
    have hws : w ∈ s := (hsS w).2 hwS
    have h1 : w.maximalIdeal.valuation L (algebraMap (𝓞 L) L (y - a ⟨w, hws⟩)) ≤
        w.maximalIdeal.valuation L g := by
      rw [hn w hwS, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact hy w hws
    have h2 := (ha ⟨w, hws⟩).le
    have he : ((ι y - x : placesRing S) : L) =
        algebraMap (𝓞 L) L (y - a ⟨w, hws⟩) + (algebraMap (𝓞 L) L (a ⟨w, hws⟩) - x) := by
      simp only [AddSubgroupClass.coe_sub, hι, map_sub]
      ring
    rw [he]
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)

  have hker : RingHom.ker φ = ∏ w ∈ s, w.maximalIdeal.asIdeal ^ n w := by
    rw [← IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod s n (fun w ↦ w.maximalIdeal) hcop]
    ext a
    rw [RingHom.mem_ker, show φ a = Ideal.Quotient.mk _ (ι a) from rfl,
      Ideal.Quotient.eq_zero_iff_mem, key, Submodule.mem_finsetInf]
    refine forall_congr' fun w ↦ ?_
    rw [hsS]
    refine imp_congr_right fun hwS ↦ ?_
    rw [hι, hn w hwS, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
  have hcard : Nat.card (placesRing S ⧸ Ideal.span {g}) =
      ∏ w ∈ s, Ideal.absNorm w.maximalIdeal.asIdeal ^ n w := by
    rw [← Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv, hker,
      ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_prod]
    simp only [map_pow]
  rw [hcard, finsum_mem_eq_finite_toFinset_sum _ hS, ← hs_def]
  push_cast
  rw [Real.log_prod fun w _ ↦ pow_ne_zero _ (by
    exact_mod_cast (Nat.zero_lt_of_lt
      (NumberField.HeightOneSpectrum.one_lt_absNorm w.maximalIdeal)).ne')]
  refine Finset.sum_congr rfl fun w hws ↦ ?_
  have h0 : WithZero.exp (-(n w : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [Real.log_pow, hw, hn w ((hsS w).1 hws), WithZeroMulInt.toNNReal_neg_apply _ h0,
    WithZero.toAdd_unzero_eq_log, WithZero.log_exp]
  simp [Real.log_zpow]
end PlacesRingQuot
end GroundTheory.Heights₂.Heights
