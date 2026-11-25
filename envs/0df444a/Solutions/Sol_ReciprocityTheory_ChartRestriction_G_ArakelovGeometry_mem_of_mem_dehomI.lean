-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mem_of_mem_dehomI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:46.376028+00:00
-- url     : https://prove2.me/submissions/308a45b1-ce9a-4d95-bd96-7876862ea4a9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {W : Ideal (MRing ι)} (hWp : W.IsPrime) (hWm : IsMultiHomogIdeal W)
    {i : ∀ k, ι k} (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ W) {a : K → ℕ} {s : MRing ι}
    (hs : IsMultiHomog s a) (hsI : s ∈ dehomI W i) : s ∈ W := by
  classical
  haveI : W.IsPrime := hWp
  obtain ⟨F, _, q, hq⟩ : ∃ (F : Type) (_ : Field F) (q : MRing ι →+* F), ∀ f, q f = 0 ↔ f ∈ W :=
    ⟨FractionRing (MRing ι ⧸ W), inferInstance, (algebraMap (MRing ι ⧸ W) _).comp (Ideal.Quotient.mk W),
      fun f => by
        rw [RingHom.comp_apply, show (0 : FractionRing (MRing ι ⧸ W)) = algebraMap (MRing ι ⧸ W) _ 0 from
          (map_zero _).symm, (IsFractionRing.injective (MRing ι ⧸ W) _).eq_iff,
          Ideal.Quotient.eq_zero_iff_mem]⟩
  have hc : ∀ k, q (X ⟨k, i k⟩) ≠ 0 := fun k h => hi k ((hq _).1 h)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : MRing ι →+* F,
      Θ = MvPolynomial.eval₂Hom (Int.castRingHom F) (fun p => q (X p) / q (X ⟨p.1, i p.1⟩)) := ⟨_, rfl⟩

  have hqm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ),
      q (monomial m c) = (c : F) * ∏ p ∈ m.support, q (X p) ^ m p := by
    intro m c
    rw [MvPolynomial.monomial_eq, map_mul]
    simp only [Finsupp.prod, map_prod, map_pow]
    congr 1
    exact eq_intCast (q.comp MvPolynomial.C) c
  have hΘm : ∀ (m : ((k : K) × ι k) →₀ ℕ) (c : ℤ),
      Θ (monomial m c) = (c : F) * ∏ p ∈ m.support, (q (X p) / q (X ⟨p.1, i p.1⟩)) ^ m p := by
    intro m c
    rw [hΘ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, eq_intCast]
    rfl

  have key : ∀ (f : MRing ι) (d : K → ℕ), IsMultiHomog f d →
      Θ f * ∏ k, q (X ⟨k, i k⟩) ^ d k = q f := by
    intro f d hf
    have hC : ∏ k, q (X ⟨k, i k⟩) ^ d k ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hcm : ∏ p ∈ m.support, q (X ⟨p.1, i p.1⟩) ^ m p = ∏ k, q (X ⟨k, i k⟩) ^ d k := by
      rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
        rw [Finsupp.mem_support_iff, not_not] at hp
        rw [hp, pow_zero]), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp only
      rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
    rw [hΘm, hqm]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, hcm, mul_assoc, div_mul_cancel₀ _ hC]
  have hW : W ≤ RingHom.ker Θ := by
    obtain ⟨S, hS, hWS⟩ := hWm
    intro w hw
    have hw' : w ∈ Ideal.span S := hWS ▸ hw
    refine (Ideal.span_le.mpr ?_) hw'
    intro f hf
    rw [SetLike.mem_coe, RingHom.mem_ker]
    obtain ⟨d, hd⟩ := hS f hf
    have h1 := key f d hd
    have h2 : q f = 0 := (hq f).2 (by rw [hWS]; exact Ideal.subset_span hf)
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_right
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  have hJ : ∀ k, Θ ((X ⟨k, i k⟩ : MRing ι) - 1) = 0 := by
    intro k
    rw [map_sub, map_one, hΘ, MvPolynomial.eval₂Hom_X', div_self (hc k), sub_self]
  have hle : W ⊔ Ideal.span (Set.range fun k => (X ⟨k, i k⟩ : MRing ι) - 1) ≤ RingHom.ker Θ :=
    sup_le hW (Ideal.span_le.mpr (by
      rintro _ ⟨k, rfl⟩
      exact RingHom.mem_ker.mpr (hJ k)))
  have hΘs : Θ s = 0 := RingHom.mem_ker.mp (hle hsI)
  have h := key s a hs
  rw [hΘs, zero_mul] at h
  exact (hq s).1 h.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
