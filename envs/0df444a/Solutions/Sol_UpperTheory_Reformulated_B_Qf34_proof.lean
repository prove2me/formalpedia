-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qf34.proof
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:01.287634+00:00
-- url     : https://prove2.me/submissions/9a3f1f00-4660-4518-9e38-b2fee2fd3779

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GenericGradient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.taylor {k B : Type*} [CommRing k] [CommRing B] [Algebra k B]
    {n : ℕ} (φ ψ : MvPolynomial (Fin n) k →ₐ[k] B)
    (h : ∀ p q, (φ p - ψ p) * (φ q - ψ q) = 0) (p : MvPolynomial (Fin n) k) :
    φ p - ψ p = ∑ l, φ (pderiv l p) * (φ (X l) - ψ (X l)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algHom_C]
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, ← hp, ← hq]
    ring
  | mul_X p i hp =>
    have e : ∀ l, φ (pderiv l (p * X i)) * (φ (X l) - ψ (X l)) =
        φ (X i) * (φ (pderiv l p) * (φ (X l) - ψ (X l))) +
          (if l = i then φ p * (φ (X i) - ψ (X i)) else 0) := by
      intro l
      rw [pderiv_mul, map_add, map_mul, map_mul]
      split_ifs with hl
      · subst hl
        rw [pderiv_X_self, map_one]
        ring
      · rw [pderiv_X_of_ne (Ne.symm hl), map_zero]
        ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← hp, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_mul]
    linear_combination - h p (X i)
open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.sq_zero_case {k B K ι : Type*} [CommRing k] [CommRing B]
    [Algebra k B] [CommRing K] [Algebra k K] [Fintype ι] {n : ℕ}
    (π : B →ₐ[k] K) (σ : K →ₐ[k] B) (hσ : ∀ x, π (σ x) = x)
    (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0)
    (φ : MvPolynomial (Fin n) k →ₐ[k] B) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p = ∑ i, σ (c i) * φ (f i) := by
  have hd : ∀ q, π (φ q - (σ.comp (π.comp φ)) q) = 0 := by
    intro q
    simp [hσ]
  have ht := UpperTheory.Reformulated.B.Qf34.taylor φ (σ.comp (π.comp φ)) fun p q => hsq _ _ (hd p) (hd q)
  have ht' : ∀ q, π (φ q) = 0 →
      φ q = ∑ l, φ (pderiv l q) * (φ (X l) - (σ.comp (π.comp φ)) (X l)) := by
    intro q hq
    rw [← ht q]
    simp [hq]
  rw [ht' p hp, Finset.sum_congr rfl fun i _ => congrArg (σ (c i) * ·) (ht' _ (hf i))]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← sub_eq_zero, ← sub_mul]
  refine hsq _ _ ?_ (hd _)
  simp [hσ, hc]
open MvPolynomial in
private theorem UpperTheory.Reformulated.B.Qf34.mem_sup_sq {k A K ι : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [CommRing K] [Algebra k K] [Algebra.FormallySmooth k K] [Fintype ι] {n : ℕ}
    (π : A →ₐ[k] K) (hπ : Function.Surjective π)
    (φ : MvPolynomial (Fin n) k →ₐ[k] A) (p : MvPolynomial (Fin n) k)
    (f : ι → MvPolynomial (Fin n) k) (c : ι → K) (hp : π (φ p) = 0) (hf : ∀ i, π (φ (f i)) = 0)
    (hc : ∀ l, π (φ (pderiv l p)) = ∑ i, c i * π (φ (pderiv l (f i)))) :
    φ p ∈ Ideal.span (Set.range fun i => φ (f i)) ⊔ RingHom.ker π * RingHom.ker π := by
  set m : Ideal A := RingHom.ker π with hm
  let π' : (A ⧸ m * m) →ₐ[k] K := Ideal.Quotient.liftₐ (m * m) π fun a ha => Ideal.mul_le_left ha
  have hπ' : ∀ a, π' (Ideal.Quotient.mk _ a) = π a := fun a => rfl
  have hs : Function.Surjective π' := fun x => by
    obtain ⟨a, rfl⟩ := hπ x
    exact ⟨_, hπ' a⟩
  have hsq : ∀ a b, π' a = 0 → π' b = 0 → a * b = 0 := by
    intro a b ha hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_mul ha hb
  have hn : IsNilpotent (RingHom.ker (π' : (A ⧸ m * m) →+* K)) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    exact hsq a b ha hb
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k K) π' hs hn
  have hσ : ∀ x, π' (σ x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id k K) π' hs hn
  have key := UpperTheory.Reformulated.B.Qf34.sq_zero_case π' σ hσ hsq ((Ideal.Quotient.mkₐ k (m * m)).comp φ)
    p f c hp hf hc
  choose a ha using fun i => Ideal.Quotient.mk_surjective (I := m * m) (σ (c i))
  have h2 : φ p - ∑ i, a i * φ (f i) ∈ m * m := by
    rw [← Ideal.Quotient.eq, map_sum]
    simpa [← ha] using key
  rw [← add_sub_cancel (∑ i, a i * φ (f i)) (φ p)]
  refine Submodule.add_mem_sup (Ideal.sum_mem _ fun i _ => ?_) h2
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qf34
theorem _root_.solution :
    UpperTheory.Reformulated.B.Qf34.Statement := by
  intro n J _ ι _ f hf hspan
  let R := MvPolynomial (Fin n) ℂ
  let K := FractionRing (R ⧸ J)
  let A := Localization.AtPrime J
  let g : R →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ (R ⧸ J) K).comp (Ideal.Quotient.mkₐ ℂ J)
  have hg : ∀ r, g r = algebraMap (R ⧸ J) K (Ideal.Quotient.mk J r) := fun r => rfl
  have hg0 : ∀ r, g r = 0 ↔ r ∈ J := fun r => by
    rw [hg, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ J) K), Ideal.Quotient.eq_zero_iff_mem]
  have hu : ∀ y : J.primeCompl, IsUnit (g y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h => y.2 ((hg0 _).mp h)
  let π : A →ₐ[ℂ] K := IsLocalization.liftAlgHom (M := J.primeCompl) hu
  let φ : R →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ R A
  have hπφ : ∀ r, π (φ r) = g r := fun r => IsLocalization.lift_eq hu r
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (R ⧸ J) x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' : b ∈ J.primeCompl := fun h =>
      nonZeroDivisors.ne_zero hb (Ideal.Quotient.eq_zero_iff_mem.mpr h)
    refine ⟨IsLocalization.mk' A a ⟨b, hb'⟩, ?_⟩
    rw [← hg, ← hg, eq_div_iff (hu ⟨b, hb'⟩).ne_zero, ← hπφ, ← hπφ, ← map_mul]
    exact congrArg π (IsLocalization.mk'_spec A a ⟨b, hb'⟩)
  haveI : Algebra.EssFiniteType (R ⧸ J) K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors (R ⧸ J))
  haveI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ (R ⧸ J) K
  haveI : Algebra.FormallySmooth ℂ K := Algebra.FormallySmooth.of_perfectField
  have hker : RingHom.ker π = IsLocalRing.maximalIdeal A :=
    IsLocalRing.ker_eq_maximalIdeal (π : A →+* K) hπ
  have hN : IsLocalRing.maximalIdeal A ≤ (Ideal.span (Set.range f)).map (algebraMap R A) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    conv_lhs => rw [← Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    have hmem : UpperTheory.Reformulated.B.Qf34.genericGradient J p ∈
        Submodule.span K (Set.range (UpperTheory.Reformulated.B.Qf34.genericGradient J ∘ f)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨p, hp, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    have := UpperTheory.Reformulated.B.Qf34.mem_sup_sq π hπ φ p f c (by rw [hπφ, hg0]; exact hp)
      (fun i => by rw [hπφ, hg0]; exact hf i) (fun l => by
        have h := congrFun hc l
        rw [Finset.sum_apply] at h
        simp only [hπφ]
        exact h.symm)
    rw [hker] at this
    rw [Ideal.mem_comap, Ideal.map_span, ← Set.range_comp, smul_eq_mul]
    exact this
  obtain ⟨t, ht⟩ : J.FG := IsNoetherian.noetherian J
  have hs : ∀ p ∈ J, ∃ s ∈ J.primeCompl, s * p ∈ Ideal.span (Set.range f) := by
    intro p hp
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff J.primeCompl A]
    apply hN
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hp
  choose! s hs hs' using hs
  have htJ : ∀ p ∈ t, p ∈ J := fun p hp => ht ▸ Ideal.subset_span hp
  refine ⟨∏ p ∈ t, s p, Submonoid.prod_mem J.primeCompl fun p hp => hs p (htJ p hp), ?_⟩
  intro p hp
  rw [← ht] at hp
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem s hx
    rw [hu, mul_comm (s x), mul_assoc]
    exact Ideal.mul_mem_left _ _ (hs' x (htJ x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
end UpperTheory.Reformulated.B.Qf34
