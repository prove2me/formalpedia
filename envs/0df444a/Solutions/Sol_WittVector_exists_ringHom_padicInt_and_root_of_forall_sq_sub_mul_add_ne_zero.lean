-- Prove2me | solution 1 for WittVector.exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/9b24ed42-1a57-5a0a-ac3f-86d9c050d804

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero

set_option autoImplicit false

namespace WittCoord

open Polynomial

section Residue

variable (p : ℕ) [Fact p.Prime] (t n : ℤ)

noncomputable def g : (ZMod p)[X] := X ^ 2 + C (-(t : ZMod p)) * X + C (n : ZMod p)

theorem g_eval (x : ZMod p) : (g p t n).eval x = x ^ 2 - (t : ZMod p) * x + (n : ZMod p) := by
  simp [g]; ring

theorem g_natDegree : (g p t n).natDegree = 2 := by
  unfold g; compute_degree!

theorem g_monic : (g p t n).Monic := by
  unfold g; monicity!

theorem g_irreducible (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) : Irreducible (g p t n) := by
  rw [(g_monic p t n).irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [g_natDegree]) (by rw [g_natDegree]; norm_num)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  rw [mem_roots (g_monic p t n).ne_zero, IsRoot, g_eval] at hx
  exact hirr x hx

theorem g_aeval {A : Type*} [CommRing A] [Algebra (ZMod p) A] (x : A) :
    aeval x (g p t n) = x ^ 2 - (t : A) * x + (n : A) := by
  simp [g, map_neg, map_intCast]; ring

theorem exists_root_galoisField (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) :
    ∃ ω : GaloisField p 2, ω ^ 2 - (t : GaloisField p 2) * ω + (n : GaloisField p 2) = 0 ∧
      ∀ z : GaloisField p 2, ∃ c d : ZMod p,
        z = algebraMap (ZMod p) (GaloisField p 2) c + algebraMap (ZMod p) (GaloisField p 2) d * ω := by
  classical
  haveI hirr' : Fact (Irreducible (g p t n)) := ⟨g_irreducible p t n hirr⟩
  let L := AdjoinRoot (g p t n)
  let pb := AdjoinRoot.powerBasis (g_monic p t n).ne_zero
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis_dim, g_natDegree]
  haveI : Module.Finite (ZMod p) L := pb.finite
  haveI : Finite L := Module.finite_of_finite (ZMod p)
  have hcard : Nat.card L = p ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := L), Nat.card_zmod]
    congr 1
    exact pb.finrank.trans hdim
  let e : L ≃ₐ[ZMod p] GaloisField p 2 := GaloisField.algEquivGaloisField p 2 hcard
  refine ⟨e (AdjoinRoot.root (g p t n)), ?_, ?_⟩
  · have h0 : aeval (AdjoinRoot.root (g p t n)) (g p t n) = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have h1 : aeval ((e : L →ₐ[ZMod p] GaloisField p 2) (AdjoinRoot.root (g p t n))) (g p t n) = 0 := by
      rw [aeval_algHom_apply, h0, map_zero]
    rw [AlgEquiv.coe_algHom, g_aeval] at h1
    exact h1
  · intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    induction y using AdjoinRoot.induction_on with
    | ih q =>
      have hq : AdjoinRoot.mk (g p t n) q = AdjoinRoot.mk (g p t n) (q %ₘ g p t n) := by
        rw [AdjoinRoot.mk_eq_mk]
        exact ⟨q /ₘ g p t n, by linear_combination (-1 : (ZMod p)[X]) * modByMonic_add_div q (g p t n)⟩
      have hdeg : (q %ₘ g p t n).degree ≤ 1 := by
        have h := degree_modByMonic_lt q (g_monic p t n)
        rw [degree_eq_natDegree (g_monic p t n).ne_zero, g_natDegree] at h
        exact Order.le_of_lt_succ (by exact_mod_cast h)
      set r := q %ₘ g p t n with hr
      rw [eq_X_add_C_of_degree_le_one hdeg] at hq
      refine ⟨r.coeff 0, r.coeff 1, ?_⟩
      rw [hq]
      simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq]
      rw [AlgEquiv.commutes, AlgEquiv.commutes]
      ring

end Residue

section Witt

variable (p : ℕ) [Fact p.Prime]

local notation "𝕂" => GaloisField p 2
local notation "𝕎₂" => WittVector p (GaloisField p 2)

theorem mem_range_algebraMap_of_pow_eq (x : GaloisField p 2) (hx : x ^ p = x) :
    ∃ c : ZMod p, algebraMap (ZMod p) (GaloisField p 2) c = x := by
  classical
  have hp : p.Prime := Fact.out
  set P : (GaloisField p 2)[X] := X ^ p - X with hP
  have hP0 : P ≠ 0 := by
    rw [hP]; apply_fun Polynomial.natDegree
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp.one_lt]
    exact hp.ne_zero
  have hdegP : P.natDegree = p := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp.one_lt]

  let S : Finset (GaloisField p 2) := Finset.univ.image (algebraMap (ZMod p) (GaloisField p 2))
  have hScard : S.card = p := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) (GaloisField p 2)).injective, Finset.card_univ, ZMod.card]
  have hSroots : S ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, hP, eval_sub, eval_pow, eval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hle : P.roots.toFinset.card ≤ p := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ = p := hdegP
  have hSeq : S = P.roots.toFinset := Finset.eq_of_subset_of_card_le hSroots (by rw [hScard]; exact hle)
  have hxroot : x ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, hP, eval_sub, eval_pow, eval_X, hx, sub_self]
  rw [← hSeq] at hxroot
  obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hxroot
  exact ⟨c, hc⟩

end Witt

end WittCoord

open WittCoord Polynomial in
theorem solution
    (p : ℕ) [Fact p.Prime] (t n : ℤ)
    (hirr : ∀ x : ZMod p, x ^ 2 - (t : ZMod p) * x + (n : ZMod p) ≠ 0) :
    ∃ (ι : ℤ_[p] →+* WittVector p (GaloisField p 2)) (ω : WittVector p (GaloisField p 2)),
      (∀ c : ℤ_[p], WittVector.frobenius (ι c) = ι c) ∧
      ω * ω = (t : WittVector p (GaloisField p 2)) * ω - (n : WittVector p (GaloisField p 2)) ∧
      WittVector.frobenius ω = (t : WittVector p (GaloisField p 2)) - ω ∧
      (∀ c d : ℤ_[p], ι c + ι d * ω = 0 → c = 0 ∧ d = 0) ∧
      (∀ (k : ℕ) (x : WittVector p (GaloisField p 2)), ∃ c d : ℤ,
        x - ((c : WittVector p (GaloisField p 2)) + (d : WittVector p (GaloisField p 2)) * ω) ∈
          Ideal.span {((p : WittVector p (GaloisField p 2))) ^ k}) := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨ωb, hωb, hspan⟩ := exists_root_galoisField p t n hirr

  have hωb_not : ∀ c : ZMod p, algebraMap (ZMod p) (GaloisField p 2) c ≠ ωb := by
    intro c hc
    apply hirr c
    apply (algebraMap (ZMod p) (GaloisField p 2)).injective
    rw [map_add, map_sub, map_mul, map_pow, hc, map_intCast, map_intCast, map_zero]; exact hωb

  have h2ωb : (2 : GaloisField p 2) * ωb - (t : GaloisField p 2) ≠ 0 := by
    intro h0
    by_cases h2 : (2 : ZMod p) = 0
    ·
      have hp2 : p = 2 := by
        have : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h2)
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      subst hp2
      have ht0 : (t : ZMod 2) = 0 := by
        have : (t : GaloisField 2 2) = 0 := by
          have : (2 : GaloisField 2 2) = 0 := by
            have h := congrArg (algebraMap (ZMod 2) (GaloisField 2 2)) h2; rwa [map_ofNat, map_zero] at h
          rw [this, zero_mul, zero_sub, neg_eq_zero] at h0; exact h0
        apply (algebraMap (ZMod 2) (GaloisField 2 2)).injective
        rw [map_intCast, map_zero]; exact this
      apply hirr (n : ZMod 2)
      rw [ht0, zero_mul, sub_zero]
      have key : ∀ x : ZMod 2, x ^ 2 + x = 0 := by intro x; fin_cases x <;> rfl
      exact key _
    · have h2ne : (2 : GaloisField p 2) ≠ 0 := fun h => h2 (by
        apply (algebraMap (ZMod p) (GaloisField p 2)).injective; rw [map_ofNat, map_zero]; exact h)
      apply hωb_not ((t : ZMod p) / 2)
      rw [map_div₀, map_intCast, map_ofNat, div_eq_iff h2ne]
      linear_combination (-1 : GaloisField p 2) * h0

  let ι : ℤ_[p] →+* WittVector p (GaloisField p 2) :=
    (WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp (WittVector.equiv p).symm.toRingHom
  have hιfix : ∀ c : ℤ_[p], WittVector.frobenius (ι c) = ι c := by
    intro c
    ext m
    simp only [ι, RingHom.coe_comp, Function.comp_apply, WittVector.coeff_frobenius_charP, WittVector.map_coeff, ← map_pow,
      ZMod.pow_card]
  have hιinj : Function.Injective ι :=
    (WittVector.map_injective _ (algebraMap (ZMod p) (GaloisField p 2)).injective).comp (WittVector.equiv p).symm.injective

  let f : (WittVector p (GaloisField p 2))[X] :=
    X ^ 2 - C ((t : WittVector p (GaloisField p 2))) * X + C ((n : WittVector p (GaloisField p 2)))
  have hfmonic : f.Monic := by unfold f; monicity!
  have hfeval : ∀ x : WittVector p (GaloisField p 2), f.eval x = x ^ 2 - (t : WittVector p (GaloisField p 2)) * x + n := by
    intro x; simp [f]
  have hfderiv : ∀ x : WittVector p (GaloisField p 2), f.derivative.eval x = 2 * x - (t : WittVector p (GaloisField p 2)) := by
    intro x
    rw [show f = X ^ 2 - C ((t : WittVector p (GaloisField p 2))) * X + C ((n : WittVector p (GaloisField p 2))) from rfl,
      derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X, derivative_C]
    simp

  set a₀ : WittVector p (GaloisField p 2) := WittVector.teichmuller p ωb with ha₀
  have ha₀c : WittVector.constantCoeff a₀ = ωb := by rw [WittVector.constantCoeff_apply, ha₀, WittVector.teichmuller_coeff_zero]
  have hct : WittVector.constantCoeff ((t : WittVector p (GaloisField p 2))) = (t : GaloisField p 2) := map_intCast _ _
  have hcn : WittVector.constantCoeff ((n : WittVector p (GaloisField p 2))) = (n : GaloisField p 2) := map_intCast _ _
  have heval₀ : f.eval a₀ ∈ Ideal.span {(p : WittVector p (GaloisField p 2))} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, hfeval, map_add, map_sub, map_mul, map_pow,
      ha₀c, hct, hcn]
    exact hωb
  have hderunit : IsUnit (f.derivative.eval a₀) := by
    rw [hfderiv]
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, ha₀c, hct, map_ofNat]
    exact h2ωb
  obtain ⟨ω, hωroot, hωa₀⟩ := HenselianRing.is_henselian f hfmonic a₀ heval₀ (hderunit.map _)
  have hω : ω * ω = (t : WittVector p (GaloisField p 2)) * ω - n := by
    have := hωroot; rw [IsRoot, hfeval] at this
    rw [← sub_eq_zero, ← this]; ring
  have hωc : WittVector.constantCoeff ω = ωb := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub, ha₀c, sub_eq_zero] at hωa₀
    exact hωa₀

  have h2ω : IsUnit (2 * ω - (t : WittVector p (GaloisField p 2))) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_sub, map_mul, hωc, hct, map_ofNat]
    exact h2ωb
  have hσω : WittVector.frobenius ω = (t : WittVector p (GaloisField p 2)) - ω := by
    set r := WittVector.frobenius ω with hr

    have hrroot : r * r = (t : WittVector p (GaloisField p 2)) * r - n := by
      have := congrArg WittVector.frobenius hω
      rw [map_mul, map_sub, map_mul, map_intCast, map_intCast] at this
      exact this

    have hprod : (r - ω) * (r - (t - ω)) = 0 := by
      have : (r - ω) * (r - (t - ω)) = (r * r - (t : WittVector p (GaloisField p 2)) * r + n) - (ω * ω - t * ω + n) := by ring
      rw [this, hrroot, hω]; ring
    rcases mul_eq_zero.mp hprod with h | h
    ·
      exfalso
      have hre : WittVector.constantCoeff r = ωb ^ p := by
        rw [WittVector.constantCoeff_apply, hr, WittVector.coeff_frobenius_charP, ← WittVector.constantCoeff_apply, hωc]
      have hfix : ωb ^ p = ωb := by rw [← hre, sub_eq_zero.mp h, hωc]
      obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_eq p ωb hfix
      exact hωb_not c hc
    · exact sub_eq_zero.mp h
  refine ⟨ι, ω, hιfix, hω, hσω, ?_, ?_⟩
  ·
    intro c d hcd
    have hσ := congrArg WittVector.frobenius hcd
    rw [map_add, map_mul, hιfix, hιfix, hσω, map_zero] at hσ

    have hd0 : ι d * (2 * ω - (t : WittVector p (GaloisField p 2))) = 0 := by linear_combination hcd - hσ
    have hd : ι d = 0 := by
      obtain ⟨u, hu⟩ := h2ω
      rw [← hu] at hd0
      exact (Units.mul_left_eq_zero u).mp hd0
    have hc : ι c = 0 := by rw [hd, zero_mul, add_zero] at hcd; exact hcd
    exact ⟨hιinj (by rw [hc, map_zero]), hιinj (by rw [hd, map_zero])⟩
  ·
    intro k
    induction k with
    | zero =>
      intro x
      exact ⟨0, 0, by rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top⟩
    | succ k ih =>
      intro x
      obtain ⟨c, d, hcd⟩ := ih x
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hcd
      obtain ⟨ca, da, hya⟩ := hspan (WittVector.constantCoeff y)

      obtain ⟨A, hA⟩ : ∃ A : ℤ, ((A : ℤ) : ZMod p) = ca := ⟨_, ZMod.intCast_zmod_cast ca⟩
      obtain ⟨B, hB⟩ : ∃ B : ℤ, ((B : ℤ) : ZMod p) = da := ⟨_, ZMod.intCast_zmod_cast da⟩
      refine ⟨c + (p : ℤ) ^ k * A, d + (p : ℤ) ^ k * B, ?_⟩
      have hy' : y - ((A : WittVector p (GaloisField p 2)) + (B : WittVector p (GaloisField p 2)) * ω) ∈
          Ideal.span {(p : WittVector p (GaloisField p 2))} := by
        rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub, map_add, map_mul, hωc,
          map_intCast, map_intCast, hya, ← map_intCast (algebraMap (ZMod p) (GaloisField p 2)) A,
          ← map_intCast (algebraMap (ZMod p) (GaloisField p 2)) B, hA, hB, sub_self]
      obtain ⟨y', hy'⟩ := Ideal.mem_span_singleton.mp hy'
      refine Ideal.mem_span_singleton.mpr ⟨y', ?_⟩
      have e1 : x - ((c : WittVector p (GaloisField p 2)) + (d : WittVector p (GaloisField p 2)) * ω) =
          (p : WittVector p (GaloisField p 2)) ^ k * y := hy
      have e2 : y - ((A : WittVector p (GaloisField p 2)) + (B : WittVector p (GaloisField p 2)) * ω) =
          (p : WittVector p (GaloisField p 2)) * y' := hy'
      push_cast
      rw [pow_succ]
      linear_combination e1 + (p : WittVector p (GaloisField p 2)) ^ k * e2

end S_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero
end P2MW
export P2MW.S_WittVector_exists_ringHom_padicInt_and_root_of_forall_sq_sub_mul_add_ne_zero (solution)
