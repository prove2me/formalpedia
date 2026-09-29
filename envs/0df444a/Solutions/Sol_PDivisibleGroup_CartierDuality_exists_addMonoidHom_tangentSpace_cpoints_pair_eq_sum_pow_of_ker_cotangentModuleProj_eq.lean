-- Prove2me | solution 1 for PDivisibleGroup.CartierDuality.exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fb1fbc3e-81b3-5633-acdd-70aafc78b500

import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_CharacterDifferential
import Definitions.Def_PDivisibleGroup_CompletedPoints
import Theorems.Thm_PDivisibleGroup_Hopf_convPow_apply_mul_eq_sum_of_apply_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq

set_option autoImplicit false

open Coalgebra Bialgebra WithConv PDivisibleGroup
p2m_open_scoped "TensorProduct Coalgebra.TensorProduct Bialgebra.TensorProduct"

namespace PDivEXPRScalars

variable (p : ℕ) [Fact p.Prime]

private theorem _root_.PDivEXPRScalars.factorial_ne_zero (k : ℕ) : ((k.factorial : ℕ) : ℤ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)

p2m_export "PDivEXPRScalars" "factorial_ne_zero"
theorem valuation_factorial (k : ℕ) :
    ((k.factorial : ℕ) : ℤ_[p]).valuation = padicValNat p k.factorial := by
  have h := PadicInt.valuation_coe ((k.factorial : ℕ) : ℤ_[p])
  rw [PadicInt.coe_natCast, Padic.valuation_natCast] at h
  exact_mod_cast h.symm

theorem valuation_factorial_lt {k : ℕ} (hk : k ≠ 0) :
    ((k.factorial : ℕ) : ℤ_[p]).valuation < k := by
  rw [valuation_factorial]
  exact padicValNat_factorial_lt_of_ne_zero p hk

theorem valuation_factorial_le (k : ℕ) :
    ((k.factorial : ℕ) : ℤ_[p]).valuation ≤ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · exact (valuation_factorial_lt p hk).le

noncomputable def c (k : ℕ) : ℤ_[p] :=
  ((PadicInt.unitCoeff (factorial_ne_zero p k))⁻¹ : ℤ_[p]ˣ) *
    (p : ℤ_[p]) ^ (2 * k - ((k.factorial : ℕ) : ℤ_[p]).valuation)

theorem factorial_mul_c (k : ℕ) : ((k.factorial : ℕ) : ℤ_[p]) * c p k = (p : ℤ_[p]) ^ (2 * k) := by
  have hspec := PadicInt.unitCoeff_spec (factorial_ne_zero p k)
  set u := PadicInt.unitCoeff (factorial_ne_zero p k)
  set v := ((k.factorial : ℕ) : ℤ_[p]).valuation
  have hv : v ≤ 2 * k := (valuation_factorial_le p k).trans (by omega)
  have hc : c p k = ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * k - v) := rfl
  clear_value u v
  rw [hc, hspec]
  calc (u : ℤ_[p]) * (p : ℤ_[p]) ^ v * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * k - v))
      = ((u : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])) * ((p : ℤ_[p]) ^ v * (p : ℤ_[p]) ^ (2 * k - v)) := by
        ring
    _ = (p : ℤ_[p]) ^ (2 * k) := by
        rw [Units.mul_inv, one_mul, ← pow_add, Nat.add_sub_cancel' hv]

theorem c_zero : c p 0 = 1 := by
  have h := factorial_mul_c p 0
  simpa using h

theorem c_one : c p 1 = (p : ℤ_[p]) ^ 2 := by
  have h := factorial_mul_c p 1
  simpa using h

theorem pow_succ_dvd_c {k : ℕ} (hk : k ≠ 0) : (p : ℤ_[p]) ^ (k + 1) ∣ c p k := by
  have hv := valuation_factorial_lt p hk
  set v := ((k.factorial : ℕ) : ℤ_[p]).valuation
  have hc : c p k = (((PadicInt.unitCoeff (factorial_ne_zero p k))⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
      (p : ℤ_[p]) ^ (2 * k - v) := rfl
  clear_value v
  rw [hc]
  refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
  omega

theorem choose_mul_c_add (j l : ℕ) :
    (((j + l).choose j : ℕ) : ℤ_[p]) * c p (j + l) = c p j * c p l := by
  have hj := factorial_ne_zero p j
  have hl := factorial_ne_zero p l
  refine mul_left_cancel₀ (mul_ne_zero hj hl) ?_
  have hnat : ((j + l).choose j) * j.factorial * l.factorial = (j + l).factorial := by
    rw [Nat.choose_symm_add]
    exact Nat.add_choose_mul_factorial_mul_factorial j l
  calc ((j.factorial : ℕ) : ℤ_[p]) * ((l.factorial : ℕ) : ℤ_[p]) *
        ((((j + l).choose j : ℕ) : ℤ_[p]) * c p (j + l))
      = ((((j + l).choose j) * j.factorial * l.factorial : ℕ) : ℤ_[p]) * c p (j + l) := by
        push_cast; ring
    _ = (p : ℤ_[p]) ^ (2 * (j + l)) := by rw [hnat, factorial_mul_c]
    _ = (((j.factorial : ℕ) : ℤ_[p]) * c p j) * (((l.factorial : ℕ) : ℤ_[p]) * c p l) := by
        rw [factorial_mul_c, factorial_mul_c, ← pow_add, mul_add]
    _ = _ := by ring

end PDivEXPRScalars

namespace ConvExpAuxR

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]
  {Λ : Type*} [CommSemiring Λ] [Algebra R Λ]

theorem sum_range_sum_range_succ_eq {M : Type*} [AddCommMonoid M] (K : ℕ) (g : ℕ → ℕ → M) :
    ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range (k + 1), g j (k - j) =
      ∑ j ∈ Finset.range K, ∑ l ∈ Finset.range K, if j + l < K then g j l else 0 := by

  have hdisj : (↑(Finset.range K) : Set ℕ).PairwiseDisjoint
      (fun k => (Finset.HasAntidiagonal.antidiagonal k : Finset (ℕ × ℕ))) := by
    intro k _ k' _ hkk'
    change Disjoint (Finset.HasAntidiagonal.antidiagonal k) (Finset.HasAntidiagonal.antidiagonal k')
    rw [Finset.disjoint_left]
    intro ij h1 h2
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
    exact hkk' (h1.symm.trans h2)
  have hL : ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range (k + 1), g j (k - j) =
      ∑ ij ∈ (Finset.range K).biUnion (fun k => Finset.HasAntidiagonal.antidiagonal k), g ij.1 ij.2 := by
    rw [Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j l => g j l) k]
  have hset : (Finset.range K).biUnion (fun k => Finset.HasAntidiagonal.antidiagonal k) =
      (Finset.range K ×ˢ Finset.range K).filter (fun ij : ℕ × ℕ => ij.1 + ij.2 < K) := by
    ext ⟨j, l⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨k, hk, hjl⟩; omega
    · rintro ⟨-, h⟩; exact ⟨j + l, h, rfl⟩
  rw [hL, hset, Finset.sum_filter, Finset.sum_product]

theorem expSum_apply_mul (d : A →ₗ[R] Λ)
    (hd : ∀ a b : A, d (a * b) = counit (R := R) a • d b + counit (R := R) b • d a)
    (c : ℕ → Λ) (K : ℕ)
    (hc : ∀ j l : ℕ, (((j + l).choose j : ℕ) : Λ) * c (j + l) = c j * c l)
    (hK : ∀ j l : ℕ, K ≤ j + l → c j * c l = 0) (a b : A) :
    ∑ k ∈ Finset.range K, c k * (toConv d ^ k) (a * b) =
      (∑ k ∈ Finset.range K, c k * (toConv d ^ k) a) *
        ∑ k ∈ Finset.range K, c k * (toConv d ^ k) b := by
  have h1 : ∀ k ∈ Finset.range K, c k * (toConv d ^ k) (a * b) =
      ∑ j ∈ Finset.range (k + 1),
        (c j * (toConv d ^ j) a) * (c (k - j) * (toConv d ^ (k - j)) b) := by
    intro k _
    rw [PDivisibleGroup.Hopf.convPow_apply_mul_eq_sum_of_apply_mul_eq d hd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hkj : j + (k - j) = k := by omega
    have := hc j (k - j)
    rw [hkj] at this
    calc c k * (((k.choose j : ℕ) : Λ) * ((toConv d ^ j) a * (toConv d ^ (k - j)) b))
        = (((k.choose j : ℕ) : Λ) * c k) * ((toConv d ^ j) a * (toConv d ^ (k - j)) b) := by ring
      _ = _ := by rw [this]; ring
  rw [Finset.sum_congr rfl h1,
    sum_range_sum_range_succ_eq K (fun j l => (c j * (toConv d ^ j) a) * (c l * (toConv d ^ l) b)),
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rfl
  · calc (0 : Λ) = (c j * c l) * ((toConv d ^ j) a * (toConv d ^ l) b) := by
          rw [hK j l (not_lt.mp h), zero_mul]
      _ = _ := by ring

theorem convPow_apply_one (d : A →ₗ[R] Λ) (k : ℕ) :
    (toConv d ^ k) (1 : A) = (d 1) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, counit_one, map_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, LinearMap.convMul_apply, comul_one, Algebra.TensorProduct.one_def,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    change (toConv d ^ k) (1 : A) * d 1 = _
    rw [ih]

theorem expSum_apply_one (d : A →ₗ[R] Λ) (hd1 : d 1 = 0) (c : ℕ → Λ) (K : ℕ) (hK : 0 < K)
    (hc0 : c 0 = 1) :
    ∑ k ∈ Finset.range K, c k * (toConv d ^ k) (1 : A) = 1 := by
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hK)]
  · rw [pow_zero, LinearMap.convOne_apply, counit_one, map_one, mul_one, hc0]
  · intro k _ hk
    rw [convPow_apply_one, hd1, zero_pow hk, mul_zero]

end ConvExpAuxR

namespace PDivEXPRPair

variable {R : Type} [CommRing R] {p h : ℕ} {G G' : PDivisibleGroup R p h}
  (D : G.CartierDuality G') (S : Type) [CommRing S] [Algebra R S]

noncomputable abbrev bas (G : PDivisibleGroup R p h) (v : ℕ) := Module.Free.chooseBasis R (G.level v)

noncomputable def beta (v : ℕ) (i : Module.Free.ChooseBasisIndex R (G.level v)) : G'.level v :=
  (D.toDualEquiv v).symm ((bas G v).coord i)

noncomputable def epair (v : ℕ) (ψ : G'.Point S v) (φ : G.level v →ₗ[R] S) : S :=
  ∑ i, φ (bas G v i) * Point.toAlgHom ψ (beta D v i)

theorem epair_point (v : ℕ) (f : G.Point S v) (ψ : G'.Point S v) :
    epair D S v ψ (Point.toAlgHom f).toLinearMap = D.pair S v f ψ := by
  rw [D.pair_def]
  rfl

theorem epair_add (v : ℕ) (ψ : G'.Point S v) (φ φ' : G.level v →ₗ[R] S) :
    epair D S v ψ (φ + φ') = epair D S v ψ φ + epair D S v ψ φ' := by
  simp only [epair, LinearMap.add_apply, add_mul, Finset.sum_add_distrib]

theorem epair_smul (v : ℕ) (ψ : G'.Point S v) (s : S) (φ : G.level v →ₗ[R] S) :
    epair D S v ψ (s • φ) = s * epair D S v ψ φ := by
  simp only [epair, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem epair_smul_base (v : ℕ) (ψ : G'.Point S v) (r : R) (φ : G.level v →ₗ[R] S) :
    epair D S v ψ (r • φ) = algebraMap R S r * epair D S v ψ φ := by
  simp only [epair, LinearMap.smul_apply, Finset.mul_sum, Algebra.smul_def, mul_assoc]

theorem epair_sum (v : ℕ) (ψ : G'.Point S v) {ι : Type*} (s : Finset ι) (φ : ι → G.level v →ₗ[R] S) :
    epair D S v ψ (∑ k ∈ s, φ k) = ∑ k ∈ s, epair D S v ψ (φ k) := by
  induction s using Finset.cons_induction with
  | empty => simp [epair]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, epair_add, ih]

theorem sum_equiv_apply_smul_beta (v : ℕ) (x : G'.level v) :
    ∑ i, (D.equiv v x) (bas G v i) • beta D v i = x := by
  have h : ∑ i, (D.equiv v x) (bas G v i) • beta D v i =
      (D.toDualEquiv v).symm (∑ i, (D.toDualEquiv v x) (bas G v i) • (bas G v).coord i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [h, Module.Basis.sum_dual_apply_smul_coord, LinearEquiv.symm_apply_apply]

theorem toAlgHom_eq_sum (v : ℕ) (ψ : G'.Point S v) (x : G'.level v) :
    Point.toAlgHom ψ x = ∑ i, (D.equiv v x) (bas G v i) • Point.toAlgHom ψ (beta D v i) := by
  conv_lhs => rw [← sum_equiv_apply_smul_beta D v x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]

theorem toDual_equiv_beta (v : ℕ) (i : Module.Free.ChooseBasisIndex R (G.level v)) :
    CartierDual.toDual R (G.level v) (D.equiv v (beta D v i)) = (bas G v).coord i := by
  change D.toDualEquiv v ((D.toDualEquiv v).symm ((bas G v).coord i)) = _
  rw [LinearEquiv.apply_symm_apply]

theorem sum3_comm {ι κ μ : Type*} {s : Finset ι} {t : Finset κ} {u : Finset μ}
    {F : ι → κ → μ → S} :
    ∑ i ∈ s, ∑ j ∈ t, ∑ l ∈ u, F i j l = ∑ l ∈ u, ∑ i ∈ s, ∑ j ∈ t, F i j l := by
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem mul'_map_eq_sum (v : ℕ) (φ φ' : G.level v →ₗ[R] S) (t : G.level v ⊗[R] G.level v) :
    LinearMap.mul' R S (TensorProduct.map φ φ' t) =
      ∑ i, ∑ j, (TensorProduct.dualDistrib R (G.level v) (G.level v)
        ((bas G v).coord i ⊗ₜ[R] (bas G v).coord j) t) • (φ (bas G v i) * φ' (bas G v j)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_smul, Finset.sum_const_zero]
  | tmul a a' =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    simp only [TensorProduct.dualDistrib_apply, Module.Basis.coord_apply]
    have ha : φ a = ∑ i, (bas G v).repr a i • φ (bas G v i) := by
      conv_lhs => rw [← (bas G v).sum_repr a]
      simp only [map_sum, map_smul]
    have ha' : φ' a' = ∑ j, (bas G v).repr a' j • φ' (bas G v j) := by
      conv_lhs => rw [← (bas G v).sum_repr a']
      simp only [map_sum, map_smul]
    rw [ha, ha', Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_smul, Finset.sum_add_distrib]

theorem epair_convMul (v : ℕ) (ψ : G'.Point S v) (φ φ' : WithConv (G.level v →ₗ[R] S)) :
    epair D S v ψ (φ * φ').ofConv = epair D S v ψ φ.ofConv * epair D S v ψ φ'.ofConv := by
  symm
  calc epair D S v ψ φ.ofConv * epair D S v ψ φ'.ofConv
      = ∑ i, ∑ j, (φ.ofConv (bas G v i) * φ'.ofConv (bas G v j)) *
          Point.toAlgHom ψ (beta D v i * beta D v j) := by
        simp only [epair, Finset.sum_mul_sum, map_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ i, ∑ j, (φ.ofConv (bas G v i) * φ'.ofConv (bas G v j)) *
          ∑ l, (TensorProduct.dualDistrib R (G.level v) (G.level v)
            ((bas G v).coord i ⊗ₜ[R] (bas G v).coord j) (comul (R := R) (bas G v l))) •
            Point.toAlgHom ψ (beta D v l) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [toAlgHom_eq_sum D S v ψ (beta D v i * beta D v j)]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [D.equiv_mul_apply, toDual_equiv_beta, toDual_equiv_beta]
    _ = ∑ l, (∑ i, ∑ j, (TensorProduct.dualDistrib R (G.level v) (G.level v)
            ((bas G v).coord i ⊗ₜ[R] (bas G v).coord j) (comul (R := R) (bas G v l))) •
            (φ.ofConv (bas G v i) * φ'.ofConv (bas G v j))) * Point.toAlgHom ψ (beta D v l) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [sum3_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm]
    _ = epair D S v ψ (φ * φ').ofConv := by
        simp only [epair]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← mul'_map_eq_sum, LinearMap.convMul_apply]

theorem epair_convPow (v : ℕ) (ψ : G'.Point S v) (φ : WithConv (G.level v →ₗ[R] S)) (k : ℕ)
    (h1 : epair D S v ψ (1 : WithConv (G.level v →ₗ[R] S)).ofConv = 1) :
    epair D S v ψ (φ ^ k).ofConv = (epair D S v ψ φ.ofConv) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, h1]
  | succ k ih => rw [pow_succ, pow_succ, epair_convMul, ih]

theorem epair_convOne (v : ℕ) (ψ : G'.Point S v) :
    epair D S v ψ (1 : WithConv (G.level v →ₗ[R] S)).ofConv = 1 := by
  have h1 : epair D S v ψ (1 : WithConv (G.level v →ₗ[R] S)).ofConv =
      ∑ i, (D.equiv v 1) (bas G v i) • Point.toAlgHom ψ (beta D v i) := by
    simp only [epair]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.convOne_apply, D.equiv_one_apply, Algebra.smul_def]
  rw [h1, ← toAlgHom_eq_sum, map_one]

end PDivEXPRPair

namespace PDivEXPRConv

section ConvNat

variable {R : Type*} [CommSemiring R] {A B C : Type*}

theorem convPow_ofConv_comp_coalgHom [Semiring A] [Algebra R A]
    [AddCommMonoid B] [Module R B] [Coalgebra R B] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (f : WithConv (C →ₗ[R] A)) (t : B →ₗc[R] C) (k : ℕ) :
    (f ^ k).ofConv ∘ₗ t.toLinearMap = ((toConv (f.ofConv ∘ₗ t.toLinearMap)) ^ k).ofConv := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, LinearMap.convOne_def, LinearMap.comp_assoc, t.counit_comp]
    rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, LinearMap.convMul_comp_coalgHom_distrib, ih]

theorem algHom_comp_convPow [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    (φ : A →ₐ[R] B) (f : WithConv (C →ₗ[R] A)) (k : ℕ) :
    φ.toLinearMap ∘ₗ (f ^ k).ofConv = ((toConv (φ.toLinearMap ∘ₗ f.ofConv)) ^ k).ofConv := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, LinearMap.convOne_def, LinearMap.convOne_def, ← LinearMap.comp_assoc]
    congr 1
    exact LinearMap.ext fun r => φ.commutes r
  | succ k ih =>
    rw [pow_succ, pow_succ, LinearMap.algHom_comp_convMul_distrib, ih]

end ConvNat

section SMulConv

variable {R : Type*} [CommSemiring R] {A : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A]
  {L : Type*} [CommSemiring L] [Algebra R L]

theorem smul_convMul (c : L) (x y : WithConv (A →ₗ[R] L)) : (c • x) * y = c • (x * y) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  change ((c • x) * y) a = c • ((x * y) a)
  rw [Coalgebra.Repr.convMul_apply (ℛ R a), Coalgebra.Repr.convMul_apply (ℛ R a), Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  change (c • x.ofConv ((ℛ R a).left r)) * y.ofConv ((ℛ R a).right r) = _
  rw [smul_mul_assoc]

theorem convMul_smul (c : L) (x y : WithConv (A →ₗ[R] L)) : x * (c • y) = c • (x * y) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  change (x * (c • y)) a = c • ((x * y) a)
  rw [Coalgebra.Repr.convMul_apply (ℛ R a), Coalgebra.Repr.convMul_apply (ℛ R a), Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  change x.ofConv ((ℛ R a).left r) * (c • y.ofConv ((ℛ R a).right r)) = _
  rw [mul_smul_comm]

scoped instance instIsScalarTowerConv : IsScalarTower L (WithConv (A →ₗ[R] L)) (WithConv (A →ₗ[R] L)) :=
  ⟨fun c x y => smul_convMul c x y⟩

scoped instance instSMulCommClassConv : SMulCommClass L (WithConv (A →ₗ[R] L)) (WithConv (A →ₗ[R] L)) :=
  ⟨fun c x y => (convMul_smul c x y).symm⟩

end SMulConv

end PDivEXPRConv
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.PDivEXPRConv"

namespace PDivEXPR

open PDivEXPRConv

variable (p : ℕ)

section Coeff

variable [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R]

abbrev Λ (i : ℕ) : Type := R ⧸ Ideal.span {(p : R) ^ i}

noncomputable abbrev mkL (i : ℕ) : R →ₗ[R] Λ p R i :=
  (Ideal.Quotient.mkₐ R (Ideal.span {(p : R) ^ i})).toLinearMap

omit [Fact p.Prime] [Algebra ℤ_[p] R] in
theorem mkL_apply (i : ℕ) (t : R) : mkL p R i t = Ideal.Quotient.mk _ t := rfl

noncomputable def cΛ (i k : ℕ) : Λ p R i := Ideal.Quotient.mk _ (algebraMap ℤ_[p] R (PDivEXPRScalars.c p k))

theorem cΛ_zero (i : ℕ) : cΛ p R i 0 = 1 := by rw [cΛ, PDivEXPRScalars.c_zero, map_one, map_one]

theorem choose_mul_cΛ (i j l : ℕ) :
    (((j + l).choose j : ℕ) : Λ p R i) * cΛ p R i (j + l) = cΛ p R i j * cΛ p R i l := by
  rw [cΛ, cΛ, cΛ, ← map_natCast ((Ideal.Quotient.mk (Ideal.span {(p : R) ^ i})).comp (algebraMap ℤ_[p] R)),
    RingHom.comp_apply, ← map_mul, ← map_mul, PDivEXPRScalars.choose_mul_c_add, map_mul, map_mul]

theorem cΛ_eq_zero {i k : ℕ} (hk : k ≠ 0) (hik : i ≤ k + 1) : cΛ p R i k = 0 := by
  rw [cΛ, Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_singleton.mpr ((pow_dvd_pow _ hik).trans ?_)
  obtain ⟨d, hd⟩ := PDivEXPRScalars.pow_succ_dvd_c p hk
  exact ⟨algebraMap ℤ_[p] R d, by rw [hd, map_mul, map_pow, map_natCast]⟩

theorem cΛ_mul_cΛ_eq_zero (i j l : ℕ) (h : i ≤ j + l) : cΛ p R i j * cΛ p R i l = 0 := by
  rcases Nat.eq_zero_or_pos (j + l) with hjl | hjl
  ·
    have hi : i = 0 := by omega
    subst hi
    haveI : Subsingleton (Λ p R 0) := Ideal.Quotient.subsingleton_iff.mpr (by
      rw [pow_zero, Ideal.span_singleton_one])
    exact Subsingleton.elim _ _
  · rw [← choose_mul_cΛ, cΛ_eq_zero p R (Nat.pos_iff_ne_zero.mp hjl) (by omega), mul_zero]

end Coeff
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.PDivEXPRConv"

variable {R : Type} [CommRing R]

structure Tower {h : ℕ} (G : PDivisibleGroup R p h) : Prop where
  surj : ∀ v, Function.Surjective (G.cotangentModuleProj v)
  ker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) = Ideal.span {(p : R) ^ v} • ⊤

variable {h : ℕ} {G : PDivisibleGroup R p h}

theorem ker_proj_le_ker (hT : Tower p G) (τ : G.tangentSpace R) {w i : ℕ} (hiw : i ≤ w) :
    LinearMap.ker (G.cotangentModuleProj w) ≤ LinearMap.ker (mkL p R i ∘ₗ τ) := by
  rw [hT.ker w, Submodule.smul_le]
  intro r hr x _
  rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, mkL_apply, smul_eq_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _
    ((Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (p : R) hiw)) hr)

variable (hT : Tower p G) (τ : G.tangentSpace R)

noncomputable def lam (w i : ℕ) (hiw : i ≤ w) : G.Cotangent w →ₗ[R] Λ p R i :=
  ((LinearMap.ker (G.cotangentModuleProj w)).liftQ (mkL p R i ∘ₗ τ) (ker_proj_le_ker p hT τ hiw)) ∘ₗ
    (LinearMap.quotKerEquivOfSurjective (G.cotangentModuleProj w) (hT.surj w)).symm.toLinearMap

theorem lam_proj (w i : ℕ) (hiw : i ≤ w) (x : G.cotangentModule) :
    lam p hT τ w i hiw (G.cotangentModuleProj w x) = Ideal.Quotient.mk _ (τ x) := by
  have hsymm : (LinearMap.quotKerEquivOfSurjective (G.cotangentModuleProj w)
      (hT.surj w)).symm (G.cotangentModuleProj w x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [lam, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hsymm, Submodule.liftQ_apply]
  rfl

theorem lam_add (τ' : G.tangentSpace R) (w i : ℕ) (hiw : i ≤ w) :
    lam p hT (τ + τ') w i hiw = lam p hT τ w i hiw + lam p hT τ' w i hiw := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hT.surj w y
  rw [LinearMap.add_apply, lam_proj, lam_proj, lam_proj, LinearMap.add_apply, map_add]

theorem lam_cotangentMap (w i : ℕ) (hiw : i ≤ w) (y : G.Cotangent (w + 1)) :
    lam p hT τ w i hiw (G.cotangentMap w y) = lam p hT τ (w + 1) i (hiw.trans (Nat.le_succ w)) y := by
  obtain ⟨x, rfl⟩ := hT.surj (w + 1) y
  rw [G.cotangentMap_cotangentModuleProj, lam_proj, lam_proj]

theorem reduce_lam (w i : ℕ) (hiw : i + 1 ≤ w) (y : G.Cotangent w) :
    reduceModPow R p R i (lam p hT τ w (i + 1) hiw y) =
      lam p hT τ w i ((Nat.le_succ i).trans hiw) y := by
  obtain ⟨x, rfl⟩ := hT.surj w y
  rw [lam_proj, lam_proj, reduceModPow_mk]

noncomputable def der (w i : ℕ) (hiw : i ≤ w) : G.level w →ₗ[R] Λ p R i :=
  lam p hT τ w i hiw ∘ₗ G.cotangentClass w

theorem der_apply (w i : ℕ) (hiw : i ≤ w) (a : G.level w) :
    der p hT τ w i hiw a = lam p hT τ w i hiw (G.cotangentClass w a) := rfl

theorem der_one (w i : ℕ) (hiw : i ≤ w) : der p hT τ w i hiw 1 = 0 := by
  rw [der_apply, cotangentClass_one, map_zero]

theorem cotangentClass_mul (w : ℕ) (a b : G.level w) :
    G.cotangentClass w (a * b) =
      counit (R := R) a • G.cotangentClass w b + counit (R := R) b • G.cotangentClass w a := by
  rw [cotangentClass_apply, cotangentClass_apply, cotangentClass_apply,
    ← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add, Ideal.toCotangent_eq,
    pow_two]
  refine Ideal.mul_mem_mul (Hopf.sub_algebraMap_counit_mem_augIdeal R _ a)
    (Hopf.sub_algebraMap_counit_mem_augIdeal R _ b) |> fun hmem => ?_
  convert hmem using 1
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Bialgebra.counit_mul, map_mul,
    Algebra.smul_def]
  ring

theorem der_mul (w i : ℕ) (hiw : i ≤ w) (a b : G.level w) :
    der p hT τ w i hiw (a * b) =
      counit (R := R) a • der p hT τ w i hiw b + counit (R := R) b • der p hT τ w i hiw a := by
  rw [der_apply, cotangentClass_mul, map_add, map_smul, map_smul, der_apply, der_apply]

variable [Fact p.Prime] [Algebra ℤ_[p] R]

noncomputable abbrev Pconv (w i : ℕ) (hiw : i ≤ w) : WithConv (G.level w →ₗ[R] Λ p R i) :=
  toConv (der p hT τ w i hiw)

noncomputable def expW (w i : ℕ) (hiw : i ≤ w) : WithConv (G.level w →ₗ[R] Λ p R i) :=
  ∑ k ∈ Finset.range i, cΛ p R i k • Pconv p hT τ w i hiw ^ k

noncomputable def expLin (w i : ℕ) (hiw : i ≤ w) : G.level w →ₗ[R] Λ p R i :=
  (expW p hT τ w i hiw).ofConv

theorem toConv_expLin (w i : ℕ) (hiw : i ≤ w) : toConv (expLin p hT τ w i hiw) = expW p hT τ w i hiw := rfl

theorem expLin_apply (w i : ℕ) (hiw : i ≤ w) (a : G.level w) :
    expLin p hT τ w i hiw a = ∑ k ∈ Finset.range i, cΛ p R i k * (Pconv p hT τ w i hiw ^ k) a := by
  rw [expLin, expW, ofConv_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ofConv_smul, LinearMap.smul_apply, smul_eq_mul]

theorem expLin_mul (w i : ℕ) (hiw : i ≤ w) (a b : G.level w) :
    expLin p hT τ w i hiw (a * b) = expLin p hT τ w i hiw a * expLin p hT τ w i hiw b := by
  rw [expLin_apply, expLin_apply, expLin_apply]
  exact ConvExpAuxR.expSum_apply_mul (der p hT τ w i hiw) (der_mul p hT τ w i hiw) (cΛ p R i) i
    (choose_mul_cΛ p R i) (cΛ_mul_cΛ_eq_zero p R i) a b

theorem expLin_one (w i : ℕ) (hiw : i ≤ w) : expLin p hT τ w i hiw 1 = 1 := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    haveI : Subsingleton (Λ p R 0) := Ideal.Quotient.subsingleton_iff.mpr (by
      rw [pow_zero, Ideal.span_singleton_one])
    exact Subsingleton.elim _ _
  · rw [expLin_apply]
    exact ConvExpAuxR.expSum_apply_one (der p hT τ w i hiw) (der_one p hT τ w i hiw) (cΛ p R i) i hi (cΛ_zero p R i)

noncomputable def expAlgHom (w i : ℕ) (hiw : i ≤ w) : G.level w →ₐ[R] Λ p R i :=
  AlgHom.ofLinearMap (expLin p hT τ w i hiw) (expLin_one p hT τ w i hiw) (expLin_mul p hT τ w i hiw)

noncomputable def expPoint (w i : ℕ) (hiw : i ≤ w) : G.Point (Λ p R i) w :=
  Point.ofAlgHom (expAlgHom p hT τ w i hiw)

@[scoped simp] theorem toAlgHom_expPoint (w i : ℕ) (hiw : i ≤ w) :
    Point.toAlgHom (expPoint p hT τ w i hiw) = expAlgHom p hT τ w i hiw := rfl

theorem expAlgHom_toLinearMap (w i : ℕ) (hiw : i ≤ w) :
    (expAlgHom p hT τ w i hiw).toLinearMap = expLin p hT τ w i hiw := rfl

omit [Fact p.Prime] [Algebra ℤ_[p] R] in

theorem cotangentClass_transition (w : ℕ) (a : G.level (w + 1)) :
    G.cotangentClass w (G.transition w a) = G.cotangentMap w (G.cotangentClass (w + 1) a) := by
  rw [cotangentClass_apply, cotangentClass_apply, cotangentMap_toCotangent]
  congr 1
  refine Subtype.ext ?_
  change G.transition w a - algebraMap R _ (counit (R := R) (G.transition w a)) =
    G.transition w (a - algebraMap R _ (counit (R := R) a))
  rw [map_sub, G.counit_transition]
  congr 1
  exact ((G.transitionAlgHom w).commutes (counit (R := R) a)).symm

omit [Fact p.Prime] [Algebra ℤ_[p] R] in
theorem der_transition (w i : ℕ) (hiw : i ≤ w) (a : G.level (w + 1)) :
    der p hT τ w i hiw (G.transition w a) = der p hT τ (w + 1) i (hiw.trans (Nat.le_succ w)) a := by
  rw [der_apply, der_apply, cotangentClass_transition, lam_cotangentMap]

omit [Fact p.Prime] [Algebra ℤ_[p] R] in
theorem der_comp_transition (w i : ℕ) (hiw : i ≤ w) :
    der p hT τ w i hiw ∘ₗ (G.transition w : G.level (w + 1) →ₗc[R] G.level w).toLinearMap =
      der p hT τ (w + 1) i (hiw.trans (Nat.le_succ w)) :=
  LinearMap.ext fun a => der_transition p hT τ w i hiw a

theorem expLin_succ (w i : ℕ) (hiw : i ≤ w) :
    expLin p hT τ (w + 1) i (hiw.trans (Nat.le_succ w)) =
      expLin p hT τ w i hiw ∘ₗ (G.transition w : G.level (w + 1) →ₗc[R] G.level w).toLinearMap := by
  rw [expLin, expLin, expW, expW, ofConv_sum, ofConv_sum]
  have hsum : ∀ (F : ℕ → (G.level w →ₗ[R] Λ p R i)) (s : Finset ℕ),
      (∑ k ∈ s, F k) ∘ₗ (G.transition w : G.level (w + 1) →ₗc[R] G.level w).toLinearMap =
        ∑ k ∈ s, F k ∘ₗ (G.transition w : G.level (w + 1) →ₗc[R] G.level w).toLinearMap := by
    intro F s
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ofConv_smul, ofConv_smul, LinearMap.smul_comp, convPow_ofConv_comp_coalgHom, ofConv_toConv,
    der_comp_transition]

theorem expPoint_succ (w i : ℕ) (hiw : i ≤ w) :
    expPoint p hT τ (w + 1) i (hiw.trans (Nat.le_succ w)) = G.pointIncl (Λ p R i) w (expPoint p hT τ w i hiw) := by
  refine Point.ext fun a => ?_
  rw [pointIncl_apply, toAlgHom_expPoint, toAlgHom_expPoint]
  change expLin p hT τ (w + 1) i _ a = expLin p hT τ w i hiw (G.transition w a)
  rw [expLin_succ]
  rfl

theorem pointInclLE_expPoint {i w : ℕ} (hiw : i ≤ w) :
    G.pointInclLE (Λ p R i) hiw (expPoint p hT τ i i le_rfl) = expPoint p hT τ w i hiw := by
  induction hiw with
  | refl => rw [pointInclLE_self]
  | @step w hiw ih => rw [G.pointInclLE_succ hiw, ih, ← expPoint_succ]

omit [Fact p.Prime] [Algebra ℤ_[p] R] in

theorem reduce_comp_der (w i : ℕ) (hiw : i + 1 ≤ w) :
    (reduceModPow R p R i).toLinearMap ∘ₗ der p hT τ w (i + 1) hiw =
      der p hT τ w i ((Nat.le_succ i).trans hiw) :=
  LinearMap.ext fun a => reduce_lam p hT τ w i hiw (G.cotangentClass w a)

theorem reduce_comp_expLin (w i : ℕ) (hiw : i + 1 ≤ w) :
    (reduceModPow R p R i).toLinearMap ∘ₗ expLin p hT τ w (i + 1) hiw =
      expLin p hT τ w i ((Nat.le_succ i).trans hiw) := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    haveI : Subsingleton (Λ p R 0) := Ideal.Quotient.subsingleton_iff.mpr (by
      rw [pow_zero, Ideal.span_singleton_one])
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  have hsum : ∀ (F : ℕ → (G.level w →ₗ[R] Λ p R (i + 1))) (s : Finset ℕ),
      (reduceModPow R p R i).toLinearMap ∘ₗ (∑ k ∈ s, F k) =
        ∑ k ∈ s, (reduceModPow R p R i).toLinearMap ∘ₗ F k := by
    intro F s
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  have hsm : ∀ k : ℕ, (reduceModPow R p R i).toLinearMap ∘ₗ
      (cΛ p R (i + 1) k • Pconv p hT τ w (i + 1) hiw ^ k).ofConv =
      cΛ p R i k • (Pconv p hT τ w i ((Nat.le_succ i).trans hiw) ^ k).ofConv := by
    intro k
    simp only [ofConv_smul]
    have h1 : (reduceModPow R p R i).toLinearMap ∘ₗ
        (cΛ p R (i + 1) k • (Pconv p hT τ w (i + 1) hiw ^ k).ofConv) =
        cΛ p R i k • ((reduceModPow R p R i).toLinearMap ∘ₗ (Pconv p hT τ w (i + 1) hiw ^ k).ofConv) := by
      refine LinearMap.ext fun a => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_mul,
        map_mul]
      congr 1
    rw [h1, algHom_comp_convPow, ofConv_toConv, reduce_comp_der]
  rw [expLin, expLin, expW, expW, ofConv_sum, ofConv_sum, hsum, Finset.sum_range_succ]
  simp_rw [hsm]
  rw [cΛ_eq_zero p R (Nat.pos_iff_ne_zero.mp hi) (Nat.le_succ i), zero_smul, add_zero]
  simp only [ofConv_smul]

theorem pointMap_reduce_expPoint (w i : ℕ) (hiw : i + 1 ≤ w) :
    G.pointMap (reduceModPow R p R i) w (expPoint p hT τ w (i + 1) hiw) =
      expPoint p hT τ w i ((Nat.le_succ i).trans hiw) := by
  refine Point.ext fun a => ?_
  rw [toAlgHom_pointMap, toAlgHom_expPoint, toAlgHom_expPoint, AlgHom.comp_apply]
  change (reduceModPow R p R i).toLinearMap (expLin p hT τ w (i + 1) hiw a) = expLin p hT τ w i _ a
  rw [← reduce_comp_expLin p hT τ w i hiw]
  rfl

noncomputable def expFamily : ∀ i : ℕ, G.Points (Λ p R i) :=
  fun i => G.pointsMkAdd (Λ p R i) i (Additive.ofMul (expPoint p hT τ i i le_rfl))

theorem expFamily_mem : expFamily p hT τ ∈ G.CPoints R := by
  intro i
  change G.pointsMap (reduceModPow R p R i)
      (G.pointsMkAdd (Λ p R (i + 1)) (i + 1) (Additive.ofMul (expPoint p hT τ (i + 1) (i + 1) le_rfl))) =
    G.pointsMkAdd (Λ p R i) i (Additive.ofMul (expPoint p hT τ i i le_rfl))
  rw [pointsMap_pointsMkAdd, pointMap_reduce_expPoint,
    show expPoint p hT τ (i + 1) i ((Nat.le_succ i).trans le_rfl) =
      G.pointIncl (Λ p R i) i (expPoint p hT τ i i le_rfl) from expPoint_succ p hT τ i i le_rfl,
    pointsMkAdd_pointIncl]

noncomputable def expC : G.CPoints R := ⟨expFamily p hT τ, expFamily_mem p hT τ⟩

theorem cpointsProj_expC (i : ℕ) :
    G.cpointsProj R i (expC p hT τ) = G.pointsMkAdd (Λ p R i) i (Additive.ofMul (expPoint p hT τ i i le_rfl)) :=
  rfl

theorem expW_add (τ' : G.tangentSpace R) (w i : ℕ) (hiw : i ≤ w) :
    expW p hT (τ + τ') w i hiw = expW p hT τ w i hiw * expW p hT τ' w i hiw := by
  have hP : Pconv p hT (τ + τ') w i hiw = Pconv p hT τ w i hiw + Pconv p hT τ' w i hiw := by
    change toConv (der p hT (τ + τ') w i hiw) = _
    rw [der, lam_add, LinearMap.add_comp, toConv_add]
    rfl
  set P := Pconv p hT τ w i hiw
  set P' := Pconv p hT τ' w i hiw
  rw [expW, hP, expW, expW, Finset.sum_mul_sum]

  have h1 : ∀ k ∈ Finset.range i, cΛ p R i k • (P + P') ^ k =
      ∑ j ∈ Finset.range (k + 1), (cΛ p R i j • P ^ j) * (cΛ p R i (k - j) • P' ^ (k - j)) := by
    intro k _
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hkj : j + (k - j) = k := by omega
    have hc := choose_mul_cΛ p R i j (k - j)
    rw [hkj] at hc
    rw [smul_mul_smul_comm, ← hc, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul (Λ p R i), smul_smul,
      mul_comm (cΛ p R i k)]
  calc ∑ k ∈ Finset.range i, cΛ p R i k • (P + P') ^ k
      = ∑ k ∈ Finset.range i, ∑ j ∈ Finset.range (k + 1),
          (cΛ p R i j • P ^ j) * (cΛ p R i (k - j) • P' ^ (k - j)) := Finset.sum_congr rfl h1
    _ = ∑ j ∈ Finset.range i, ∑ l ∈ Finset.range i,
          if j + l < i then (cΛ p R i j • P ^ j) * (cΛ p R i l • P' ^ l) else 0 :=
        ConvExpAuxR.sum_range_sum_range_succ_eq i (fun j l => (cΛ p R i j • P ^ j) * (cΛ p R i l • P' ^ l))
    _ = ∑ j ∈ Finset.range i, ∑ l ∈ Finset.range i, (cΛ p R i j • P ^ j) * (cΛ p R i l • P' ^ l) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        split_ifs with hjl
        · rfl
        · rw [smul_mul_smul_comm, cΛ_mul_cΛ_eq_zero p R i j l (not_lt.mp hjl), zero_smul]

theorem expPoint_add (τ' : G.tangentSpace R) (w i : ℕ) (hiw : i ≤ w) :
    expPoint p hT (τ + τ') w i hiw = expPoint p hT τ w i hiw * expPoint p hT τ' w i hiw := by
  refine Point.ext fun a => ?_
  have hlin : (Point.toAlgHom (expPoint p hT τ w i hiw * expPoint p hT τ' w i hiw)).toLinearMap =
      (toConv (Point.toAlgHom (expPoint p hT τ w i hiw)).toLinearMap *
        toConv (Point.toAlgHom (expPoint p hT τ' w i hiw)).toLinearMap).ofConv := rfl
  change (Point.toAlgHom (expPoint p hT (τ + τ') w i hiw)).toLinearMap a =
    (Point.toAlgHom (expPoint p hT τ w i hiw * expPoint p hT τ' w i hiw)).toLinearMap a
  rw [hlin, toAlgHom_expPoint, toAlgHom_expPoint, toAlgHom_expPoint, expAlgHom_toLinearMap,
    expAlgHom_toLinearMap, expAlgHom_toLinearMap, toConv_expLin, toConv_expLin, ← expW_add]
  rfl

theorem expC_add (τ' : G.tangentSpace R) : expC p hT (τ + τ') = expC p hT τ + expC p hT τ' := by
  refine cpointsProj_ext G R fun i => ?_
  rw [map_add, cpointsProj_expC, cpointsProj_expC, cpointsProj_expC, expPoint_add, ofMul_mul, map_add]

noncomputable def expHom : G.tangentSpace R →+ G.CPoints R :=
  AddMonoidHom.mk' (fun τ => expC p hT τ) fun τ τ' => expC_add p hT τ τ'

theorem expHom_apply : expHom p hT (G := G) τ = expC p hT τ := rfl

theorem expW_eq_one_of_expC_eq_zero (hτ : expC p hT τ = 0) (i : ℕ) : expW p hT τ i i le_rfl = 1 := by
  have h1 : G.pointsMkAdd (Λ p R i) i (Additive.ofMul (expPoint p hT τ i i le_rfl)) =
      G.pointsMkAdd (Λ p R i) i (Additive.ofMul 1) := by
    rw [← cpointsProj_expC, hτ, map_zero, ofMul_one, map_zero]
  have h2 : expPoint p hT τ i i le_rfl = 1 := (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).mp h1
  have h3 : (Point.toAlgHom (expPoint p hT τ i i le_rfl)).toLinearMap =
      (Point.toAlgHom (1 : G.Point (Λ p R i) i)).toLinearMap := by rw [h2]
  have h4 : (Point.toAlgHom (1 : G.Point (Λ p R i) i)).toLinearMap =
      (1 : WithConv (G.level i →ₗ[R] Λ p R i)).ofConv := rfl
  rw [h4, toAlgHom_expPoint, expAlgHom_toLinearMap, expLin] at h3
  exact WithConv.ext h3

theorem sq_mul_mem_span_of_expC_eq_zero (hτ : expC p hT τ = 0) (x : G.cotangentModule) (n : ℕ) :
    (p : R) ^ 2 * τ x ∈ Ideal.span {(p : R) ^ (n + 2)} := by
  set P := Pconv p hT τ (n + 2) (n + 2) le_rfl with hPdef
  set pb : Λ p R (n + 2) := Ideal.Quotient.mk _ (p : R) with hpb

  have hdvd : ∀ k : ℕ, ∃ c'' : ℤ_[p], PDivEXPRScalars.c p (k + 2) = (p : ℤ_[p]) ^ 3 * c'' := fun k =>
    (pow_dvd_pow (p : ℤ_[p]) (by omega : 3 ≤ k + 2 + 1)).trans
      (PDivEXPRScalars.pow_succ_dvd_c p (Nat.succ_ne_zero (k + 1)))
  choose c'' hc'' using hdvd
  have hc''R : ∀ k : ℕ, algebraMap ℤ_[p] R (PDivEXPRScalars.c p (k + 2)) =
      (p : R) ^ 3 * algebraMap ℤ_[p] R (c'' k) := fun k => by
    rw [hc'', map_mul, map_pow, map_natCast]

  set N : WithConv (G.level (n + 2) →ₗ[R] Λ p R (n + 2)) :=
    ∑ k ∈ Finset.range n, (Ideal.Quotient.mk _ (algebraMap ℤ_[p] R (c'' k)) : Λ p R (n + 2)) • P ^ (k + 1)
    with hN
  have hE : expW p hT τ (n + 2) (n + 2) le_rfl = 1 + pb ^ 2 • (P * (1 + pb • N)) := by
    rw [expW, Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, cΛ_zero, one_smul, pow_one]
    have hc1 : cΛ p R (n + 2) 1 = pb ^ 2 := by
      rw [cΛ, PDivEXPRScalars.c_one, map_pow, map_natCast, map_pow]
    rw [hc1, ← hPdef]
    have hterm : ∀ k ∈ Finset.range n, cΛ p R (n + 2) (k + 1 + 1) • P ^ (k + 1 + 1) =
        pb ^ 2 • (P * (pb • ((Ideal.Quotient.mk _ (algebraMap ℤ_[p] R (c'' k)) : Λ p R (n + 2)) •
          P ^ (k + 1)))) := by
      intro k _
      rw [show k + 1 + 1 = k + 2 from rfl, cΛ, hc''R, map_mul, map_pow, ← hpb, mul_smul_comm,
        mul_smul_comm, ← pow_succ', smul_smul, smul_smul, ← pow_succ]
    rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.mul_sum, ← Finset.smul_sum, ← hN,
      mul_add, mul_one, smul_add]
    abel

  have hunit : IsUnit (1 + pb • N) := by
    have hnil : IsNilpotent (pb • N) := by
      refine ⟨n + 2, ?_⟩
      rw [smul_pow, hpb, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
        zero_smul]
    exact hnil.isUnit_one_add

  have hP0 : pb ^ 2 • P = 0 := by
    have h1 := expW_eq_one_of_expC_eq_zero p hT τ hτ (n + 2)
    rw [hE, add_eq_left, ← smul_mul_assoc] at h1
    obtain ⟨u, hu⟩ := hunit
    rw [← hu] at h1
    have := congrArg (· * (↑u⁻¹ : WithConv (G.level (n + 2) →ₗ[R] Λ p R (n + 2)))) h1
    simpa only [Units.mul_inv_cancel_right, zero_mul] using this

  obtain ⟨⟨a, ha⟩, hax⟩ := (G.augIdeal (n + 2)).toCotangent_surjective (G.cotangentModuleProj (n + 2) x)
  have hcls : G.cotangentClass (n + 2) a = G.cotangentModuleProj (n + 2) x := by
    rw [← hax]
    exact G.cotangentClass_of_mem (n + 2) ⟨a, ha⟩
  have heval : (pb ^ 2 • P) a = pb ^ 2 * Ideal.Quotient.mk _ (τ x) := by
    change pb ^ 2 * der p hT τ (n + 2) (n + 2) le_rfl a = _
    rw [der_apply, hcls, lam_proj]
  rw [hP0] at heval
  change (0 : Λ p R (n + 2)) = _ at heval
  rw [hpb, ← map_pow, ← map_mul] at heval
  exact Ideal.Quotient.eq_zero_iff_mem.mp heval.symm

theorem expC_injective_aux (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ i : ℕ, x ∈ Ideal.span {(p : R) ^ i}) → x = 0)
    (hτ : expC p hT τ = 0) : τ = 0 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  refine hsep (τ x) fun n => ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (sq_mul_mem_span_of_expC_eq_zero p hT τ hτ x n)

  have h1 : (p : R) * ((p : R) * (τ x - (p : R) ^ n * d)) = 0 := by
    have h2 : (p : R) * ((p : R) * (τ x - (p : R) ^ n * d)) =
        (p : R) ^ 2 * τ x - d * (p : R) ^ (n + 2) := by
      ring
    rw [h2, hd, sub_self]
  have h3 : τ x - (p : R) ^ n * d = 0 := htf _ (htf _ h1)
  rw [sub_eq_zero] at h3
  rw [h3]
  exact Ideal.mem_span_singleton'.mpr ⟨d, mul_comm _ _⟩

theorem expHom_injective (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ i : ℕ, x ∈ Ideal.span {(p : R) ^ i}) → x = 0) :
    Function.Injective (expHom p hT (G := G)) := by
  refine (injective_iff_map_eq_zero (expHom p hT (G := G))).mpr fun τ hτ => ?_
  exact expC_injective_aux p hT τ htf hsep hτ

section Pairing

variable {G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
variable (S : Type) [CommRing S] [Algebra R S]

abbrev Oq (i : ℕ) : Type := S ⧸ Ideal.span {(p : S) ^ i}

noncomputable abbrev φq (i : ℕ) : Λ p R i →ₐ[R] Oq p S i :=
  mapModPow R p R (Algebra.ofId R S) i

omit [Fact p.Prime] [Algebra ℤ_[p] R] in
theorem φq_mk (i : ℕ) (t : R) :
    φq p S i (Ideal.Quotient.mk _ t) = algebraMap R (Oq p S i) t := by
  rw [mapModPow_mk, Algebra.ofId_apply]
  rfl

theorem eq_pointMap_expPoint {i w : ℕ} (hiw : i ≤ w) (f : G.Point (Oq p S i) w)
    (hf : G.pointsMkAdd _ w (Additive.ofMul f) =
      G.cpointsProj S i (G.cpointsMap (Algebra.ofId R S) (expHom p hT (G := G) τ))) :
    f = G.pointMap (φq p S i) w (expPoint p hT τ w i hiw) := by
  have h1 : G.cpointsProj S i (G.cpointsMap (Algebra.ofId R S) (expHom p hT (G := G) τ)) =
      G.pointsMkAdd (Oq p S i) w (Additive.ofMul (G.pointMap (φq p S i) w (expPoint p hT τ w i hiw))) := by
    rw [cpointsProj_cpointsMap, expHom_apply, cpointsProj_expC, pointsMap_pointsMkAdd,
      ← G.pointsMkAdd_pointInclLE hiw, ← pointMap_pointInclLE, pointInclLE_expPoint]
  exact (G.pointsMkAdd_eq_pointsMkAdd_iff _ _).mp (hf.trans h1)

theorem toLinearMap_pointMap_expPoint {i w : ℕ} (hiw : i ≤ w) :
    (Point.toAlgHom (G.pointMap (φq p S i) w (expPoint p hT τ w i hiw))).toLinearMap =
      ∑ k ∈ Finset.range i, algebraMap ℤ_[p] R (PDivEXPRScalars.c p k) •
        ((toConv ((φq p S i).toLinearMap ∘ₗ der p hT τ w i hiw)) ^ k).ofConv := by
  rw [toAlgHom_pointMap, toAlgHom_expPoint, AlgHom.comp_toLinearMap, expAlgHom_toLinearMap, expLin,
    expW, ofConv_sum]
  have hsum : ∀ (F : ℕ → (G.level w →ₗ[R] Λ p R i)) (s : Finset ℕ),
      (φq p S i).toLinearMap ∘ₗ (∑ k ∈ s, F k) = ∑ k ∈ s, (φq p S i).toLinearMap ∘ₗ F k := by
    intro F s
    refine LinearMap.ext fun a => ?_
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ofConv_smul]
  have h1 : (φq p S i).toLinearMap ∘ₗ (cΛ p R i k • (Pconv p hT τ w i hiw ^ k).ofConv) =
      algebraMap ℤ_[p] R (PDivEXPRScalars.c p k) •
        ((φq p S i).toLinearMap ∘ₗ (Pconv p hT τ w i hiw ^ k).ofConv) := by
    refine LinearMap.ext fun a => ?_
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul, cΛ, φq_mk,
      Algebra.smul_def]
  rw [h1, algHom_comp_convPow, ofConv_toConv]

noncomputable def Φ (i w : ℕ) (hiw : i ≤ w) : S ⊗[R] G.Cotangent w →ₗ[R] Oq p S i :=
  LinearMap.mul' R (Oq p S i) ∘ₗ
    TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})).toLinearMap
      ((φq p S i).toLinearMap ∘ₗ lam p hT τ w i hiw)

omit [Fact p.Prime] [Algebra ℤ_[p] R] in
theorem Φ_tmul (i w : ℕ) (hiw : i ≤ w) (o : S) (y : G.Cotangent w) :
    Φ p hT τ S i w hiw (o ⊗ₜ[R] y) = Ideal.Quotient.mk _ o * φq p S i (lam p hT τ w i hiw y) := by
  simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
    AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]

omit [Fact p.Prime] [Algebra ℤ_[p] R] in

theorem Φ_charDiff (i w : ℕ) (hiw : i ≤ w) (ψ : G'.Point S w) :
    Φ p hT τ S i w hiw (D.charDiff S w ψ) =
      PDivEXPRPair.epair D (Oq p S i) w
        (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) w ψ)
        ((φq p S i).toLinearMap ∘ₗ der p hT τ w i hiw) := by
  rw [D.charDiff_eq_sum, map_sum, PDivEXPRPair.epair]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Φ_tmul, mul_comm]
  rfl

omit [Fact p.Prime] [Algebra ℤ_[p] R] in

theorem Φ_lTensor_proj (i w : ℕ) (hiw : i ≤ w) (z : S ⊗[R] G.cotangentModule) :
    Φ p hT τ S i w hiw ((G.cotangentModuleProj w).lTensor S z) =
      Ideal.Quotient.mk _ (TensorProduct.rid R S (τ.lTensor S z)) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero, LinearEquiv.map_zero,
      RingHom.map_zero]
  | tmul o x =>
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Φ_tmul, lam_proj, φq_mk, TensorProduct.rid_tmul,
      Algebra.smul_def, RingHom.map_mul, mul_comm]
    rfl
  | add x y hx hy =>
    rw [LinearMap.map_add, LinearMap.map_add, hx, hy, LinearMap.map_add, LinearEquiv.map_add,
      RingHom.map_add]

theorem pair_pointMap_expPoint (i w : ℕ) (hiw : i ≤ w) (ψ : G'.Point S w)
    (z : S ⊗[R] G.cotangentModule)
    (hz : (G.cotangentModuleProj w).lTensor S z = D.charDiff S w ψ) :
    D.pair _ w (G.pointMap (φq p S i) w (expPoint p hT τ w i hiw))
        (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) w ψ) =
      ∑ k ∈ Finset.range i, algebraMap R _ (algebraMap ℤ_[p] R (PDivEXPRScalars.c p k)) *
        (Ideal.Quotient.mk (Ideal.span {(p : S) ^ i})
          (TensorProduct.rid R S (τ.lTensor S z))) ^ k := by
  set ψq := G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) w ψ
  have hone : PDivEXPRPair.epair D (Oq p S i) w ψq (1 : WithConv (G.level w →ₗ[R] Oq p S i)).ofConv = 1 :=
    PDivEXPRPair.epair_convOne D (Oq p S i) w ψq
  rw [← PDivEXPRPair.epair_point, toLinearMap_pointMap_expPoint, PDivEXPRPair.epair_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PDivEXPRPair.epair_smul_base, PDivEXPRPair.epair_convPow D (Oq p S i) w ψq _ k hone,
    ofConv_toConv, ← Φ_charDiff, ← hz, Φ_lTensor_proj]

end Pairing
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.PDivEXPRConv"

end PDivEXPR
p2m_reactivate "P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.PDivEXPRConv P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq.PDivEXPR"

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [Algebra ℤ_[p] R]
    (htf : ∀ x : R, (p : R) * x = 0 → x = 0)
    (hsep : ∀ x : R, (∀ i : ℕ, x ∈ Ideal.span {(p : R) ^ i}) → x = 0)
    {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')
    (hsurj : ∀ v, Function.Surjective (G.cotangentModuleProj v))
    (hker : ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule)) :
    ∃ (m : ℕ) (c : ℕ → R) (e : G.tangentSpace R →+ G.CPoints R),
      (∀ k : ℕ, (k.factorial : R) * c k = (p : R) ^ (m * k)) ∧
      Function.Injective e ∧
      ∀ (S : Type) [CommRing S] [Algebra R S] (τ : G.tangentSpace R) (i w : ℕ), i ≤ w →
        ∀ (f : G.Point (S ⧸ Ideal.span {(p : S) ^ i}) w),
          G.pointsMkAdd _ w (Additive.ofMul f) =
            G.cpointsProj S i (G.cpointsMap (Algebra.ofId R S) (e τ)) →
        ∀ (ψ : G'.Point S w) (z : S ⊗[R] G.cotangentModule),
          (G.cotangentModuleProj w).lTensor S z = D.charDiff S w ψ →
          D.pair _ w f (G'.pointMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) w ψ) =
            ∑ k ∈ Finset.range i,
              algebraMap R _ (c k) *
                (Ideal.Quotient.mk (Ideal.span {(p : S) ^ i})
                  (TensorProduct.rid R S (τ.lTensor S z))) ^ k := by
  have hT : PDivEXPR.Tower p G := ⟨hsurj, hker⟩
  refine ⟨2, fun k => algebraMap ℤ_[p] R (PDivEXPRScalars.c p k), PDivEXPR.expHom p hT, ?_,
    PDivEXPR.expHom_injective p hT htf hsep, ?_⟩
  · intro k
    rw [← map_natCast (algebraMap ℤ_[p] R) k.factorial, ← map_mul, PDivEXPRScalars.factorial_mul_c, map_pow,
      map_natCast]
  · intro S _ _ τ i w hiw f hf ψ z hz
    rw [PDivEXPR.eq_pointMap_expPoint p hT τ S hiw f hf]
    exact PDivEXPR.pair_pointMap_expPoint p hT τ D S i w hiw ψ z hz

end S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq
end P2MW
export P2MW.S_PDivisibleGroup_CartierDuality_exists_addMonoidHom_tangentSpace_cpoints_pair_eq_sum_pow_of_ker_cotangentModuleProj_eq (solution)
