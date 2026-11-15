-- Prove2me | solution 1 for TimeSpaceMA.shortLosslessCondenser
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-14T20:31:32.84309+00:00
-- url     : https://prove2.me/submissions/addfe8ae-767c-43b5-95e5-85ac30022152

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
import Definitions.Def_TimeSpaceMA_GUVFieldOperations
import Definitions.Def_TimeSpaceMA_TUZExtractorComponents
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_TimeSpaceMA_GUV_fieldOperations_exists


namespace TimeSpaceMA.GUV
open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

def digit (h j i : ℕ) : ℕ := j / h ^ i % h

theorem digit_lt {h : ℕ} (hh : 0 < h) (j i : ℕ) : digit h j i < h :=
  Nat.mod_lt _ hh

theorem sum_digits {h j m : ℕ} (hh : 0 < h) (hj : j < h ^ m) :
    ∑ i : Fin m, digit h j i * h ^ i.val = j := by
  induction m generalizing j with
  | zero => simp at hj; simp [hj]
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hj' : j / h < h ^ m := Nat.div_lt_of_lt_mul (by simpa [pow_succ, mul_comm] using hj)
    have hs (i : Fin m) : digit h j i.succ * h ^ i.succ.val =
        h * (digit h (j / h) i * h ^ i.val) := by
      simp only [digit, Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul]
      rw [mul_comm (h ^ i.val) h]
      ac_rfl
    simp_rw [hs]
    rw [← Finset.mul_sum, ih hj']
    simpa [digit] using Nat.mod_add_div j h

def digitProduct {M : Type*} [CommMonoid M] {m : ℕ} (h j : ℕ) (z : Fin m → M) : M :=
  ∏ i, z i ^ digit h j i.val

theorem digitProduct_powers {M : Type*} [CommMonoid M] {h j m : ℕ} (hh : 0 < h)
    (hj : j < h ^ m) (x : M) :
    digitProduct h j (fun i : Fin m => x ^ h ^ i.val) = x ^ j := by
  unfold digitProduct
  simp_rw [← pow_mul, mul_comm (h ^ _) (digit h j _)]
  rw [Finset.prod_pow_eq_pow_sum, sum_digits hh hj]

theorem interpolate {m K A h : ℕ} {T : Finset (F × (Fin m → F))}
    (hcount : T.card < K * A) :
    ∃ p : Fin K → F[X], (∃ j, p j ≠ 0) ∧ (∀ j, (p j).natDegree ≤ A - 1) ∧
      ∀ z ∈ T, ∑ j, (p j).eval z.1 * digitProduct h j.val z.2 = 0 := by
  classical
  let W (z : ↥T) (ij : Fin K × Fin A) :=
    z.val.1 ^ ij.2.val * digitProduct h ij.1.val z.val.2
  let M : ((Fin K × Fin A) → F) →ₗ[F] (↥T → F) :=
    {toFun := fun c z => ∑ ij, c ij * W z ij
     map_add' := fun c d => by ext z; simp [add_mul, Finset.sum_add_distrib]
     map_smul' := fun a c => by
       ext z
       simp [mul_assoc, Finset.mul_sum]}
  have hker : M.ker ≠ ⊥ := by
    intro he
    have hdim := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    simpa only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
      not_le.mpr hcount] using hdim
  obtain ⟨c, hc, hnz⟩ := (Submodule.ne_bot_iff M.ker).mp hker
  let p (j : Fin K) : F[X] := ∑ i : Fin A, monomial i.val (c (j,i))
  refine ⟨p, ?_, ?_, ?_⟩
  · by_contra! hp
    apply hnz
    ext ⟨j,i⟩
    have hh := congrArg (fun q : F[X] => q.coeff i.val) (hp j)
    simp only [p, finsetSum_coeff, coeff_monomial, coeff_zero] at hh
    have hh' : (∑ i' : Fin A, if i'.val = i.val then c (j,i') else 0) = c (j,i) := by
      simp [Fin.ext_iff.symm]
    exact hh'.symm.trans hh
  · intro j
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_monomial_le _).trans (by have := i.isLt; omega)
  · intro z hz
    have he := congrFun (show M c = 0 from LinearMap.mem_ker.mp hc) ⟨z,hz⟩
    simp only [M, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, W] at he
    rw [Fintype.sum_prod_type] at he
    simpa only [p, eval_finsetSum, eval_monomial, Finset.sum_mul, mul_assoc] using he

theorem interpolate_residue {m K A h : ℕ} {T : Finset (F × (Fin m → F))}
    (hcount : T.card < K * A) {E : F[X]} (hmon : E.Monic) 
    (hdegree : 0 < E.natDegree) (hroot : ∀ y : F, E.eval y ≠ 0) :
    ∃ p : Fin K → F[X], (∃ j, AdjoinRoot.mk E (p j) ≠ 0) ∧
      (∀ j, (p j).natDegree ≤ A - 1) ∧
      ∀ z ∈ T, ∑ j, (p j).eval z.1 * digitProduct h j.val z.2 = 0 := by
  classical
  let P (N : ℕ) : Prop := ∃ p : Fin K → F[X], (∃ j, p j ≠ 0) ∧
      (∀ j, (p j).natDegree ≤ N) ∧
      ∀ z ∈ T, ∑ j, (p j).eval z.1 * digitProduct h j.val z.2 = 0
  have hstart : P (A - 1) := interpolate hcount
  have hex : ∃ N, P N := ⟨_, hstart⟩
  let N := Nat.find hex
  have hN : N ≤ A - 1 := Nat.find_min' hex hstart
  obtain ⟨p, hp, hdeg, hval⟩ := Nat.find_spec hex
  refine ⟨p, ?_, fun j => (hdeg j).trans hN, hval⟩
  by_contra! h
  have hdvd (j) : E ∣ p j := AdjoinRoot.mk_eq_zero.mp (h j)
  let d (j) := p j /ₘ E
  have heq (j) : E * d j = p j := by
    have hh := modByMonic_add_div (p j) E
    rwa [(modByMonic_eq_zero_iff_dvd hmon).mpr (hdvd j), zero_add] at hh
  obtain ⟨j, hj⟩ := hp
  have hnon : d j ≠ 0 := by
    intro hf
    apply hj
    rw [←heq j, hf, mul_zero]
  have hpos : 0 < N := by
    have hE := natDegree_le_of_dvd (hdvd j) hj
    have := hdeg j
    omega
  have hsmaller : P (N - 1) := by
    refine ⟨d, ⟨j, hnon⟩, ?_, ?_⟩
    · intro i
      have hdi := hdeg i
      dsimp [d]
      rw [natDegree_divByMonic (p i) hmon]
      omega
    · intro z hz
      have hprev := hval z hz
      simp_rw [← heq, eval_mul, mul_assoc, ← Finset.mul_sum] at hprev
      exact (mul_eq_zero.mp hprev).resolve_left (hroot z.1)
  have := Nat.find_min' hex hsmaller
  change N ≤ N - 1 at this
  omega


theorem image_card_ge [Fintype F] [DecidableEq F] {m h b : ℕ} (hh : 0 < h)
    {E : F[X]} (hmon : E.Monic) (hirr : Irreducible E)
    (hdegree : b < E.natDegree) (hroot : ∀ y : F, E.eval y ≠ 0)
    (g : F[X] → Fin m → F[X])
    (S : Finset F[X]) (hK : S.card ≤ h ^ m)
    (hS : ∀ f ∈ S, f.natDegree ≤ b)
    (hg : ∀ f ∈ S, ∀ i : Fin m, (g f i).natDegree ≤ b)
    (hgmod : ∀ f ∈ S, ∀ i : Fin m,
      AdjoinRoot.mk E (g f i) = AdjoinRoot.mk E f ^ h ^ i.val) :
    S.card * (Fintype.card F - m * (h - 1) * b) ≤
      ((S ×ˢ (Finset.univ : Finset F)).image
        (fun z => (z.2, fun i => (g z.1 i).eval z.2))).card := by
  classical
  let : Fact (Irreducible E) := ⟨hirr⟩
  let T := (S ×ˢ (Finset.univ : Finset F)).image
    (fun z => (z.2, fun i => (g z.1 i).eval z.2))
  let B := m * (h - 1) * b
  let A := Fintype.card F - B
  change S.card * A ≤ T.card
  by_contra! hsmall
  have hA : 0 < A := Nat.pos_of_ne_zero (by intro H; simp [H] at hsmall)
  obtain ⟨p, hp, hpdeg, hpval⟩ := interpolate_residue (h := h) hsmall hmon
    (by omega) hroot
  let C (j : Fin S.card) := AdjoinRoot.mk E (p j)
  let Q : Polynomial (AdjoinRoot E) := ∑ j : Fin S.card, monomial j.val (C j)
  have hQ : Q ≠ 0 := by
    obtain ⟨j, hj⟩ := hp
    intro hz
    have hs := congrArg (fun a : Polynomial (AdjoinRoot E) => a.coeff j.val) hz
    simp only [Q, finsetSum_coeff, coeff_monomial, coeff_zero] at hs
    have hs' : (∑ i : Fin S.card, if i.val = j.val then C i else 0) = C j := by
      simp [Fin.ext_iff.symm]
    exact hj (hs'.symm.trans hs)
  have hQdeg : Q.natDegree ≤ S.card - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (by have := j.isLt; omega)
  have hfroot (f : F[X]) (hf : f ∈ S) : Q.IsRoot (AdjoinRoot.mk E f) := by
    let R : F[X] := ∑ j : Fin S.card, p j * digitProduct h j.val (g f)
    have hRdeg : R.natDegree ≤ A - 1 + B := by
      apply natDegree_sum_le_of_forall_le
      intro j hj
      apply natDegree_mul_le.trans (Nat.add_le_add (hpdeg j) _)
      unfold digitProduct
      apply (natDegree_prod_le ..).trans
      have hle (i : Fin m) :
          ((g f i) ^ digit h j.val i.val).natDegree ≤ (h - 1) * b := by
        have hdi := digit_lt hh j.val i.val
        exact natDegree_pow_le.trans (Nat.mul_le_mul (by omega) (hg f hf i))
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)
      simpa [B, mul_assoc] using hsum
    have hReval (y : F) : R.eval y = 0 := by
      have he := hpval (y, fun i => (g f i).eval y)
        (Finset.mem_image.mpr ⟨(f,y), Finset.mem_product.mpr
          ⟨hf, Finset.mem_univ _⟩, rfl⟩)
      simpa only [R, eval_finsetSum, eval_mul, digitProduct, eval_prod, eval_pow] using he
    have hR : R = 0 := by
      by_contra hne
      have hq : (Finset.univ : Finset F) ⊆ R.roots.toFinset := by
        intro y hy
        exact Multiset.mem_toFinset.mpr ((mem_roots hne).mpr (hReval y))
      have hq' := (Finset.card_le_card hq).trans
        ((Multiset.toFinset_card_le R.roots).trans R.card_roots')
      simp only [Finset.card_univ] at hq'
      dsimp [A] at hRdeg hA
      omega
    have hmap (j : Fin S.card) :
        AdjoinRoot.mk E (digitProduct h j.val (g f)) = AdjoinRoot.mk E f ^ j.val := by
      unfold digitProduct
      simp only [map_prod, map_pow, hgmod f hf]
      apply digitProduct_powers hh (j.isLt.trans_le hK)
    have hzero := congrArg (AdjoinRoot.mk E) hR
    change Q.eval (AdjoinRoot.mk E f) = 0
    simpa only [Q, C, eval_finsetSum, eval_monomial, R, map_sum, map_mul, map_zero, hmap]
      using hzero
  have hinj : Set.InjOn (AdjoinRoot.mk E) ↑S := by
    intro x hx y hy he
    by_contra hne
    have hnz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hdiv := natDegree_le_of_dvd (AdjoinRoot.mk_eq_mk.mp he) hnz
    have hx' : x.natDegree ≤ b := hS _ hx
    have hy' : y.natDegree ≤ b := hS _ hy
    exact (not_le_of_gt hdegree) (hdiv.trans ((natDegree_sub_le x y).trans
      (max_le hx' hy')))
  have hmapS : (S.image (AdjoinRoot.mk E)).card ≤ Q.roots.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hQ).mpr (hfroot f hf))
  rw [Finset.card_image_of_injOn hinj] at hmapS
  have := hmapS.trans ((Multiset.toFinset_card_le Q.roots).trans
    (Q.card_roots'.trans hQdeg))
  have hpos : 0 < S.card := Nat.pos_of_ne_zero (by intro H; simp [H] at hsmall)
  omega

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV
open Polynomial

variable {F : Type*} [Field F]

theorem iterate_frob {L : Type*} [CommMonoid L] {h : ℕ} {x z : L}
    (hx : x ^ h = z * x) (hz : z ^ h = z) (i : ℕ) :
    x ^ (h ^ i) = z ^ i * x := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ h, pow_mul, ih, mul_pow, pow_right_comm z, hz, hx,
      pow_succ z, mul_assoc]

theorem binomial_irreducible [Fintype F] {h : ℕ} (hh : 1 < h)
    (hc : (h - 1).Coprime 2) (hF : Fintype.card F = h ^ 2)
    {z : F} (hzord : orderOf z = h - 1) :
    Irreducible (X ^ (h - 1) - C z : F[X]) := by
  classical
  have hb : 0 < h - 1 := by omega
  have hnu : ¬ IsUnit (X ^ (h - 1) - C z : F[X]) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hb, Nat.cast_eq_zero]
    exact hb.ne'
  have hnon : (X ^ (h - 1) - C z : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hb z
  obtain ⟨g, hg, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hnu hnon
  let : Fact (Irreducible g) := ⟨hg⟩
  let L := AdjoinRoot g
  let α : L := AdjoinRoot.root g
  let φ : F →+* L := AdjoinRoot.of g
  have hgz : α ^ (h - 1) = φ z := by
    have hv := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hdiv (AdjoinRoot.eval₂_root g)
    simpa only [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] using hv
  have hζ : z ^ (h - 1) = 1 := hzord ▸ pow_orderOf_eq_one z
  have hzne : z ≠ 0 := by
    intro he
    rw [he, zero_pow hb.ne'] at hζ
    exact zero_ne_one hζ
  have ha : α ≠ 0 := by
    intro he
    rw [he, zero_pow hb.ne'] at hgz
    exact hzne (φ.injective (hgz.symm.trans φ.map_zero.symm))
  have hh' : h = h - 1 + 1 := by omega
  have hzfixed : (φ z) ^ h = φ z := by
    rw [← map_pow, hh', pow_succ, hζ, one_mul]
  have hafixed : α ^ h = φ z * α := by
    rw [hh', pow_succ, hgz]
  let d := g.natDegree
  let : Fintype L := Fintype.ofEquiv (Fin (AdjoinRoot.powerBasis hg.ne_zero).dim → F)
    (AdjoinRoot.powerBasis hg.ne_zero).basis.equivFun.symm.toEquiv
  have hL : Fintype.card L = h ^ (2 * d) := by
    change Fintype.card (AdjoinRoot g) = _
    rw [Module.card_eq_pow_finrank (K := F), (AdjoinRoot.powerBasis hg.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim hg.ne_zero, hF, ← pow_mul]
  have hfin := FiniteField.pow_card α
  rw [hL, iterate_frob hafixed hzfixed] at hfin
  have hpower : z ^ (2 * d) = 1 := by
    apply φ.injective
    rw [map_pow, map_one]
    exact mul_right_cancel₀ ha (hfin.trans (one_mul α).symm)
  have hdvd : h - 1 ∣ d :=
    hc.dvd_of_dvd_mul_left (hzord ▸ orderOf_dvd_iff_pow_eq_one.mpr hpower)
  have dpos : 0 < d := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hg)
  have hbig : h - 1 ≤ d := Nat.le_of_dvd dpos hdvd
  exact (associated_of_dvd_of_natDegree_le hdiv hnon (by simpa using hbig)).irreducible hg

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV
open Polynomial
open scoped BigOperators

variable {K F : Type*} [Field K] [Field F]

theorem natDegree_fold_le (z : F) (i : ℕ) (f : F[X]) :
    (fold z i f).natDegree ≤ f.natDegree := by
  unfold fold
  apply natDegree_comp_le.trans
  have hdeg : (C (z ^ i) * X).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    simp
  simpa using Nat.mul_le_mul_left f.natDegree hdeg

theorem mk_fold_eq_power [CharP F 2] [Fintype K] (φ : K →+* F) {c : ℕ}
    (hK : Fintype.card K = 2 ^ c) (z : K) (f : K[X]) (i : ℕ)
    (hi : Irreducible (X ^ (2 ^ c - 1) - C (φ z))) :
    let E : F[X] := X ^ (2 ^ c - 1) - C (φ z)
    AdjoinRoot.mk E (fold (φ z) i (f.map φ)) =
      AdjoinRoot.mk E (f.map φ) ^ (2 ^ c) ^ i := by
  let h := 2 ^ c
  let E : F[X] := X ^ (h - 1) - C (φ z)
  change AdjoinRoot.mk E (fold (φ z) i (f.map φ)) =
    AdjoinRoot.mk E (f.map φ) ^ h ^ i
  let : Fact (Irreducible E) := ⟨hi⟩
  let L := AdjoinRoot E
  let α : L := AdjoinRoot.root E
  let ψ : K →+* L := (AdjoinRoot.of E).comp φ
  let : CharP L 2 := CharP.of_ringHom_of_ne_zero (AdjoinRoot.of E) 2 (by decide)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha : α ^ (h - 1) = ψ z := by
    simpa only [E, α, ψ, eval₂_sub, eval₂_pow, eval₂_C, eval₂_X,
      sub_eq_zero, RingHom.comp_apply] using AdjoinRoot.eval₂_root E
  have hpos : 0 < h := by dsimp [h]; positivity
  have hsucc : h - 1 + 1 = h := by omega
  have hα : α ^ h = ψ z * α := by rw [← hsucc, pow_succ, ha]
  have hfixed (x : K) : (ψ x) ^ h = ψ x := by
    have he := FiniteField.pow_card x
    rw [hK] at he
    exact (map_pow ψ x h).symm.trans (congrArg ψ he)
  have hfixed_iter (a : K) (j : ℕ) : ψ a ^ h ^ j = ψ a := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ h, pow_mul, ih, hfixed]
  have hz := iterate_frob hα (hfixed z) i
  let P := iterateFrobenius L 2 (c * i)
  have P_eq (x : L) : P x = x ^ h ^ i := by
    simp only [P, iterateFrobenius_def, h, pow_mul]
  let ev := eval₂RingHom ψ α
  let ev' := eval₂RingHom ψ (ψ z ^ i * α)
  have hev : ev' = P.comp ev := by
    apply Polynomial.ringHom_ext
    · intro a
      change eval₂ ψ (ψ z ^ i * α) (C a) = P (eval₂ ψ α (C a))
      rw [eval₂_C, eval₂_C, P_eq]
      exact (hfixed_iter a i).symm
    · change eval₂ ψ (ψ z ^ i * α) X = P (eval₂ ψ α X)
      rw [eval₂_X, eval₂_X, P_eq, hz]
  have hmk (q : F[X]) : AdjoinRoot.mk E q = eval₂ (AdjoinRoot.of E) α q := by
    exact (AdjoinRoot.aeval_eq q).symm
  rw [hmk, hmk]
  simp only [fold, eval₂_comp, eval₂_mul, eval₂_X]
  have hmap (x : L) : eval₂ (AdjoinRoot.of E) x (f.map φ) = eval₂ ψ x f := by
    simp only [ψ, eval₂_eq_eval_map, Polynomial.map_map]
  rw [hmap, hmap]
  rw [eval₂_C, map_pow]
  change ev' f = ev f ^ h ^ i
  rw [hev, RingHom.comp_apply, P_eq]

theorem binomial_eval_ne_zero {z y : F} {h : ℕ} (hh : 2 < h)
    (hi : Irreducible (X ^ (h - 1) - C z : F[X])) :
    (X ^ (h - 1) - C z).eval y ≠ 0 := by
  intro he
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr he
  rcases hi.isUnit_or_isUnit hq with hunit | hunit
  · exact not_isUnit_X_sub_C _ hunit
  · have hqne : q ≠ 0 := hunit.ne_zero
    have hd : q.natDegree = 0 := by
      have hd := Polynomial.isUnit_iff_degree_eq_zero.mp hunit
      rw [degree_eq_natDegree hqne, Nat.cast_eq_zero] at hd
      exact hd
    have hdeg := congrArg (Polynomial.natDegree (R := F)) hq
    rw [natDegree_X_pow_sub_C, natDegree_mul (X_sub_C_ne_zero _) hqne,
      natDegree_X_sub_C, hd, add_zero] at hdeg
    omega

theorem rs_image_card_ge [CharP F 2] [Fintype K] [Fintype F] [DecidableEq F]
    (φ : K →+* F) {c m b : ℕ} (hc : 1 < c)
    (hK : Fintype.card K = 2 ^ c) (hF : Fintype.card F = (2 ^ c)^2)
    {ζ : K} (hzord : orderOf ζ = 2 ^ c - 1)
    (hb : b < 2 ^ c - 1) (S : Finset K[X]) (hS : ∀ f ∈ S, f.natDegree ≤ b)
    (hKmax : S.card ≤ (2 ^ c) ^ m) :
    S.card * (Fintype.card F - m * (2 ^ c - 1) * b) ≤
      ((S ×ˢ (Finset.univ : Finset F)).image
        (fun z => (z.2, fun i : Fin m => (fold (φ ζ) i.val (z.1.map φ)).eval z.2))).card := by
  classical
  let h := 2 ^ c
  have hh : 2 < h := by
    change 2 < 2 ^ c
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hc
  have hcop : (h - 1).Coprime 2 := by
    rw [Nat.coprime_two_right]
    have hm : h % 2 = 0 := by
      change 2 ^ c % 2 = 0
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    rw [Nat.odd_iff]
    omega
  let E : F[X] := X ^ (h - 1) - C (φ ζ)
  have hord : orderOf (φ ζ) = h - 1 :=
    (orderOf_injective φ.toMonoidHom φ.injective ζ).trans hzord
  have hi : Irreducible E := binomial_irreducible (by omega) hcop hF hord
  let S' := S.image (Polynomial.map φ)
  have hmapinj := Polynomial.map_injective φ φ.injective
  have hS' : S'.card = S.card := Finset.card_image_of_injective _ hmapinj
  have he := image_card_ge (F := F) (m := m) (b := b) (h := h) (by omega)
    (E := E) (monic_X_pow_sub_C _ (by omega)) hi
    (by simpa [E] using hb) (fun y => binomial_eval_ne_zero hh hi)
    (fun f i => fold (φ ζ) i.val f) S' (by simpa [hS'] using hKmax)
    (fun f hf => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      exact natDegree_map_le.trans (hS g hg))
    (fun f hf i => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      exact (natDegree_fold_le _ _ _).trans (natDegree_map_le.trans (hS g hg)))
    (fun f hf i => by
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hf
      exact mk_fold_eq_power φ hK ζ g i.val hi)
  rw [hS'] at he
  apply he.trans
  apply Finset.card_le_card
  intro x hx
  obtain ⟨⟨g,y⟩, hg, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hg).1
  exact Finset.mem_image.mpr ⟨(f,y), Finset.mem_product.mpr
    ⟨hf, Finset.mem_univ _⟩, rfl⟩

end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.GUV

variable {X Y Seed : Type} [Fintype Seed] [Fintype Y] [DecidableEq Y]

theorem exact_condenses_of_image_card (C : X → Seed → Y) (S : Finset X) (δ : ℝ)
    (hpos : 0 < S.card * Fintype.card Seed)
    (hroom : S.card * Fintype.card Seed ≤ Fintype.card Y)
    (himage : let P := S ×ˢ (Finset.univ : Finset Seed);
      (1 - δ) * (P.card : ℝ) ≤ ((P.image fun p => C p.1 p.2).card : ℝ)) :
    ∃ q : Y → ℝ, (∀ y, 0 ≤ q y ∧ q y ≤ 1 / (S.card * Fintype.card Seed : ℝ)) ∧
      ∑ y, q y = 1 ∧ CondensesFlatEvents C S q δ := by
  classical
  let P := S ×ˢ (Finset.univ : Finset Seed)
  let C' (p : X × Seed) := C p.1 p.2
  let I := P.image C'
  have hP : P.card = S.card * Fintype.card Seed := by simp [P]
  have hIP : I.card ≤ P.card := Finset.card_image_le
  have hextra : P.card - I.card ≤ Iᶜ.card := by
    rw [Finset.card_compl]
    exact Nat.sub_le_sub_right (hP ▸ hroom) _
  obtain ⟨A, hA, hcA⟩ := Finset.exists_subset_card_eq hextra
  have hdis : Disjoint I A :=
    Finset.disjoint_left.mpr (fun y hy ha => Finset.mem_compl.mp (hA ha) hy)
  let J := I ∪ A
  have hJ : J.card = P.card := by
    rw [Finset.card_union_of_disjoint hdis, hcA, Nat.add_sub_of_le hIP]
  let d : ℝ := P.card
  have hd : 0 < d := by
    dsimp [d]
    rw [hP]
    exact_mod_cast hpos
  let q (y : Y) : ℝ := if y ∈ J then 1 / d else 0
  refine ⟨q, ?_, ?_, ?_⟩
  · intro y
    have h0 : 0 ≤ 1 / d := by positivity
    have heq : d = (S.card : ℝ) * Fintype.card Seed := by dsimp [d]; exact_mod_cast hP
    rw [← heq]
    by_cases hy : y ∈ J
    · exact ⟨by simpa only [q, if_pos hy] using h0, by simp only [q, if_pos hy, le_refl]⟩
    · exact ⟨by simp only [q, if_neg hy, le_refl], by simpa only [q, if_neg hy] using h0⟩
  · have heq : (∑ y, q y) = ∑ _y ∈ J, 1 / d := by
      simp [q]
    rw [heq, Finset.sum_const, nsmul_eq_mul, hJ]
    change d * (1 / d) = 1
    field_simp
  · intro U
    let Q := P.filter (fun p => C' p ∈ U)
    have hJU : (J ∩ U).card + (P \ Q).card ≥ I.card := by
      let M := (P \ Q).image C'
      have hsub : I ⊆ (J ∩ U) ∪ M := by
        intro y hy
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
        by_cases hU : C' p ∈ U
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
            ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩), hU⟩)
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr
            ⟨p, Finset.mem_sdiff.mpr ⟨hp, by simp [Q, hU]⟩, rfl⟩)
      exact (Finset.card_le_card hsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _))
    have hsubQ : Q ⊆ P := Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset hsubQ] at hJU
    have hqU : ∑ y ∈ U, q y = ((J ∩ U).card : ℝ) / d := by
      simp [q, Finset.inter_comm, div_eq_mul_inv]
    have hle : (Q.card : ℝ) + I.card ≤ P.card + (J ∩ U).card := by
      have hQ := Finset.card_le_card hsubQ
      exact_mod_cast (show Q.card + I.card ≤ P.card + (J ∩ U).card by omega)
    change (Q.card : ℝ) / ((S.card : ℝ) * Fintype.card Seed) - _ ≤ _
    rw [show (S.card : ℝ) * Fintype.card Seed = d by dsimp [d]; exact_mod_cast hP.symm,
      hqU, ← sub_div]
    apply (div_le_iff₀ hd).mpr
    change (1 - δ) * d ≤ (I.card : ℝ) at himage
    change (Q.card : ℝ) - (J ∩ U).card ≤ δ * d
    change (Q.card : ℝ) + I.card ≤ d + (J ∩ U).card at hle
    linarith

private theorem avg_over_powerset {K : ℕ} {S : Finset X} (hK : 0 < K) (hS : K ≤ S.card)
    (a : X → ℝ) :
    (∑ U ∈ S.powersetCard K, ∑ x ∈ U, a x) =
      ((S.card - 1).choose (K - 1) : ℝ) * ∑ x ∈ S, a x := by
  classical
  have hsum (U : Finset X) (hU : U ∈ S.powersetCard K) :
      ∑ x ∈ U, a x = ∑ x ∈ S, if x ∈ U then a x else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    have hs := (Finset.mem_powersetCard.mp hU).1
    ext x
    exact ⟨fun hx => Finset.mem_filter.mpr ⟨hs hx, hx⟩,
      fun hx => (Finset.mem_filter.mp hx).2⟩
  rw [Finset.sum_congr rfl hsum, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcnt := Finset.card_filter_powersetCard_subset {x} S K
    (Finset.singleton_subset_iff.mpr hx) (by simpa using (show 1 ≤ K by omega))
  rw [show (S.powersetCard K).filter (fun U => x ∈ U) =
      (S.powersetCard K).filter (fun U => {x} ⊆ U) by ext U; simp]
  simpa only [Finset.card_singleton, hcnt]

private theorem avg_fiber_count (C : X → Seed → Y) {K : ℕ} {S : Finset X}
    (hK : 0 < K) (hS : K ≤ S.card) (V : Finset Y) :
    (∑ U ∈ S.powersetCard K,
      (((U ×ˢ (Finset.univ : Finset Seed)).filter (fun p => C p.1 p.2 ∈ V)).card : ℝ)) =
      ((S.card - 1).choose (K - 1) : ℝ) *
      (((S ×ˢ (Finset.univ : Finset Seed)).filter (fun p => C p.1 p.2 ∈ V)).card : ℝ) := by
  classical
  let a (x : X) : ℝ := ∑ r : Seed, if C x r ∈ V then 1 else 0
  have hcount (U : Finset X) :
      (((U ×ˢ (Finset.univ : Finset Seed)).filter (fun p => C p.1 p.2 ∈ V)).card : ℝ)
       = ∑ x ∈ U, a x := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [a]
    apply Finset.sum_congr rfl
    intro r hr
    split <;> norm_num
  simp only [hcount]
  exact avg_over_powerset hK hS a

theorem condenses_of_exact (C : X → Seed → Y) {K : ℕ} (hK : 0 < K)
    (hD : 0 < Fintype.card Seed) (δ : ℝ)
    (hExact : ∀ U : Finset X, U.card = K →
      ∃ q : Y → ℝ, (∀ y, 0 ≤ q y ∧ q y ≤ 1 / (K * Fintype.card Seed : ℝ)) ∧
        ∑ y, q y = 1 ∧ CondensesFlatEvents C U q δ)
    (S : Finset X) (hS : K ≤ S.card) :
    ∃ q : Y → ℝ, (∀ y, 0 ≤ q y ∧ q y ≤ 1 / (K * Fintype.card Seed : ℝ)) ∧
      ∑ y, q y = 1 ∧ CondensesFlatEvents C S q δ := by
  classical
  let Ω := S.powersetCard K
  let M : ℝ := Ω.card
  let D : ℝ := Fintype.card Seed
  let cap : ℝ := 1 / (K * D)
  have hM : 0 < M := by dsimp [M, Ω]; exact_mod_cast Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hS)
  have hDr : 0 < D := by dsimp [D]; exact_mod_cast hD
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  have hSr : 0 < (S.card : ℝ) := by exact_mod_cast hK.trans_le hS
  have hex (U : Finset X) : U ∈ Ω → ∃ q : Y → ℝ,
      (∀ y, 0 ≤ q y ∧ q y ≤ cap) ∧ ∑ y, q y = 1 ∧ CondensesFlatEvents C U q δ :=
    fun hU => hExact U (Finset.mem_powersetCard.mp hU).2
  choose ref href using hex
  let qU (U : Finset X) (y : Y) : ℝ := if h : U ∈ Ω then ref U h y else 0
  have hqU (U : Finset X) (hU : U ∈ Ω) :
      (∀ y, 0 ≤ qU U y ∧ qU U y ≤ cap) ∧ ∑ y, qU U y = 1 ∧
      CondensesFlatEvents C U (qU U) δ := by
    simp only [qU, dif_pos hU]
    exact href U hU
  let q (y : Y) := (∑ U ∈ Ω, qU U y) / M
  have hsumV (V : Finset Y) : ∑ y ∈ V, q y = (∑ U ∈ Ω, ∑ y ∈ V, qU U y) / M := by
    simp only [q, ← Finset.sum_div]
    rw [Finset.sum_comm]
  refine ⟨q, ?_, ?_, ?_⟩
  · intro y
    constructor
    · apply div_nonneg _ hM.le
      exact Finset.sum_nonneg (fun U hU => ((hqU U hU).1 y).1)
    · apply (div_le_iff₀ hM).mpr
      exact (Finset.sum_le_sum (fun U hU => ((hqU U hU).1 y).2)).trans_eq
        (by simp only [M, cap, D, Finset.sum_const, nsmul_eq_mul, mul_comm])
  · rw [hsumV, Finset.sum_congr rfl (fun U hU => (hqU U hU).2.1),
      Finset.sum_const, nsmul_eq_mul, mul_one]
    exact div_self hM.ne'
  · intro V
    let N (U : Finset X) : ℝ :=
      (((U ×ˢ (Finset.univ : Finset Seed)).filter fun p => C p.1 p.2 ∈ V).card : ℝ)
    have hin (U : Finset X) (hU : U ∈ Ω) :
        N U / (K * D) - ∑ y ∈ V, qU U y ≤ δ := by
      have h := (hqU U hU).2.2 V
      simpa [N, D, (Finset.mem_powersetCard.mp hU).2] using h
    have hAvg := Finset.sum_le_sum (fun U hU => hin U hU)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, nsmul_eq_mul] at hAvg
    have hAvg' := (div_le_iff₀ hM).mpr (hAvg.trans_eq (mul_comm M δ))
    rw [sub_div, ← hsumV, div_div] at hAvg'
    have hrel : ((S.card - 1).choose (K - 1) : ℝ) * S.card = M * K := by
      have hh := Nat.choose_mul (n := S.card) (k := K) (s := 1) hK
      simp only [Nat.choose_one_right] at hh
      dsimp [M]
      exact_mod_cast (show (S.card - 1).choose (K - 1) * S.card = Ω.card * K by
        rw [Finset.card_powersetCard, mul_comm _ S.card, ← hh])
    have hnum : (∑ U ∈ Ω, N U) / (K * D * M) = N S / (S.card * D) := by
      rw [avg_fiber_count C hK hS V]
      change ((S.card - 1).choose (K - 1) : ℝ) * N S / (K * D * M) = _
      field_simp
      linear_combination N S * hrel
    change N S / (S.card * D) - _ ≤ _
    exact hnum ▸ hAvg'

end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.GUV
open Polynomial

theorem symbols_le {c k : ℕ} (hc : 0 < c) : symbols c k ≤ k := by
  by_cases hk : k = 0
  · simp [symbols, hk, Nat.div_eq_of_lt (show c - 1 < c by omega)]
  unfold symbols
  apply (Nat.div_le_iff_le_mul_add_pred hc).mpr
  have h := Nat.mul_le_mul_right k (show 1 ≤ c by omega)
  simp only [one_mul] at h
  omega

theorem le_symbols_mul {c k : ℕ} (hc : 0 < c) : k ≤ c * symbols c k := by
  by_contra! h
  have hd := (Nat.div_le_iff_le_mul_add_pred hc).mp (show symbols c k ≤ symbols c k from le_rfl)
  change k+c-1 ≤ _ at hd
  omega

theorem halfSeed_exists (δ : ℝ) (hδ : 0 < δ) : ∃ a > 0, ∀ n, 1 ≤ n →
    let c := halfSeed a n
    1 < c ∧ n < 2 ^ c ∧ (n : ℝ)^2 ≤ δ * (2^c : ℕ) := by
  obtain ⟨C, hC⟩ := exists_nat_ge (1/δ)
  refine ⟨C+2, by omega, ?_⟩
  intro n hn c
  let d := n.size
  have hd : 0 < d := Nat.size_pos.mpr hn
  have hcn : c = (C+2)*d := halfSeed_of_pos hn
  have hc : C + 2 ≤ c := by
    rw [hcn]
    exact Nat.le_mul_of_pos_right _ hd
  have hc' : d ≤ c := by
    rw [hcn]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hn' : n < 2 ^ d := Nat.lt_size_self n
  refine ⟨by omega, hn'.trans_le (Nat.pow_le_pow_right (by decide) hc'), ?_⟩
  have he : C+2*d ≤ c := by
    rw [hcn, Nat.add_mul]
    have he := Nat.le_mul_of_pos_right C hd
    omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) he
  rw [pow_add, pow_mul] at hpow
  have hC' : 1 ≤ δ * C := by
    have hh := (div_le_iff₀ hδ).mp hC
    simpa [mul_comm] using hh
  have hCpow (M : ℕ) : M ≤ 2 ^ M := Nat.le_of_lt (Nat.lt_two_pow_self (n := M))
  have hCδ : 1 ≤ δ * (2 ^ C : ℕ) := hC'.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hCpow C) hδ.le)
  have hn2 : (n : ℝ)^2 ≤ (2 ^ d : ℕ)^2 := by exact_mod_cast Nat.pow_le_pow_left hn'.le 2
  calc
    _ ≤ ((2^d : ℕ) : ℝ)^2 := hn2
    _ ≤ (δ * (2 ^ C : ℕ)) * (2^d : ℕ)^2 := le_mul_of_one_le_left (by positivity) hCδ
    _ = δ * ((2^C * (2 ^ 2) ^ d : ℕ) : ℝ) := by
      have heq : (2 ^ d : ℕ)^2 = (2 ^ 2) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm d]
      simp only [← heq, Nat.cast_mul, Nat.cast_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hpow) hδ.le

theorem close_degree_estimate (δ : ℝ) (hδ : 0 < δ)
    {n k c : ℕ} (hc : 0 < c) (hk : k ≤ n)
    (hbig : (n : ℝ)^2 ≤ δ * (2^c : ℕ)) :
    (1-δ) * ((2^c : ℕ)^2 : ℝ) ≤ (((2^c : ℕ)^2 - symbols c k * (2^c-1) * (n-1) : ℕ) : ℝ) := by
  let h := 2^c
  let W := symbols c k * (h-1) * (n-1)
  have hM : symbols c k ≤ n := (symbols_le hc).trans hk
  have hW : W ≤ n^2*h := by
    change symbols c k * (h - 1) * (n - 1) ≤ _
    calc
      _ ≤ n * h * n := Nat.mul_le_mul (Nat.mul_le_mul hM (Nat.sub_le _ _)) (Nat.sub_le _ _)
      _ = _ := by ring
  have hWr : (W : ℝ) ≤ δ * (h : ℝ)^2 := by
    calc
      (W : ℝ) ≤ (n : ℝ)^2 * h := by exact_mod_cast hW
      _ ≤ δ * h * h := mul_le_mul_of_nonneg_right hbig (Nat.cast_nonneg _)
      _ = _ := by ring
  change _ ≤ ((h^2-W : ℕ) : ℝ)
  by_cases H : W ≤ h^2
  · rw [Nat.cast_sub H, Nat.cast_pow]
    try dsimp [h] at hs
    try push_cast at hs
    simp only [Nat.cast_pow] at hWr ⊢
    dsimp [h] at hWr ⊢
    push_cast at hWr ⊢
    linarith
  · have hs : (h:ℝ)^2 < (W : ℝ) := by exact_mod_cast lt_of_not_ge H
    rw [Nat.sub_eq_zero_of_le (lt_of_not_ge H).le, Nat.cast_zero]
    try dsimp [h] at hs
    try push_cast at hs
    simp only [Nat.cast_pow] at hWr ⊢
    dsimp [h] at hWr ⊢
    push_cast at hWr ⊢
    linarith

theorem vectorPoly_degree {K : Type} [Field K] {n : ℕ} (a : Fin n → K) :
    (vectorPoly a).natDegree ≤ n - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by have := j.isLt; omega)

theorem vectorPoly_injective {K : Type} [Field K] {n : ℕ} :
    Function.Injective (vectorPoly (K := K) (n := n)) := by
  classical
  intro a b h
  ext i
  have h' := congrArg (fun f : K[X] => f.coeff i.val) h
  simpa [vectorPoly, finsetSum_coeff, coeff_monomial, Fin.ext_iff.symm] using h'

open Classical in
theorem concrete_condenses
    {K F : Type} [Field K] [Field F] [CharP F 2] [Fintype K] [Fintype F]
    (φ : K →+* F) {c n k : ℕ} (hc : 1 < c) (hn : n < 2 ^ c) (hk : k ≤ n)
    (hK : Fintype.card K = 2 ^ c) (hF : Fintype.card F = (2 ^ c)^2)
    {ζ : K} (hζ : orderOf ζ = 2 ^ c-1)
    (δ : ℝ) (hδ : 0 < δ) (hbig : (n:ℝ)^2 ≤ δ * (2^c : ℕ))
    (input : Fin (2^n) ↪ (Fin n → K)) (seeds : Fin (2^(2*c)) ≃ F)
    (output : (F × (Fin (symbols c k) → F)) ↪ Fin (2^(2*(k+2*c)))) :
    ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
      ∃ q : Fin (2^(2*(k+2*c))) → ℝ,
        (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^(k+2*c)) ∧
        ∑ y, q y = 1 ∧
        CondensesFlatEvents (fun x y =>
          output (seeds y, fun i => (fold (φ ζ) i.val ((vectorPoly (input x)).map φ)).eval (seeds y)))
          S q δ := by
  let h := 2^c
  have hTwo : 2 < 2^c := by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hc
  let m := symbols c k
  let C (f : K[X]) (y : F) : F × (Fin m → F) :=
    (y, fun i => (fold (φ ζ) i.val (f.map φ)).eval y)
  let C' (x : Fin (2^n)) (y : Fin (2^(2*c))) := output (C (vectorPoly (input x)) (seeds y))
  have hd : 0 < Fintype.card (Fin (2^(2*c))) := by simp
  have hpow : 2^k ≤ (2^c)^m := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (le_symbols_mul (by omega))
  have hwidth : 2 ^ k * Fintype.card (Fin (2^(2*c))) ≤ Fintype.card (Fin (2^(2*(k+2*c)))) := by
    simp only [Fintype.card_fin, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hevents (S : Finset (Fin (2^n))) (hS : S.card = 2^k) :
      (1-δ) * ((S ×ˢ (Finset.univ : Finset (Fin (2^(2*c))))).card : ℝ) ≤
        (((S ×ˢ Finset.univ).image fun p => C' p.1 p.2).card : ℝ) := by
    let P := S.image (vectorPoly ∘ input)
    have hP : P.card = S.card :=
      Finset.card_image_of_injective _ (vectorPoly_injective.comp input.injective)
    let J := (P ×ˢ (Finset.univ : Finset F)).image (fun p => C p.1 p.2)
    have hJ : P.card * (Fintype.card F - m*(h-1)*(n-1)) ≤ J.card :=
      rs_image_card_ge φ hc hK hF hζ (show n-1 < 2^c-1 from by omega) P
        (by
          intro f hf
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf
          exact vectorPoly_degree (input x))
        (by rwa [hP, hS])
    have heq : J.image output = (S ×ˢ Finset.univ).image (fun p => C' p.1 p.2) := by
      ext z
      constructor
      · intro hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨⟨f,y⟩, hf, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_product.mp hf).1
        exact Finset.mem_image.mpr ⟨(x, seeds.symm y),
          Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, by simp [C']⟩
      · intro hz
        obtain ⟨⟨x,y⟩, huv, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr
          ⟨(vectorPoly (input x), seeds y), Finset.mem_product.mpr
            ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_product.mp huv).1,rfl⟩,
              Finset.mem_univ _⟩, rfl⟩, rfl⟩
    rw [← heq, Finset.card_image_of_injective _ output.injective]
    have hFseed : Fintype.card F = Fintype.card (Fin (2^(2*c))) := (Fintype.card_congr seeds).symm
    have hb := close_degree_estimate δ hδ (by omega) hk hbig
    rw [hP] at hJ
    calc
      _ = (S.card : ℝ) * ((1-δ) * (Fintype.card F : ℝ)) := by
        rw [hFseed, Finset.card_product, Finset.card_univ, Nat.cast_mul]; ring
      _ ≤ (S.card : ℝ) * (↑(Fintype.card F - m*(h-1)*(n-1)) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        rw [hF]
        exact_mod_cast hb
      _ ≤ _ := by exact_mod_cast hJ
  have h := condenses_of_exact C' (K := 2^k) (by positivity) hd δ (fun S hS => by
    have hpos : 0 < S.card * Fintype.card (Fin (2^(2*c))) := by rw [hS]; positivity
    simpa only [hS] using exact_condenses_of_image_card C' S δ hpos (hS.symm ▸ hwidth)
      (hevents S hS))
  intro S hS
  obtain ⟨q, hq, hqnorm, hqc⟩ := h S hS
  exact ⟨q, by simpa [Fintype.card_fin, pow_add] using hq, hqnorm, hqc⟩

end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.GUV

open Turing.MultiTapeTM Polynomial

theorem inputCode_injective {K : Type} {c n : ℕ} (hc : 0 < c) (basis : Fin (2^c) ≃ K) :
    Function.Injective (inputCode (n := n) basis hc) := by
  intro x y hxy
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hh := congrArg (fun a : Fin n → K => a ⟨i,hi⟩) hxy
    have he := congrArg Fin.val (basis.injective hh)
    change x.val / 2^i % 2 = y.val / 2^i % 2 at he
    simp only [Nat.testBit_eq_decide_div_mod_eq, he]
  · have hx := x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))
    have hy := y.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi))
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

theorem hasShortLosslessCondenser_of_foldedEvaluator
    (δ : ℝ) (hδ : 0 < δ)
    (heval : ∀ a (ha : 0 < a), ∃ cond, Nonempty (FoldedEvaluator a ha cond)) :
    HasShortLosslessCondenser δ := by
  classical
  obtain ⟨a, ha, hs⟩ := halfSeed_exists δ hδ
  obtain ⟨cond, ⟨I⟩⟩ := heval a ha
  refine ⟨2*a, cond, Nat.mul_pos (by decide) ha, I.native, ?_⟩
  intro n k hn hk
  let c := halfSeed a n
  change ∀ S : Finset (Fin (2^n)), 2^k ≤ S.card →
    ∃ q : Fin (2^(2*(k+(2*a)*n.size))) → ℝ, (∑ y, q y) = 1 ∧
      (∀ y, 0 ≤ q y ∧ q y ≤ 1/(2:ℝ)^(k+(2*a)*n.size)) ∧
      CondensesFlatEvents (fixedOutput cond n k ((2*a)*n.size) (2*(k+(2*a)*n.size))) S q δ
  rw [Nat.mul_assoc, ← halfSeed_of_pos hn]
  obtain ⟨hc, hnc, hbig⟩ := hs n hn
  let K := I.K n
  let F := I.F n
  let : Field K := I.fieldK n
  let : Field F := I.fieldF n
  let : CharP F 2 := I.charF n
  let : Fintype K := Fintype.ofEquiv _ (I.codeK n)
  let : Fintype F := Fintype.ofEquiv _ (I.codeF n)
  have hK : Fintype.card K = 2^c := by
    rw [Fintype.card_congr (I.codeK n).symm, Fintype.card_fin]
  have hF : Fintype.card F = (2^c)^2 := by
    rw [Fintype.card_congr (I.codeF n).symm, Fintype.card_fin, ← pow_mul, Nat.mul_comm]
  let L : Fin (2^n) ↪ (Fin n → K) :=
    ⟨inputCode (I.codeK n) (show 0 < c from by omega), inputCode_injective (show 0 < c from by omega) _⟩
  have H := concrete_condenses (I.embed n) hc hnc hk hK hF (I.primitive_order n hn)
    δ hδ hbig L (I.codeF n) (outputCode (k := k) (I.codeF n))
  intro S hS
  obtain ⟨q, hq, hsum, hcond⟩ := H S hS
  refine ⟨q, hsum, hq, ?_⟩
  have heq : fixedOutput cond n k (2*c) (2*(k+2*c)) = fun x y =>
      outputCode (k := k) (I.codeF n) (I.codeF n y, fun i =>
        (fold (I.embed n (I.primitive n)) i.val ((vectorPoly (L x)).map (I.embed n))).eval
          (I.codeF n y)) := by
    funext x y
    apply Fin.ext
    change cond (n,k,2*c,x.val,y.val) % 2 ^ (2*(k+2*c)) = _
    rw [I.correct n k hn hk]
    exact Nat.mod_eq_of_lt (Fin.isLt _)
  change CondensesFlatEvents (fixedOutput cond n k (2*c) (2*(k+2*c))) S q δ
  rw [heq]
  exact hcond

end TimeSpaceMA.GUV

namespace TimeSpaceMA.GUV

/-- The finite-field data required by the evaluator contract exist in every
positive binary width, independently of the evaluation algorithm. -/
theorem exists_field_codes (c : ℕ) (hc : 0 < c) :
    ∃ (K F : Type) (_ : Field K) (_ : Field F) (_ : CharP F 2)
      (_ : Fin (2 ^ c) ≃ K) (_ : Fin (2 ^ (2*c)) ≃ F)
      (_ : K →+* F) (ζ : K), orderOf ζ = 2^c - 1 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 c
  let F := FiniteField.Extension K 2 2
  let : Fintype K := Fintype.ofFinite K
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := CharP.of_ringHom_of_ne_zero (algebraMap K F) 2 (by decide)
  have hK : Nat.card K = 2^c := GaloisField.card 2 c hc.ne'
  have hF : Nat.card F = 2^(2*c) := by
    rw [FiniteField.natCard_extension, hK, ← pow_mul, Nat.mul_comm]
  let eK := (Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := K)).symm.trans hK)).symm
  let eF := (Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := F)).symm.trans hF)).symm
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have horder : orderOf (g : K) = 2^c - 1 := by
    rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  exact ⟨K,F,inferInstance,inferInstance,inferInstance,eK,eF,algebraMap K F,g,horder⟩

end TimeSpaceMA.GUV

open scoped BigOperators

namespace TimeSpaceMA.GUV

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Polynomial

namespace BinaryFieldArithmetic

variable {a : ℕ} {ha : 0 < a} (I : BinaryFieldArithmetic a ha)

attribute [local instance] BinaryFieldArithmetic.fieldK BinaryFieldArithmetic.fieldF
def radix (a n : ℕ) := 2^(2*halfSeed a n)

theorem radix_pos (a n : ℕ) : 0 < radix a n := by unfold radix; positivity

def clip (a n w : ℕ) : ℕ := w % radix a n

def word (a n w : ℕ) : FieldWord a n := ⟨clip a n w, Nat.mod_lt _ (radix_pos ..)⟩

def addWord (n u v : ℕ) : ℕ := clip a n (I.add (n,u,v))
def mulWord (n u v : ℕ) : ℕ := clip a n (I.mul (n,u,v))
def coeffWord (n : ℕ) (b : Bool) : ℕ := clip a n (I.coeff (n,b))
def zeroWord (n : ℕ) : ℕ := clip a n (I.zero n)
def generatorWord (n : ℕ) : ℕ := clip a n (I.generator n)

theorem clip_bound (a n u : ℕ) : clip a n u < radix a n :=
  Nat.mod_lt _ (radix_pos ..)

theorem clip_eq (a n u : ℕ) (hu : u < radix a n) : clip a n u = u :=
  Nat.mod_eq_of_lt hu

theorem size_le_of_lt {u a n : ℕ} (hu : u < radix a n) :
    u.size ≤ 2*halfSeed a n := Nat.size_le.mpr hu

theorem word_val (a n w : ℕ) (hw : w < radix a n) :
    (word a n w).val = w := clip_eq a n w hw

theorem code_apply_addWord (n : ℕ) (hn : 1 ≤ n) (u v : ℕ)
    (hu : u < radix a n) (hv : v < radix a n) :
    I.codeF n (word a n (I.addWord n u v)) =
      I.codeF n (word a n u) + I.codeF n (word a n v) := by
  have H := I.add_correct n hn (word a n u) (word a n v)
  rw [word_val _ _ _ hu, word_val _ _ _ hv] at H
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans H

theorem code_apply_mulWord (n : ℕ) (hn : 1 ≤ n) (u v : ℕ)
    (hu : u < radix a n) (hv : v < radix a n) :
    I.codeF n (word a n (I.mulWord n u v)) =
      I.codeF n (word a n u) * I.codeF n (word a n v) := by
  have H := I.mul_correct n hn (word a n u) (word a n v)
  rw [word_val _ _ _ hu, word_val _ _ _ hv] at H
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans H

theorem code_apply_coeffWord (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (j : Fin n) :
    I.codeF n (word a n (I.coeffWord n (x.val.testBit j.val))) =
      I.embed n (inputCode (I.codeK n) (halfSeed_pos ha n) x j) := by
  have H := I.coeff_correct n hn (x.val.testBit j.val)
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  rw [word_val _ _ _ (show I.coeffWord n (x.val.testBit j.val) < radix a n from clip_bound ..)]
  change I.coeff (n,x.val.testBit j.val) % 2^(2*halfSeed a n) = _
  rw [H]
  congr 4
  apply Fin.ext
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  have hl := Nat.mod_lt (x.val / 2^j.val) (by decide : 0 < 2)
  by_cases h : x.val / 2^j.val % 2 = 1
  · simp [h]
  · have h0 : x.val / 2^j.val % 2 = 0 := by omega
    simp [h0]

theorem code_apply_zeroWord (n : ℕ) (hn : 1 ≤ n) :
    I.codeF n (word a n (I.zeroWord n)) = 0 := by
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans (I.zero_correct n hn)

theorem code_apply_generatorWord (n : ℕ) (hn : 1 ≤ n) :
    I.codeF n (word a n (I.generatorWord n)) = I.embed n (I.primitive n) := by
  apply (I.codeF n).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  exact (word_val _ _ _ (clip_bound ..)).trans (I.generator_correct n hn)

theorem native_halfSeed {α : Type} {enc : α ↪ List Bool} (a : ℕ) {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => halfSeed a (n x)) enc encUnary := by
  let hb := (binary_le' (const 1) (unary_to_binary.comp hn))
  have hm : ComputableTidilyInPolyTime (fun x => max 1 (n x)) enc encUnary := by
    apply (hb.ite_decide hn (const 1)).of_enc_eq
    intro x
    by_cases h : 1 ≤ n x
    · simp [h, max_eq_right h]
    · simp [h, max_eq_left (by omega : n x ≤ 1)]
  exact unary_mul.comp ((const a).prod
    (ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hm)))

private theorem native_radix {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => radix a (n x)) enc encNat := by
  exact binary_two_pow.comp (unary_mul.comp ((const 2).prod (native_halfSeed a hn)))

private theorem native_clip {α : Type} {enc : α ↪ List Bool} {n w : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hw : ComputableTidilyInPolyTime w enc encNat) :
    ComputableTidilyInPolyTime (fun x => clip a (n x) (w x)) enc encNat :=
  binary_mod' hw (native_radix hn)

private theorem native_fieldBin {α : Type} {enc : α ↪ List Bool} {n u v : α → ℕ}
    {f : FieldBinInput → ℕ} (hf : ComputableInPolyTime f encFieldBinInput encNat)
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hu : ComputableTidilyInPolyTime u enc encNat)
    (hv : ComputableTidilyInPolyTime v enc encNat) :
    ComputableTidilyInPolyTime (fun x => clip a (n x) (f (n x,u x,v x))) enc encNat :=
  native_clip hn (hf.tidy.comp (hn.prod (hu.prod hv)))

abbrev HornerInput := ℕ × ℕ × ℕ
abbrev encHornerInput : HornerInput ↪ List Bool := encPair encUnary (encPair encNat encNat)
abbrev HornerState := ℕ × ℕ
abbrev encHornerState : HornerState ↪ List Bool := encPair encUnary encNat

def hornerStep (p : HornerInput) (s : HornerState) : HornerState :=
  let (n,x,y) := p
  let j := s.1-1
  (j, I.addWord n (I.coeffWord n (x.testBit j)) (I.mulWord n s.2 y))

def horner (n x y : ℕ) : ℕ :=
  ((I.hornerStep (n,x,y))^[n] (n, I.zeroWord n)).2

theorem horner_bound (n x y : ℕ) : I.horner n x y < radix a n := by
  generalize n = j at ⊢
  cases j with
  | zero => exact clip_bound ..
  | succ t =>
    unfold horner
    rw [Function.iterate_succ_apply']
    exact clip_bound ..

theorem horner_polytime : ComputableTidilyInPolyTime
    (fun p : HornerInput => I.horner p.1 p.2.1 p.2.2) encHornerInput encNat := by
  let np : ComputableTidilyInPolyTime (fun p : HornerInput => p.1) encHornerInput encUnary := fst _ _
  let init : ComputableTidilyInPolyTime (fun p : HornerInput => (p.1,I.zeroWord p.1))
      encHornerInput encHornerState := np.prod (native_clip np (I.zero_native.tidy.comp np))
  let joint := encPair encHornerInput encHornerState
  let pars := fst encHornerInput encHornerState
  let state := snd encHornerInput encHornerState
  let n := pars.fst'
  let x := pars.snd'.fst'
  let y := pars.snd'.snd'
  let j := unary_sub.comp (state.fst'.prod (const 1))
  let bit := binary_testBit x j
  have hstep : ComputableTidilyInPolyTime (fun p : HornerInput × HornerState =>
      I.hornerStep p.1 p.2) joint encHornerState :=
    j.prod (native_fieldBin I.add_native n
      (native_clip n (I.coeff_native.tidy.comp (n.prod bit)))
      (native_fieldBin I.mul_native n state.snd' y))
  let size : HornerInput → ℕ := fun p => 2*p.1 + 1 + 2*halfSeed a p.1
  have hsize : PolyBounded (fun p => (encHornerInput p).length) size := by
    have hs := np.polyBounded
    have hc := (native_halfSeed a np).polyBounded
    apply ((hs.add hs).add (.const 1)).add (hc.add hc) |>.mono
    intro p
    dsimp [size]
    omega
  have hstates (p : HornerInput) (j : ℕ) : j ≤ p.1 →
      (encHornerState ((I.hornerStep p)^[j] (p.1,I.zeroWord p.1))).length ≤ size p := by
    have ht (j : ℕ) : ((I.hornerStep p)^[j] (p.1,I.zeroWord p.1)).1 ≤ p.1 ∧
        ((I.hornerStep p)^[j] (p.1,I.zeroWord p.1)).2 < radix a p.1 := by
      induction j with
      | zero => exact ⟨le_rfl, clip_bound ..⟩
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact ⟨(Nat.sub_le _ _).trans ih.1, clip_bound ..⟩
    have hj := ht j
    have hd := size_le_of_lt hj.2
    intro _
    simp only [encHornerState, length_encPair, encUnary_apply, List.length_replicate,
      encNat_apply, Nat.size_eq_bits_len]
    dsimp [size]
    omega
  exact (snd encUnary encNat).comp (iterateWith id' np init hstep hsize hstates)

theorem horner_correct (n : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (y : FieldWord a n) :
    I.codeF n (word a n (I.horner n x.val y.val)) =
      ((vectorPoly (inputCode (I.codeK n) (halfSeed_pos ha n) x)).map
        (I.embed n)).eval (I.codeF n y) := by
  let B := I.codeF n y
  let γ (j : ℕ) := I.codeF n (word a n (I.coeffWord n (x.val.testBit j)))
  let H (i : ℕ) := ((I.hornerStep (n,x.val,y.val))^[i] (n,I.zeroWord n))
  have hy : y.val < radix a n := y.isLt
  have hwy : word a n y.val = y := Fin.ext (word_val _ _ _ hy)
  have hH (i : ℕ) (hi : i ≤ n) :
      (H i).1 = n-i ∧ (H i).2 < radix a n ∧
      I.codeF n (word a n (H i).2) =
        ∑ j ∈ Finset.range i, γ (n-i+j) * B^j := by
    induction i with
    | zero => simpa only [H, Function.iterate_zero_apply, Nat.sub_zero, Finset.range_zero,
        Finset.sum_empty, true_and] using
        (show I.zeroWord n < radix a n ∧ _ from ⟨clip_bound .., I.code_apply_zeroWord n hn⟩)
    | succ i ih =>
      obtain ⟨hcounter, hwidth, heval⟩ := ih (by omega)
      have hstep : H (i+1) = I.hornerStep (n,x.val,y.val) (H i) := by
        simp only [H, Function.iterate_succ_apply']
      have hj : (H i).1-1 = n-(i+1) := by rw [hcounter]; omega
      rw [hstep]
      refine ⟨hj, clip_bound .., ?_⟩
      change I.codeF n (word a n (I.addWord n (I.coeffWord n (x.val.testBit ((H i).1-1)))
          (I.mulWord n (H i).2 y.val))) = _
      have hc : I.coeffWord n (x.val.testBit ((H i).1-1)) < radix a n := clip_bound ..
      have hm : I.mulWord n (H i).2 y.val < radix a n := clip_bound ..
      rw [I.code_apply_addWord n hn _ _ hc hm,
        I.code_apply_mulWord n hn _ _ hwidth hy, hwy, heval, hj,
        Finset.sum_range_succ', Finset.sum_mul]
      change γ (n-(i+1)) + (∑ j ∈ Finset.range i, γ (n-i+j) * B^j * B) =
        (∑ j ∈ Finset.range i, γ (n-(i+1)+(j+1)) * B^(j+1)) + _ 
      rw [add_comm, pow_zero, mul_one, Nat.add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj'
      have hidx : n - i + j = n - (i+1) + (j+1) := by omega
      rw [hidx, pow_succ, mul_assoc]
  have h := (hH n le_rfl).2.2
  dsimp [horner, H] at h ⊢
  rw [h, Nat.sub_self]
  simp_rw [zero_add]
  rw [vectorPoly, Polynomial.map_sum, Polynomial.eval_finsetSum]
  simp only [Polynomial.map_monomial, Polynomial.eval_monomial, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (· * B^j.val) (I.code_apply_coeffWord n hn x j)

abbrev FoldInput := ℕ × ℕ × ℕ × ℕ
abbrev encFoldInput : FoldInput ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat encNat))

abbrev FoldState := ℕ × ℕ × ℕ
abbrev encFoldState : FoldState ↪ List Bool :=
  encPair encUnary (encPair encNat encNat)

def foldStep (p : FoldInput) (s : FoldState) : FoldState :=
  let (n,_,x,_) := p
  let (i,z,v) := s
  (i+1, I.mulWord n z (I.generatorWord n),
    v + I.horner n x z * (radix a n)^i)

def roll (p : FoldInput) : FoldState :=
  let (n,m,_,y) := p
  (I.foldStep p)^[m] (0,clip a n y,0)

theorem roll_bounds (p : FoldInput) (i : ℕ) :
    let r := (I.foldStep p)^[i] (0,clip a p.1 p.2.2.2,0)
    r.1 = i ∧ r.2.1 < radix a p.1 ∧ r.2.2 < (radix a p.1)^i := by
  induction i with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, true_and]; exact ⟨clip_bound .., by decide⟩
  | succ i ih =>
    simp only [Function.iterate_succ_apply']
    let r := (I.foldStep p)^[i] (0,clip a p.1 p.2.2.2,0)
    change r.1+1 = i+1 ∧ I.mulWord p.1 r.2.1 (I.generatorWord p.1) < radix a p.1 ∧
      r.2.2 + I.horner p.1 p.2.2.1 r.2.1 * (radix a p.1)^r.1 < (radix a p.1)^(i+1)
    refine ⟨by rw [ih.1], clip_bound .., ?_⟩
    rw [ih.1, pow_succ]
    have h₁ : r.2.2 < radix a p.1 ^ i := ih.2.2
    have h₂ := Nat.mul_le_mul_right ((radix a p.1)^i)
      (show I.horner p.1 p.2.2.1 r.2.1 + 1 ≤ radix a p.1 from I.horner_bound ..)
    rw [Nat.add_mul, Nat.one_mul, mul_comm (radix a p.1)] at h₂
    omega

private theorem native_fieldWidth {α : Type} {enc : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary) :
    ComputableTidilyInPolyTime (fun x => 2*halfSeed a (n x)) enc encUnary := by
  exact unary_mul.comp ((const 2).prod (native_halfSeed a hn))

private theorem native_radixPow {α : Type} {enc : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableTidilyInPolyTime n enc encUnary)
    (hi : ComputableTidilyInPolyTime i enc encUnary) :
    ComputableTidilyInPolyTime (fun x => (radix a (n x))^(i x)) enc encNat := by
  simp only [radix, ← pow_mul]
  exact binary_two_pow.comp (unary_mul.comp ((native_fieldWidth hn).prod hi))

theorem roll_polytime :
    ComputableTidilyInPolyTime I.roll encFoldInput encFoldState := by
  let np := fst encUnary (encPair encUnary (encPair encNat encNat))
  let mp := (snd encUnary (encPair encUnary (encPair encNat encNat))).fst'
  let yp := (snd encUnary (encPair encUnary (encPair encNat encNat))).snd'.snd'
  have hinit : ComputableTidilyInPolyTime (fun p : FoldInput => (0,clip a p.1 p.2.2.2,0))
      encFoldInput encFoldState := (const 0).prod ((native_clip np yp).prod (const 0))
  let par := fst encFoldInput encFoldState
  let st := snd encFoldInput encFoldState
  let n := par.fst'
  let x := par.snd'.snd'.fst'
  let j := st.fst'
  let z := st.snd'.fst'
  let v := st.snd'.snd'
  have hh := I.horner_polytime.comp (n.prod (x.prod z))
  have hstep : ComputableTidilyInPolyTime (fun p : FoldInput × FoldState => I.foldStep p.1 p.2)
      (encPair encFoldInput encFoldState) encFoldState :=
    (unary_add.comp (j.prod (const 1))).prod
      ((native_fieldBin I.mul_native n z (native_clip n (I.generator_native.tidy.comp n))).prod
        (binary_add' v (binary_mul' hh (native_radixPow n j))))
  let size : FoldInput → ℕ := fun p => 2*p.2.1 + 2 + 4*halfSeed a p.1 + 2*halfSeed a p.1*p.2.1
  have hpolyWidth := (native_fieldWidth (a := a) np).polyBounded
  have hsize : PolyBounded (fun p => (encFoldInput p).length) size := by
    apply ((mp.polyBounded.add mp.polyBounded).add (.const 2)).add
      ((hpolyWidth.add hpolyWidth).add (hpolyWidth.mul mp.polyBounded)) |>.mono
    intro p
    unfold size
    omega
  have hlen (p : FoldInput) (i : ℕ) (hi : i ≤ p.2.1) :
      (encFoldState ((I.foldStep p)^[i] (0,clip a p.1 p.2.2.2,0))).length ≤ size p := by
    have ⟨hj, hz, hv⟩ := I.roll_bounds p i
    have hzs := size_le_of_lt hz
    have hv' : ((I.foldStep p)^[i] (0,clip a p.1 p.2.2.2,0)).2.2.size ≤ 2*halfSeed a p.1*i := by
      apply Nat.size_le.mpr
      rw [pow_mul]
      exact hv
    have he := Nat.mul_le_mul_left (2*halfSeed a p.1) hi
    simp only [encFoldState, length_encPair, encUnary_apply, List.length_replicate,
      encNat_apply, Nat.size_eq_bits_len]
    dsimp [size]
    omega
  exact iterateWith id' mp hinit hstep hsize hlen

def packed (p : FoldInput) : ℕ :=
  let (n,m,_,y) := p
  (I.roll p).2.2 + clip a n y * (radix a n)^m

theorem packed_polytime :
    ComputableTidilyInPolyTime I.packed encFoldInput encNat := by
  let np := fst encUnary (encPair encUnary (encPair encNat encNat))
  let mp := (snd encUnary (encPair encUnary (encPair encNat encNat))).fst'
  let yp := (snd encUnary (encPair encUnary (encPair encNat encNat))).snd'.snd'
  exact binary_add' I.roll_polytime.snd'.snd'
    (binary_mul' (native_clip np yp) (native_radixPow np mp))

theorem packed_correct (n k : ℕ) (hn : 1 ≤ n) (x : Fin (2^n)) (y : FieldWord a n) :
    I.packed (n,symbols (halfSeed a n) k,x.val,y.val) =
      (outputCode (k := k) (I.codeF n) (I.codeF n y, fun i =>
        (fold (I.embed n (I.primitive n)) i.val
          ((vectorPoly (inputCode (I.codeK n) (halfSeed_pos ha n) x)).map
            (I.embed n))).eval (I.codeF n y))).val := by
  classical
  let m := symbols (halfSeed a n) k
  let p : FoldInput := (n,m,x.val,y.val)
  let R := radix a n
  let f := (vectorPoly (inputCode (I.codeK n) (halfSeed_pos ha n) x)).map
    (I.embed n)
  let B := I.codeF n y
  let ζ := I.embed n (I.primitive n)
  let r (i : ℕ) := (I.foldStep p)^[i] (0,clip a n y.val,0)
  let v (i : ℕ) := ((I.codeF n).symm ((fold ζ i f).eval B)).val
  have hy : y.val < R := y.isLt
  have hw (i : ℕ) : (r i).2.1 < R := (I.roll_bounds p i).2.1
  have counter (i : ℕ) : (r i).1 = i := (I.roll_bounds p i).1
  have hyclip : clip a n y.val = y.val := clip_eq _ _ _ hy
  have hdecode (i : ℕ) : I.codeF n (word a n (r i).2.1) = ζ^i * B := by
    induction i with
    | zero =>
      have heq : word a n (r 0).2.1 = y := by
        apply Fin.ext
        rw [word_val _ _ _ (hw 0)]
        simpa [r] using hyclip
      rw [heq, pow_zero, one_mul]
    | succ i ih =>
      have hg : I.generatorWord n < R := clip_bound ..
      have heq : (r (i+1)).2.1 = I.mulWord n (r i).2.1 (I.generatorWord n) := by
        simp only [r, Function.iterate_succ_apply', foldStep, p]
      rw [heq, I.code_apply_mulWord n hn _ _ (hw i) hg, ih,
        I.code_apply_generatorWord n hn, pow_succ]
      ac_rfl
  have hval (i : ℕ) : I.horner n x.val (r i).2.1 = v i := by
    have hword := word_val _ _ _ (hw i)
    have hh := I.horner_correct n hn x (word a n (r i).2.1)
    rw [hword, hdecode] at hh
    have hh' := congrArg (fun u => ((I.codeF n).symm u).val) hh
    simp only [Equiv.symm_apply_apply, word_val _ _ _ (I.horner_bound ..)] at hh'
    unfold v fold
    rw [eval_comp, eval_mul, eval_C, eval_X]
    exact hh'
  have hprefix (i : ℕ) : (r i).2.2 = ∑ j ∈ Finset.range i, v j * R^j := by
    induction i with
    | zero => simp [r]
    | succ i ih =>
      have heq : (r (i+1)).2.2 = (r i).2.2 + I.horner n x.val (r i).2.1 * R^(r i).1 := by
        simp only [r, Function.iterate_succ_apply', foldStep, p, R]
      rw [heq, ih, hval, counter, Finset.sum_range_succ]
  change (r m).2.2 + clip a n y.val * R^m = _
  rw [hprefix, hyclip]
  change (∑ j ∈ Finset.range m, v j * R^j) + y.val * R^m =
    (∑ j : Fin m, v j.val * R^j.val) + R^m * ((I.codeF n).symm (I.codeF n y)).val
  rw [Equiv.symm_apply_apply]
  change (∑ j ∈ Finset.range m, v j * R^j) + y.val * R^m =
    (∑ j : Fin m, v j.val * R^j.val) + R^m * y.val
  rw [Fin.sum_univ_eq_sum_range (fun j => v j * R^j), mul_comm (R^m)]

def eval (input : ExtractorInput) : ℕ :=
  let (n,k,_,x,y) := input
  I.packed (n,symbols (halfSeed a n) (min n k),x,y)

theorem eval_polytime : ComputableInPolyTime I.eval encExtractorInput encNat := by
  let hn := fst encUnary (encPair encNat (encPair encUnary (encPair encNat encNat)))
  let htail := snd encUnary (encPair encNat (encPair encUnary (encPair encNat encNat)))
  let hk := (ComputableInPolyTime.binary_min_unary' hn.computableInPolyTime
    htail.fst'.computableInPolyTime).tidy
  let hraw := htail.snd'.snd'
  let hC := native_halfSeed a hn
  let htop := unary_sub.comp ((unary_add.comp (hk.prod hC)).prod (const 1))
  have hm : ComputableTidilyInPolyTime (fun p : ExtractorInput =>
      symbols (halfSeed a p.1) (min p.1 p.2.1)) encExtractorInput encUnary := by
    apply binary_to_unary_bounded
      (binary_div' (unary_to_binary.comp htop) (unary_to_binary.comp hC)) hn
    intro p
    exact (symbols_le (halfSeed_pos ha p.1)).trans (Nat.min_le_left _ _)
  exact (I.packed_polytime.comp (hn.prod (hm.prod hraw))).computableInPolyTime

noncomputable def foldedEvaluator : FoldedEvaluator a ha I.eval where
  native := I.eval_polytime
  K := I.K
  F := I.F
  fieldK := I.fieldK
  fieldF := I.fieldF
  charF := I.charF
  codeK := I.codeK
  codeF := I.codeF
  embed := I.embed
  primitive := I.primitive
  primitive_order := I.primitive_order
  correct := by
    intro n k hn hk x y
    simp only [eval, min_eq_right hk]
    exact I.packed_correct n k hn x y

end BinaryFieldArithmetic

theorem hasShortLosslessCondenser_of_binaryFieldArithmetic
    (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ a (ha : 0 < a), Nonempty (BinaryFieldArithmetic a ha)) :
    HasShortLosslessCondenser δ :=
  hasShortLosslessCondenser_of_foldedEvaluator δ hδ (fun a ha => by
    obtain ⟨I⟩ := h a ha
    exact ⟨_, ⟨I.foldedEvaluator⟩⟩)

end TimeSpaceMA.GUV
open TimeSpaceMA TimeSpaceMA.GUV

theorem solution (δ : ℝ) (hδ : 0 < δ) (_hδ' : δ ≤ 1/8) :
    HasShortLosslessCondenser δ :=
  hasShortLosslessCondenser_of_binaryFieldArithmetic δ hδ fieldOperations_exists

