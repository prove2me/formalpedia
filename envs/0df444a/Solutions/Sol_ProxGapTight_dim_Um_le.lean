-- Prove2me | solution 1 for ProxGapTight.dim_Um_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:48:58.527083+00:00
-- url     : https://prove2.me/submissions/39200ed7-a75d-45b9-bfff-eb735e352ba3

import Mathlib
import Definitions.Def_ProxGapTight_Um

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace ProxGapTight.Dev.DimUm

open Module MvPolynomial

/-- Dimension of low-degree polynomials. -/
lemma finrank_restrictTotalDegree_le (R : Type) [Field R] (n D : ℕ) :
    finrank R (restrictTotalDegree (Fin n) R D) ≤ Nat.choose (n + D) D := by
  classical
  let M : Set (Fin n →₀ ℕ) := {s | (s.sum fun _ e => e) ≤ D}
  have h1 : finrank R (restrictTotalDegree (Fin n) R D) = Nat.card M :=
    finrank_eq_nat_card_basis (basisRestrictSupport R M)
  rw [h1]
  let φ : M → {P : Option (Fin n) →₀ ℕ // P.sum (fun _ => id) = D} := fun f =>
    ⟨Finsupp.mapDomain some f.1 + Finsupp.single none (D - (f.1.sum fun _ e => e)), by
      have hf : (f.1.sum fun _ e => e) ≤ D := f.2
      rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_mapDomain_index
        (by simp) (by intros; rfl), Finsupp.sum_single_index (by simp)]
      simp only [id]
      omega⟩
  have hφ : Function.Injective φ := by
    intro f g h
    have h' := congrArg Subtype.val h
    apply Subtype.ext
    ext i
    have := congrArg (fun P => P (some i)) h'
    simp only [φ, Finsupp.add_apply, Finsupp.mapDomain_apply (Option.some_injective _),
      Finsupp.single_apply] at this
    simpa using this
  haveI : Finite {P : Option (Fin n) →₀ ℕ // P.sum (fun _ => id) = D} :=
    Finite.of_equiv _ (Sym.equivNatSum (Option (Fin n)) D)
  calc Nat.card M ≤ Nat.card {P : Option (Fin n) →₀ ℕ // P.sum (fun _ => id) = D} :=
        Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (Sym (Option (Fin n)) D) :=
        (Nat.card_congr (Sym.equivNatSum (Option (Fin n)) D)).symm
    _ = Nat.choose (n + D) D := by
        rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose]
        simp

/-- Indicator of the kernel of a linear map to `Fp^c` is a polynomial of degree `≤ c (p-1)`. -/
lemma indicator_poly (p : ℕ) [Fact p.Prime] (n c : ℕ)
    (π : (Fin n → ZMod p) →ₗ[ZMod p] (Fin c → ZMod p)) :
    ∃ f : MvPolynomial (Fin n) (ZMod p), f.totalDegree ≤ c * (p - 1) ∧
      ∀ x : Fin n → ZMod p, MvPolynomial.eval x f = if π x = 0 then 1 else 0 := by
  classical
  have hp1 : 1 ≤ p - 1 := by
    have := (Fact.out : p.Prime).two_le
    omega
  let L : Fin c → MvPolynomial (Fin n) (ZMod p) := fun j =>
    ∑ i : Fin n, C (π (fun l => if i = l then 1 else 0) j) * X i
  have hL : ∀ j x, MvPolynomial.eval x (L j) = π x j := by
    intro j x
    simp only [L, map_sum, map_mul, eval_C, eval_X]
    conv_rhs => rw [LinearMap.pi_apply_eq_sum_univ π x]
    simp [Finset.sum_apply, mul_comm]
  have hLd : ∀ j, (L j).totalDegree ≤ 1 := by
    intro j
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_C, totalDegree_X]
  refine ⟨∏ j : Fin c, (1 - L j ^ (p - 1)), ?_, ?_⟩
  · refine (totalDegree_finsetProd _ _).trans ?_
    have : ∀ j ∈ (Finset.univ : Finset (Fin c)),
        (1 - L j ^ (p - 1)).totalDegree ≤ p - 1 := by
      intro j _
      refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
      refine (totalDegree_pow _ _).trans ?_
      calc (p - 1) * (L j).totalDegree ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ (hLd j)
        _ = p - 1 := mul_one _
    refine (Finset.sum_le_sum this).trans ?_
    simp
  · intro x
    simp only [map_prod, map_sub, map_one, map_pow, hL]
    split_ifs with h
    · refine Finset.prod_eq_one fun j _ => ?_
      have : π x j = 0 := by rw [h]; rfl
      rw [this, zero_pow (by omega)]
      simp
    · obtain ⟨j, hj⟩ : ∃ j, π x j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact h (funext hcon)
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [ZMod.pow_card_sub_one_eq_one hj]
      simp

open scoped Classical in
lemma subspace_poly (p : ℕ) [Fact p.Prime] (n c : ℕ)
    (W : Submodule (ZMod p) (Fin n → ZMod p)) (hW : finrank (ZMod p) W + c = n) :
    ∃ f : MvPolynomial (Fin n) (ZMod p), f.totalDegree ≤ c * (p - 1) ∧
      ∀ x : Fin n → ZMod p, MvPolynomial.eval x f = if x ∈ W then 1 else 0 := by
  have hq : finrank (ZMod p) ((Fin n → ZMod p) ⧸ W) = c := by
    have := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fin_fun] at this
    omega
  let e : ((Fin n → ZMod p) ⧸ W) ≃ₗ[ZMod p] (Fin c → ZMod p) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hq)
  obtain ⟨f, hf1, hf2⟩ := indicator_poly p n c (e.toLinearMap.comp W.mkQ)
  refine ⟨f, hf1, fun x => ?_⟩
  rw [hf2]
  have : ((e.toLinearMap.comp W.mkQ) x = 0) ↔ x ∈ W := by
    simp [Submodule.Quotient.mk_eq_zero]
  simp only [this]

lemma line_rep (K : Type) [Field K] (m : ℕ) (ℓ : ProxGapTight.Lines K m) :
    ∃ r : Fin m → K, ∀ W : Submodule K (Fin m → K), ℓ.1 ≤ W ↔ r ∈ W := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp ℓ.2
  refine ⟨v.1, fun W => ⟨fun h => h v.2, fun h y hy => ?_⟩⟩
  obtain ⟨c, hc⟩ := hv ⟨y, hy⟩
  have : c • v.1 = y := congrArg Subtype.val hc
  rw [← this]
  exact W.smul_mem c h

end ProxGapTight.Dev.DimUm

namespace ProxGapTight

open ProxGapTight.Dev.DimUm Module MvPolynomial in
theorem chk_dim_Um_le (p a m : ℕ) [Fact p.Prime] (K : Type) [Field K] [Fintype K]
    (hK : Fintype.card K = p ^ a) :
    Module.finrank (ZMod p) (Um K m p) ≤
      Nat.choose (a * m + 2 * a * (p - 1)) (2 * a * (p - 1)) := by
  classical
  haveI : CharP K p := charP_of_card_eq_prime_pow hK
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  have ha : finrank (ZMod p) K = a := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rw [hK, ZMod.card] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  let E : (Fin m → K) ≃ₗ[ZMod p] (Fin (a * m) → ZMod p) :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp [Module.finrank_pi_fintype, ha, mul_comm])
  choose r hr using line_rep K m
  have hW : ∀ W : Codim2 K m, ∃ f : MvPolynomial (Fin (a * m)) (ZMod p),
      f.totalDegree ≤ 2 * a * (p - 1) ∧
      ∀ ℓ : Lines K m, MvPolynomial.eval (E (r ℓ)) f = incVec (ZMod p) W ℓ := by
    intro W
    let W' : Submodule (ZMod p) (Fin (a * m) → ZMod p) :=
      (W.1.restrictScalars (ZMod p)).map (E : (Fin m → K) →ₗ[ZMod p] _)
    have hfr : finrank (ZMod p) W' + 2 * a = a * m := by
      have h1 : finrank (ZMod p) W' = finrank (ZMod p) (W.1.restrictScalars (ZMod p)) :=
        LinearEquiv.finrank_map_eq E _
      have h2 : finrank (ZMod p) (W.1.restrictScalars (ZMod p)) = a * finrank K W.1 := by
        rw [← ha]
        exact (Module.finrank_mul_finrank (ZMod p) K W.1).symm
      have h3 := W.2
      rw [h1, h2]
      have h4 : a * m = a * (finrank K W.1 + 2) := by rw [h3]
      rw [h4]
      ring
    obtain ⟨f, hf1, hf2⟩ := subspace_poly p (a * m) (2 * a) W' hfr
    refine ⟨f, hf1, fun ℓ => ?_⟩
    rw [hf2]
    have : E (r ℓ) ∈ W' ↔ ℓ.1 ≤ W.1 := by
      rw [hr ℓ W.1]
      constructor
      · rintro ⟨y, hy, hyE⟩
        have : y = r ℓ := E.injective hyE
        subst this
        exact hy
      · intro h
        exact ⟨r ℓ, h, rfl⟩
    unfold incVec
    simp only [this]
  choose f hf1 hf2 using hW
  let Φ : restrictTotalDegree (Fin (a * m)) (ZMod p) (2 * a * (p - 1)) →ₗ[ZMod p]
      (Lines K m → ZMod p) :=
    (LinearMap.pi fun ℓ => (aeval (E (r ℓ))).toLinearMap).comp
      (restrictTotalDegree (Fin (a * m)) (ZMod p) (2 * a * (p - 1))).subtype
  have hle : Um K m p ≤ LinearMap.range Φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨W, rfl⟩
    refine ⟨⟨f W, (mem_restrictTotalDegree _ _ _).mpr (hf1 W)⟩, ?_⟩
    funext ℓ
    have := hf2 W ℓ
    simpa [Φ, aeval_def, eval₂_id] using this
  calc finrank (ZMod p) (Um K m p) ≤ finrank (ZMod p) (LinearMap.range Φ) :=
        Submodule.finrank_mono hle
    _ ≤ finrank (ZMod p) (restrictTotalDegree (Fin (a * m)) (ZMod p) (2 * a * (p - 1))) :=
        LinearMap.finrank_range_le Φ
    _ ≤ _ := finrank_restrictTotalDegree_le _ _ _

end ProxGapTight
end

theorem solution : type_of% @ProxGapTight.chk_dim_Um_le := @ProxGapTight.chk_dim_Um_le
