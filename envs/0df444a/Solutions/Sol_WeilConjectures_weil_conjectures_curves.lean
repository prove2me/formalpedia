-- Prove2me | solution 1 for WeilConjectures.weil_conjectures_curves
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-19T22:50:03.209648+00:00
-- url     : https://prove2.me/submissions/c2fed667-e86d-4d2d-9848-b4bbbd283351

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction
import Theorems.Thm_AlgebraicCurve_Place_finite_setOf_deg_eq
import Theorems.Thm_AlgebraicCurve_card_effectiveDivisors_mul_eq_sum
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_apply_algebraMap_eq_pow_card
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_exists_LPolynomial_of_finite
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral

/-!
# Solution de `WeilConjectures.weil_conjectures_curves` (fichier autonome)

FICHIER ENGENDRÉ par `scripts/assemble_solution.py weil_conjectures_curves` à partir de la bibliothèque `Bridge` :
ne pas modifier à la main.

Il n'importe que Mathlib et des nœuds de la plateforme (définitions, et théorèmes PROVED du
projet FLT) ; les lemmes intermédiaires sont recopiés depuis `Bridge/` (espace de noms
`WeilConjectures.Bridge`).
-/

/-! ## Recopié de `Bridge/Zeta.lean` -/

/-!
# Calcul de la fonction zêta de la plateforme (partie A2 du pont)

La plateforme définit `zetaOfCounts N = exp(∑_{m ≥ 1} N m · T^m / m)` par
`PowerSeries.subst` dans `PowerSeries.exp ℚ`. On la caractérise ici par une équation
différentielle :

`Z(0) = 1` et `Z' = (∑_{m ≥ 0} N (m + 1) · T^m) · Z`,

ce qui donne sans logarithme formel les règles de calcul utiles : produit pour une somme de
comptages, et inverse de `1 - aT` pour le comptage géométrique `m ↦ a^m`.

Les indices suivent la plateforme : `N m` est le nombre de points en degré `m`, et `N 0` est
ignoré. Dans `finite_fields` (`Zeta/CountingSeries.lean`, `ZetaCalculus.lean`), l'indice `n`
désigne le degré `n + 1` ; `countingSeries N` ci-dessous y correspond à
`countingSeries (N ∘ Nat.succ)`.
-/

noncomputable section

open PowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R] [IsAddTorsionFree R]

/-- Unicité pour l'équation différentielle linéaire `f' = f · a` : deux solutions de même terme
constant coïncident. (Porté de `finite_fields`, `Algebra/PowerSeries/LinearODE.lean`.) -/
theorem eq_of_derivative_eq_mul {f g a : R⟦X⟧}
    (hf : derivative R f = f * a) (hg : derivative R g = g * a)
    (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using h0
    | succ n =>
      have e1 := congrArg (coeff n) hf
      have e2 := congrArg (coeff n) hg
      rw [coeff_derivative, coeff_mul] at e1 e2
      have equ : coeff (n + 1) f * (n + 1) = coeff (n + 1) g * (n + 1) := by
        rw [e1, e2]
        refine Finset.sum_congr rfl ?_
        rintro ⟨i, j⟩ hij
        have hsum : i + j = n := by simpa using hij
        rw [ih i (by omega)]
      rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul] at equ
      exact (smul_right_inj (Nat.succ_ne_zero n)).mp equ

end PowerSeries

namespace WeilConjectures.Bridge

/-- La série génératrice des comptages : `∑_{m ≥ 0} N (m + 1) · T^m`, dérivée logarithmique
attendue de la fonction zêta. -/
def countingSeries (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ (N (m + 1) : ℚ)

@[simp]
theorem coeff_countingSeries (N : ℕ → ℕ) (m : ℕ) :
    coeff m (countingSeries N) = (N (m + 1) : ℚ) := by
  simp [countingSeries]

theorem countingSeries_add (N₁ N₂ : ℕ → ℕ) :
    countingSeries (N₁ + N₂) = countingSeries N₁ + countingSeries N₂ := by
  ext m
  simp

/-- Caractérisation différentielle de la série zêta associée au comptage `N`. -/
def IsZetaSeries (N : ℕ → ℕ) (Z : ℚ⟦X⟧) : Prop :=
  constantCoeff Z = 1 ∧ d⁄dX ℚ Z = countingSeries N * Z

/-- Le terme constant et l'équation différentielle déterminent la série zêta. -/
theorem IsZetaSeries.unique {N : ℕ → ℕ} {Z W : ℚ⟦X⟧}
    (hZ : IsZetaSeries N Z) (hW : IsZetaSeries N W) : Z = W :=
  PowerSeries.eq_of_derivative_eq_mul
    (by rw [hZ.2, mul_comm]) (by rw [hW.2, mul_comm]) (hZ.1.trans hW.1.symm)

/-- Le « logarithme » `∑_{m ≥ 1} N m · T^m / m` substitué dans `exp` par la plateforme. -/
def zetaLog (N : ℕ → ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ if m = 0 then (0 : ℚ) else (N m : ℚ) / (m : ℚ)

theorem zetaOfCounts_eq (N : ℕ → ℕ) :
    zetaOfCounts N = (PowerSeries.exp ℚ).subst (zetaLog N) := rfl

@[simp]
theorem constantCoeff_zetaLog (N : ℕ → ℕ) : constantCoeff (zetaLog N) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, zetaLog, coeff_mk]
  simp

theorem hasSubst_zetaLog (N : ℕ → ℕ) : HasSubst (zetaLog N) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_zetaLog N)

theorem derivative_zetaLog (N : ℕ → ℕ) : d⁄dX ℚ (zetaLog N) = countingSeries N := by
  ext m
  rw [coeff_derivative, zetaLog, coeff_mk, coeff_countingSeries]
  have hne : (m : ℚ) + 1 ≠ 0 := by positivity
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
  push_cast
  field_simp

theorem constantCoeff_zetaOfCounts (N : ℕ → ℕ) : constantCoeff (zetaOfCounts N) = 1 := by
  rw [zetaOfCounts_eq, ← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' (hasSubst_zetaLog N), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [he, constantCoeff_zetaLog]

theorem derivative_zetaOfCounts (N : ℕ → ℕ) :
    d⁄dX ℚ (zetaOfCounts N) = countingSeries N * zetaOfCounts N := by
  rw [zetaOfCounts_eq, derivative_subst (hasSubst_zetaLog N), derivative_exp,
    derivative_zetaLog, mul_comm]

/-- **La série zêta de la plateforme vérifie l'équation différentielle.** -/
theorem zetaOfCounts_isZetaSeries (N : ℕ → ℕ) : IsZetaSeries N (zetaOfCounts N) :=
  ⟨constantCoeff_zetaOfCounts N, derivative_zetaOfCounts N⟩

/-- Toute solution de l'équation différentielle est la série zêta de la plateforme. -/
theorem IsZetaSeries.eq_zetaOfCounts {N : ℕ → ℕ} {Z : ℚ⟦X⟧} (hZ : IsZetaSeries N Z) :
    Z = zetaOfCounts N :=
  hZ.unique (zetaOfCounts_isZetaSeries N)

/-- La valeur `N 0` est ignorée : seuls les comptages en degré `m ≥ 1` comptent. -/
theorem zetaOfCounts_congr {N N' : ℕ → ℕ} (h : ∀ m, 1 ≤ m → N m = N' m) :
    zetaOfCounts N = zetaOfCounts N' := by
  have hc : countingSeries N = countingSeries N' := by
    ext m
    simp [h (m + 1) (Nat.succ_pos m)]
  refine (zetaOfCounts_isZetaSeries N).unique ⟨constantCoeff_zetaOfCounts N', ?_⟩
  rw [hc]
  exact derivative_zetaOfCounts N'

/-- **Somme de comptages, produit de séries zêta.** -/
theorem zetaOfCounts_add (N₁ N₂ : ℕ → ℕ) :
    zetaOfCounts (N₁ + N₂) = zetaOfCounts N₁ * zetaOfCounts N₂ := by
  refine (zetaOfCounts_isZetaSeries _).unique ⟨?_, ?_⟩
  · rw [map_mul, constantCoeff_zetaOfCounts, constantCoeff_zetaOfCounts, one_mul]
  · rw [(derivative ℚ).leibniz, smul_eq_mul, smul_eq_mul,
      derivative_zetaOfCounts, derivative_zetaOfCounts, countingSeries_add]
    ring

theorem zetaOfCounts_zero : zetaOfCounts 0 = 1 := by
  refine ((zetaOfCounts_isZetaSeries 0).unique ⟨map_one _, ?_⟩)
  have h0 : countingSeries 0 = 0 := by
    ext m
    simp
  rw [h0, zero_mul]
  exact Derivation.map_one_eq_zero _

/-- **Version finie : comptage somme, série zêta produit.** -/
theorem zetaOfCounts_sum {ι : Type*} (s : Finset ι) (N : ι → ℕ → ℕ) :
    zetaOfCounts (∑ i ∈ s, N i) = ∏ i ∈ s, zetaOfCounts (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zetaOfCounts_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, zetaOfCounts_add, Finset.prod_insert hi, ih]

/-- La série géométrique `∑ a^m T^m`. -/
def geometricSeries (a : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun m ↦ a ^ m

theorem geometricSeries_isZetaSeries (a : ℕ) :
    IsZetaSeries (fun m ↦ a ^ m) (geometricSeries (a : ℚ)) := by
  constructor
  · rw [← coeff_zero_eq_constantCoeff_apply]
    simp [geometricSeries]
  · ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [geometricSeries, coeff_mk, coeff_countingSeries, Nat.cast_pow]
    calc
      (a : ℚ) ^ (n + 1) * (n + 1) = ∑ _k ∈ Finset.range n.succ, (a : ℚ) ^ (n + 1) := by
        simp [nsmul_eq_mul, mul_comm]
      _ = ∑ k ∈ Finset.range n.succ, (a : ℚ) ^ (k + 1) * (a : ℚ) ^ (n - k) := by
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [← pow_add]
        have hk' : k < n.succ := Finset.mem_range.mp hk
        congr 1
        omega

theorem geometricSeries_mul_one_sub (a : ℚ) :
    geometricSeries a * (1 - C a * X) = 1 := by
  have h : geometricSeries a = rescale a (PowerSeries.mk 1 : ℚ⟦X⟧) := by
    ext n
    simp [geometricSeries]
  rw [h, ← rescale_X]
  have hsub : (1 : ℚ⟦X⟧) - rescale a X = rescale a (1 - X) := by
    rw [map_sub, map_one]
  rw [hsub, ← map_mul, mk_one_mul_one_sub_eq_one, map_one]

/-- **Comptage géométrique : `exp(∑ a^m T^m / m) · (1 - aT) = 1`.** -/
theorem zetaOfCounts_pow_mul (a : ℕ) :
    zetaOfCounts (fun m ↦ a ^ m) * (1 - C (a : ℚ) * X) = 1 := by
  rw [← (geometricSeries_isZetaSeries a).eq_zetaOfCounts, geometricSeries_mul_one_sub]

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/Points.lean` -/

/-!
# Comptage de points de la plateforme (partie A1 du pont)

Dépliage de `pointCount` : en degré `m ≥ 1`, c'est le nombre de `k`-morphismes
`Spec 𝔽_{q^m} ⟶ X`, avec `𝔽_{q^m} = FiniteField.Extension k p m` ; en degré `0`, c'est `0`.

Dans `finite_fields`, `pointCount X π n` compte les points sur `Extension k p n`, qui y désigne
`FiniteField.Extension k p (n + 1)` : il correspond à `pointCount p f (n + 1)` ci-dessous
(`pointCount_succ`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k] [CharP k p]
  {X : Scheme} (f : X ⟶ Spec (.of k))

@[simp]
theorem pointCount_zero : pointCount p f 0 = 0 := by
  simp [pointCount]

/-- En degré `m ≠ 0`, `pointCount` compte les points sur l'extension de degré `m`. -/
theorem pointCount_of_neZero (m : ℕ) [NeZero m] :
    pointCount p f m = pointsOver f (FiniteField.Extension k p m) := by
  rw [pointCount, dif_neg (NeZero.ne m)]

/-- Version indexée comme dans `finite_fields` (degré `n + 1`). -/
theorem pointCount_succ (n : ℕ) :
    pointCount p f (n + 1) = pointsOver f (FiniteField.Extension k p (n + 1)) :=
  pointCount_of_neZero p f (n + 1)

theorem zetaFunction_eq : zetaFunction p f = zetaOfCounts (pointCount p f) := rfl

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/ZetaField.lean` -/

section

/-!
# Dérivée logarithmique d'un produit `∏ (1 - aT)` (partie H1)

Sur un corps `K` quelconque, la dérivée logarithmique de `∏_{a ∈ s} (1 - aT)` est
`-∑_m (∑_{a ∈ s} a^{m+1}) T^m`. Si une série `Z` vérifie `Z' = c Z` et
`Z · ∏_{b ∈ β} (1 - bT) = ∏_{a ∈ α} (1 - aT)`, alors `c = S_β - S_α`. Appliqué à la série zêta
de la plateforme envoyée dans `K` (de caractéristique nulle), cela donne les comptages :
`N_m = ∑_{b ∈ β} b^m - ∑_{a ∈ α} a^m`.
-/

open PowerSeries

namespace WeilConjectures.Bridge

section Field

variable {K : Type*} [Field K]

/-- La série des sommes de puissances `∑_m (∑_{a ∈ s} a^{m+1}) T^m`. -/
def powerSumSeries (s : Multiset K) : K⟦X⟧ :=
  PowerSeries.mk fun m ↦ (s.map (· ^ (m + 1))).sum

@[simp]
theorem coeff_powerSumSeries (s : Multiset K) (m : ℕ) :
    coeff m (powerSumSeries s) = (s.map (· ^ (m + 1))).sum := by
  simp [powerSumSeries]

theorem powerSumSeries_zero : powerSumSeries (0 : Multiset K) = 0 := by
  ext
  simp

theorem powerSumSeries_cons (a : K) (s : Multiset K) :
    powerSumSeries (a ::ₘ s) = PowerSeries.mk (fun m ↦ a ^ (m + 1)) + powerSumSeries s := by
  ext
  simp

theorem mk_pow_succ_mul_one_sub (a : K) :
    PowerSeries.mk (fun m ↦ a ^ (m + 1)) * (1 - C a * X) = C a := by
  have h : PowerSeries.mk (fun m ↦ a ^ (m + 1)) = C a * rescale a (PowerSeries.mk 1) := by
    ext n
    simp [coeff_rescale, pow_succ, mul_comm]
  rw [h, ← rescale_X, mul_assoc]
  have hsub : (1 : K⟦X⟧) - rescale a X = rescale a (1 - X) := by
    rw [map_sub, map_one]
  rw [hsub, ← map_mul, mk_one_mul_one_sub_eq_one, map_one, mul_one]

/-- Le produit `∏_{a ∈ s} (1 - aT)`. -/
noncomputable def oneSubProd (s : Multiset K) : K⟦X⟧ :=
  (s.map fun a ↦ (1 - C a * X : K⟦X⟧)).prod

theorem constantCoeff_oneSubProd (s : Multiset K) : constantCoeff (oneSubProd s) = 1 := by
  rw [oneSubProd, map_multiset_prod, Multiset.map_map]
  simp

theorem oneSubProd_ne_zero (s : Multiset K) : oneSubProd s ≠ 0 := by
  intro h
  simpa [h] using constantCoeff_oneSubProd s

theorem derivative_oneSubProd (s : Multiset K) :
    d⁄dX K (oneSubProd s) = -(powerSumSeries s * oneSubProd s) := by
  induction s using Multiset.induction_on with
  | empty => simp [oneSubProd, powerSumSeries_zero]
  | cons a s ih =>
    simp only [oneSubProd] at ih ⊢
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, ih, powerSumSeries_cons]
    have hd : d⁄dX K (1 - C a * X : K⟦X⟧) = -C a := by
      rw [map_sub, Derivation.leibniz, derivative_C, derivative_X]
      simp
    rw [hd, smul_eq_mul, smul_eq_mul]
    linear_combination (s.map fun a ↦ (1 - C a * X : K⟦X⟧)).prod * mk_pow_succ_mul_one_sub a

/-- **Dérivée logarithmique** : si `Z' = c Z` et `Z · ∏_β (1 - bT) = ∏_α (1 - aT)`, alors
`c = S_β - S_α`. -/
theorem eq_powerSumSeries_sub {Z c : K⟦X⟧} (hZ' : d⁄dX K Z = c * Z) {α β : Multiset K}
    (h : Z * oneSubProd β = oneSubProd α) :
    c = powerSumSeries β - powerSumSeries α := by
  have hd := congrArg (d⁄dX K) h
  rw [Derivation.leibniz, derivative_oneSubProd, derivative_oneSubProd, hZ', smul_eq_mul,
    smul_eq_mul] at hd
  have hz : (c - powerSumSeries β + powerSumSeries α) * (Z * oneSubProd β) = 0 := by
    linear_combination hd + powerSumSeries α * h
  rw [h] at hz
  have := (mul_eq_zero.mp hz).resolve_right (oneSubProd_ne_zero α)
  linear_combination this

end Field

section Map

variable {R S : Type*} [CommRing R] [CommRing S]

theorem derivative_map (f : R →+* S) (φ : R⟦X⟧) :
    d⁄dX S (PowerSeries.map f φ) = PowerSeries.map f (d⁄dX R φ) := by
  ext n
  simp [coeff_derivative]

end Map

/-- **Comptages par les racines inverses.** Si la série zêta de la plateforme, envoyée dans un corps
`K` de caractéristique nulle, vérifie `Z · ∏_β (1 - bT) = ∏_α (1 - aT)`, alors
`N_m = ∑_{b ∈ β} b^m - ∑_{a ∈ α} a^m` pour `m ≥ 1`. -/
theorem cast_count_eq_of_map_zetaOfCounts_mul {K : Type*} [Field K] [CharZero K] (N : ℕ → ℕ)
    {α β : Multiset K}
    (h : PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N) * oneSubProd β = oneSubProd α)
    {m : ℕ} (hm : 0 < m) :
    (N m : K) = (β.map (· ^ m)).sum - (α.map (· ^ m)).sum := by
  have hZ' : d⁄dX K (PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N)) =
      PowerSeries.map (algebraMap ℚ K) (countingSeries N) *
        PowerSeries.map (algebraMap ℚ K) (zetaOfCounts N) := by
    rw [derivative_map, derivative_zetaOfCounts, map_mul]
  have hc := congrArg (coeff (m - 1)) (eq_powerSumSeries_sub hZ' h)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm.ne'
  simpa using hc

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/InverseRoots.lean` -/

section

/-!
# Racines inverses d'un polynôme de terme constant 1 (partie G)

Pour un polynôme `p` de terme constant `1` sur un corps algébriquement clos, les racines de son
polynôme réciproque `p.reverse` sont ses *racines inverses* : `p = ∏ (1 - a X)`. Quand `p`
vérifie de plus l'équation fonctionnelle `p_{2g-i} q^i = q^g p_i` (celle du L-polynôme d'une
courbe), ces racines sont stables par `a ↦ q / a`, et `p(1/(qt)) = q^{-g} t^{-2g} p(t)`.
-/

open Polynomial

namespace WeilConjectures.Bridge

section Reverse

variable {R S : Type*} [Semiring R] [Semiring S]

theorem reverse_map_of_injective (f : R →+* S) (hf : Function.Injective f) (p : R[X]) :
    (p.map f).reverse = p.reverse.map f := by
  ext n
  simp [coeff_reverse, coeff_map, natDegree_map_eq_of_injective hf]

theorem reverse_reverse_of_coeff_zero_ne_zero {p : R[X]} (h : p.coeff 0 ≠ 0) :
    p.reverse.reverse = p := by
  have ht : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr h)
  have hd : p.reverse.natDegree = p.natDegree := by
    rw [reverse_natDegree, ht, Nat.sub_zero]
  ext n
  rw [coeff_reverse, hd, coeff_reverse, revAt_invol]

theorem reverse_one' : (1 : R[X]).reverse = 1 := by
  ext n
  rw [coeff_reverse, natDegree_one]
  rcases n with _ | n <;> simp [revAt]

end Reverse

section Field

variable {K : Type*} [Field K]

theorem reverse_X_sub_C (a : K) : (X - C a).reverse = 1 - C a * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_C]
  have hX : reflect 1 (X : K[X]) = 1 := by
    have := reflect_monomial (R := K) 1 1
    rwa [pow_one, revAt_le le_rfl, Nat.sub_self, pow_zero] at this
  rw [hX, pow_one]

theorem reverse_multiset_prod (s : Multiset K[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse_one']
  | cons a s ih => rw [Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons]

/-- Le polynôme réciproque d'un polynôme de terme constant `1` est unitaire. -/
theorem monic_reverse_of_coeff_zero_eq_one {p : K[X]} (h0 : p.coeff 0 = 1) : p.reverse.Monic := by
  rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by simp [h0]), h0]

/-- **Factorisation en racines inverses** : `p = ∏_{a} (1 - a X)`, où `a` parcourt les racines
du polynôme réciproque. -/
theorem eq_prod_one_sub_C_mul_X [IsAlgClosed K] {p : K[X]} (h0 : p.coeff 0 = 1) :
    p = (p.reverse.roots.map fun a ↦ 1 - C a * X).prod := by
  have hsplit : (p.reverse.roots.map fun a ↦ X - C a).prod = p.reverse :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_reverse_of_coeff_zero_eq_one h0)
      IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← reverse_reverse_of_coeff_zero_ne_zero (p := p) (by simp [h0]), ← hsplit]
  rw [reverse_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun a _ ↦ reverse_X_sub_C a

/-- Les racines du polynôme réciproque sont non nulles. -/
theorem ne_zero_of_mem_roots_reverse {p : K[X]} (hp : p ≠ 0) {a : K}
    (ha : a ∈ p.reverse.roots) : a ≠ 0 := by
  rintro rfl
  have h := (mem_roots (by simpa [reverse_eq_zero] using hp)).mp ha
  rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero_reverse] at h
  exact hp (leadingCoeff_eq_zero.mp h)

/-- Les racines de `p` sont les inverses de celles de `p.reverse`. -/
theorem roots_eq_map_inv_roots_reverse [IsAlgClosed K] {p : K[X]} (h0 : p.coeff 0 = 1) :
    p.roots = p.reverse.roots.map (·⁻¹) := by
  have hp : p ≠ 0 := fun h ↦ by simp [h] at h0
  have hfac := eq_prod_one_sub_C_mul_X h0
  have hlin : ∀ a ∈ p.reverse.roots,
      (1 - C a * X : K[X]) = C (-a) * X - C (-1) := by
    intro a _
    simp only [C_neg, C_1]
    ring
  conv_lhs => rw [hfac, Multiset.map_congr rfl hlin]
  rw [roots_multiset_prod, Multiset.bind_map]
  · refine (Multiset.bind_congr fun a ha ↦ ?_).trans (Multiset.bind_singleton _ _)
    rw [roots_C_mul_X_sub_C _ (neg_ne_zero.mpr (ne_zero_of_mem_roots_reverse hp ha))]
    simp
  · rw [Multiset.mem_map]
    rintro ⟨a, ha, h⟩
    have := congrArg (coeff · 1) h
    simp [coeff_one] at this
    exact ne_zero_of_mem_roots_reverse hp ha this

end Field

section FunctionalEquation

variable {K : Type*} [Field K] {p : K[X]} {q : K} {g : ℕ}

/-- L'équation fonctionnelle force le degré exact `2g`. -/
theorem natDegree_eq_of_symm (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.natDegree = 2 * g := by
  refine le_antisymm hdeg (le_natDegree_of_ne_zero ?_)
  have := hsymm 0 (Nat.zero_le _)
  rw [Nat.sub_zero, pow_zero, mul_one, h0, mul_one] at this
  rw [this]
  exact pow_ne_zero _ hq

/-- Le polynôme réciproque est, à un scalaire près, `p (X / q)`. -/
theorem reverse_eq_C_mul_comp (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.reverse = C (q ^ g) * p.comp (C q⁻¹ * X) := by
  have hd := natDegree_eq_of_symm hq h0 hdeg hsymm
  ext i
  rw [coeff_reverse, hd, coeff_C_mul, comp_C_mul_X_coeff]
  by_cases hi : i ≤ 2 * g
  · rw [revAt_le hi, inv_pow, ← mul_assoc, ← hsymm i hi]
    field_simp
  · push Not at hi
    rw [← revAtFun_eq, revAtFun, if_neg (by omega),
      coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- **Symétrie des racines inverses** : `a ↦ q / a` permute les racines de `p.reverse`. -/
theorem roots_reverse_map_div [IsAlgClosed K] (hq : q ≠ 0) (h0 : p.coeff 0 = 1)
    (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) :
    p.reverse.roots.map (q / ·) = p.reverse.roots := by
  have hcomp : (p.comp (C q⁻¹ * X)).roots = p.roots.map (q * ·) := by
    have := roots_comp_C_mul_X_add_C p q⁻¹ 0 (isUnit_iff_ne_zero.mpr (inv_ne_zero hq))
    simpa [Ring.inverse_eq_inv'] using this
  conv_rhs => rw [reverse_eq_C_mul_comp hq h0 hdeg hsymm, roots_C_mul _ (pow_ne_zero _ hq),
    hcomp, roots_eq_map_inv_roots_reverse h0, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ ↦ by simp [div_eq_mul_inv]

/-- **Équation fonctionnelle sur les valeurs** : `p(1/(qt)) = q^{-g} t^{-2g} p(t)`. -/
theorem eval_inv_mul_eq (hq : q ≠ 0) (h0 : p.coeff 0 = 1) (hdeg : p.natDegree ≤ 2 * g)
    (hsymm : ∀ i ≤ 2 * g, p.coeff (2 * g - i) * q ^ i = q ^ g * p.coeff i) {t : K}
    (ht : t ≠ 0) :
    p.eval (q * t)⁻¹ = (q ^ g)⁻¹ * (t ^ (2 * g))⁻¹ * p.eval t := by
  have hd := natDegree_eq_of_symm hq h0 hdeg hsymm
  let := invertibleOfNonzero ht
  have h := eval₂_reverse_mul_pow (RingHom.id K) t p
  rw [invOf_eq_inv, reverse_eq_C_mul_comp hq h0 hdeg hsymm, hd] at h
  simp only [eval₂_id, eval_mul, eval_C, eval_comp, eval_X] at h
  rw [← h, mul_inv]
  field_simp

end FunctionalEquation

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/CurvesFunctionField.lean` -/

section

/-!
# Les conjectures de Weil pour une courbe, côté corps de fonctions (parties F, G, H)

On démontre la conclusion de `WeilConjectures.weil_conjectures_curves` pour un corps de fonctions
`F₀ / k`, à partir des nœuds PROVED du projet FLT, sous **une seule hypothèse géométrique** :
les comptages `N m` sont donnés par les places, `N m = ∑_{d ∣ m} d · #{places de degré d}`
(ce sera la partie E pour `N = pointCount p f`).

* **F** : la série zêta est la série des diviseurs effectifs, et le L-polynôme `L` du projet
  FLT donne la rationalité `Z (1 - T) (1 - qT) = L`.
* **G** : `L = ∏ (1 - aT)` sur les racines `a` de `L.reverse`, stables par `a ↦ q / a`, et
  l'équation fonctionnelle `Z(1/(qt)) = q^{1-g} t^{2-2g} Z(t)`.
* **H** : `N m = 1 + q^m - ∑ a^m`, ce qui fournit l'hypothèse `hfix` du théorème FLT de
  l'hypothèse de Riemann appliqué à `P = L.reverse` ; d'où `‖a‖ = √q`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

namespace WeilConjectures.Bridge

/-- La conclusion de `weil_conjectures_curves`, recopiée telle quelle, avec `q = Nat.card k` et
`Z = zetaFunction p f`. -/
def CurvesConclusion (q : ℕ) (Z : PowerSeries ℚ) : Prop :=
  ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ),
      Z *
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * 1) = 1 - C ((q : ℤ) ^ 1) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        ∀ t : ℂ, t ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, aeval t (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
              aeval (((q : ℂ) ^ 1 * t)⁻¹) (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd,
                aeval (((q : ℂ) ^ 1 * t)⁻¹) (P i)) /
              (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
                aeval (((q : ℂ) ^ 1 * t)⁻¹) (P i)) =
            ε * (((q : ℝ) ^ ((1 : ℝ) *
                ((∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ) : ℤ) : ℝ)
                  / 2) : ℝ) : ℂ) *
              t ^ (∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) *
              ((∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd, aeval t (P i)) /
                (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, aeval t (P i)))) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 →
        α (2 * 1 - i) = (α i).map fun a => (q : ℂ) ^ 1 / a) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 → ∀ a ∈ α i,
        ‖a‖ = (q : ℝ) ^ ((i : ℝ) / 2))

section FunctionField

variable (k F₀ : Type*) [Field k] [Finite k] [Field F₀] [Algebra k F₀]
  [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]

/-- `A_n` : le nombre de diviseurs effectifs de degré `n`. -/
noncomputable abbrev effCount (n : ℕ) : ℕ :=
  Nat.card {D : AlgebraicCurve.Divisor k F₀ //
    0 ≤ D ∧ AlgebraicCurve.Divisor.degree D = (n : ℤ)}

/-- Le comptage par les places : `∑_{d ∣ m} d · #{places de degré d}`. -/
noncomputable abbrev placeCount (m : ℕ) : ℕ :=
  ∑ d ∈ Nat.divisors m, d * Nat.card {v : AlgebraicCurve.Place k F₀ | v.deg = d}

/-- **F1.** La série zêta des comptages par les places est la série des diviseurs effectifs. -/
theorem zetaOfCounts_eq_mk_effCount {N : ℕ → ℕ} (hN : ∀ m, 0 < m → N m = placeCount k F₀ m)
    (hA0 : effCount k F₀ 0 = 1) :
    zetaOfCounts N = PowerSeries.mk fun n ↦ (effCount k F₀ n : ℚ) := by
  refine (IsZetaSeries.eq_zetaOfCounts ⟨?_, ?_⟩).symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hA0,
      Nat.cast_one]
  · ext n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_countingSeries, PowerSeries.coeff_mk]
    have h := AlgebraicCurve.card_effectiveDivisors_mul_eq_sum k F₀ (n + 1)
    have h' : (n + 1) * effCount k F₀ (n + 1) =
        ∑ i ∈ Finset.range (n + 1), N (i + 1) * effCount k F₀ (n - i) := by
      have hI : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
        ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [h, hI, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by simp) fun i hi ↦ ?_
      rw [hN (i + 1) (Nat.succ_pos i), add_comm 1 i,
        show n + 1 - (i + 1) = n - i by omega]
    exact_mod_cast (mul_comm _ _).trans h'

end FunctionField

section Main

theorem natDegree_one_sub_C_mul_X {c : ℤ} (hc : c ≠ 0) : (1 - C c * X : ℤ[X]).natDegree = 1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X c hc]
  simp

theorem natDegree_one_sub_X : (1 - X : ℤ[X]).natDegree = 1 := by
  simpa using natDegree_one_sub_C_mul_X (c := 1) one_ne_zero

theorem coe_oneSubProd {K : Type*} [Field K] (s : Multiset K) :
    (((s.map fun a ↦ 1 - C a * X).prod : K[X]) : PowerSeries K) = oneSubProd s := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_multiset_prod, Multiset.map_map,
    oneSubProd]
  congr 1
  refine Multiset.map_congr rfl fun a _ ↦ ?_
  simp [Polynomial.coeToPowerSeries.ringHom_apply]

/-- **Théorème conditionnel (parties F, G, H).** Pour un corps de fonctions `F₀ / k` muni de son
extension des constantes `F / K` et du Frobenius `φ`, si les comptages `N m` sont donnés par les
places, la conclusion de `weil_conjectures_curves` vaut pour `zetaOfCounts N`. -/
theorem curvesConclusion_of_functionField
    (k K F₀ F : Type*) [Field k] [Finite k] [Field K] [IsAlgClosed K] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra K F] [Algebra F₀ F]
    [AlgebraicCurve.IsCurveOver k F₀] [Algebra.EssFiniteType k F₀]
    [AlgebraicCurve.IsCurveOver K F]
    (hfg : ∃ s : Finset F₀, IntermediateField.adjoin k (s : Set F₀) = ⊤)
    (hgen : IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤)
    (φ : F →ₐ[K] F) (hφi : φ.toRingHom.IsIntegral)
    (hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Nat.card k))
    {N : ℕ → ℕ} (hN : ∀ m, 0 < m → N m = placeCount k F₀ m) :
    CurvesConclusion (Nat.card k) (zetaOfCounts N) := by
  have hC := AlgebraicCurve.constantsAreBase_of_apply_algebraMap_eq_pow_card k K F₀ F hfg hgen
    φ hφ
  obtain ⟨L, hLdeg, hL0, hLsymm, hLser⟩ := AlgebraicCurve.exists_LPolynomial_of_finite k F₀ hC
  have hgenus := AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
    k K F₀ F hfg hgen φ hφ hC
  set g := AlgebraicCurve.genusFF k F₀ with hg
  set q := Nat.card k with hq
  have hq0 : 0 < q := Nat.card_pos
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  -- F : la série zêta est la série des diviseurs effectifs.
  have hA0 : effCount k F₀ 0 = 1 := by
    have := congrArg (PowerSeries.coeff 0) hLser
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_sub, map_one,
      PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, mul_zero, sub_zero, one_mul,
      Polynomial.constantCoeff_coe, hL0] at this
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk] at this
    exact_mod_cast this
  have hZ := zetaOfCounts_eq_mk_effCount k F₀ hN hA0
  have hrat : zetaOfCounts N *
      (((1 - X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ) *
        ((1 - C (q : ℤ) * X : ℤ[X]).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
      (L.map (Int.castRingHom ℚ) : PowerSeries ℚ) := by
    have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hLser
    rw [Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe,
      Polynomial.polynomial_map_coe, ← h, hZ]
    simp only [map_mul, map_sub, map_one, PowerSeries.map_X, PowerSeries.map_C,
      Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_mul,
      Polynomial.coe_C]
    have hmk : PowerSeries.map (Int.castRingHom ℚ)
        (PowerSeries.mk fun n ↦ (effCount k F₀ n : ℤ)) =
        PowerSeries.mk fun n ↦ (effCount k F₀ n : ℚ) := by
      ext n
      simp
    rw [hmk]
    simp only [eq_intCast, Int.cast_natCast]
    ring
  -- G : racines inverses.
  set Lc := L.map (Int.castRingHom ℂ) with hLc
  have hLc0 : Lc.coeff 0 = 1 := by simp [Lc, coeff_map, hL0]
  have hLcdeg : Lc.natDegree ≤ 2 * g := natDegree_map_le.trans hLdeg
  have hLcsymm : ∀ i ≤ 2 * g, Lc.coeff (2 * g - i) * (q : ℂ) ^ i = (q : ℂ) ^ g * Lc.coeff i := by
    intro i hi
    have := congrArg (Int.cast : ℤ → ℂ) (hLsymm i hi)
    push_cast at this
    simpa [Lc, coeff_map] using this
  have hLc_ne : Lc ≠ 0 := fun h ↦ by simp [h] at hLc0
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hLnat : L.natDegree = 2 * g := by
    rw [← natDegree_map_eq_of_injective hinj]
    exact natDegree_eq_of_symm hqC hLc0 hLcdeg hLcsymm
  set α₁ := Lc.reverse.roots with hα₁
  have hfac : Lc = (α₁.map fun a ↦ 1 - C a * X).prod := eq_prod_one_sub_C_mul_X hLc0
  -- Les ensembles d'indices pairs et impairs.
  have hE : (Finset.range (2 * 1 + 1)).filter Even = {0, 2} := by decide
  have hO : (Finset.range (2 * 1 + 1)).filter Odd = {1} := by decide
  refine ⟨fun i ↦ if i = 0 then 1 - X else if i = 1 then L else if i = 2 then 1 - C (q : ℤ) * X
      else 1, fun i ↦ if i = 1 then α₁ else 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Rationalité.
    rw [hE, hO, Finset.prod_pair (by norm_num), Finset.prod_singleton]
    simpa using hrat
  · simp
  · simp
  · intro i h1 h2
    obtain rfl : i = 1 := by omega
    simp only [one_ne_zero, if_false, if_true]
    exact ⟨hfac, fun a ha ↦ ne_zero_of_mem_roots_reverse hLc_ne ha⟩
  · -- Équation fonctionnelle.
    have hχ : (∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i *
        (((fun i ↦ if i = 0 then 1 - X else if i = 1 then L else if i = 2 then
          1 - C (q : ℤ) * X else 1) i : ℤ[X]).natDegree : ℤ)) = 2 - 2 * (g : ℤ) := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.mul_one]
      norm_num only
      simp only [↓reduceIte]
      rw [natDegree_one_sub_X, hLnat, natDegree_one_sub_C_mul_X hqZ]
      push_cast
      ring
    refine ⟨1, Or.inl rfl, fun t ht hev hev' ↦ ?_⟩
    rw [hχ]
    have h02 : (0 : ℕ) ≠ 2 := by norm_num
    simp only [hE, hO, Finset.prod_pair h02, Finset.prod_singleton] at hev hev' ⊢
    simp only [↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, pow_one,
      aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, ← hLc, Polynomial.map_sub,
      Polynomial.map_one, Polynomial.map_X, Polynomial.map_mul, eval_sub,
      eval_one, eval_X, eval_mul, eq_intCast, Int.cast_natCast, Polynomial.map_natCast,
      eval_natCast] at hev hev' ⊢
    have hpow : (((q : ℝ) ^ ((1 : ℝ) * ((((2 : ℤ) - 2 * (g : ℤ) : ℤ)) : ℝ) / 2) : ℝ) : ℂ) =
        (q : ℂ) / (q : ℂ) ^ g := by
      have he : (1 : ℝ) * ((((2 : ℤ) - 2 * (g : ℤ) : ℤ)) : ℝ) / 2 = (((1 : ℤ) - g : ℤ) : ℝ) := by
        push_cast
        ring
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
      rw [he, Real.rpow_intCast, zpow_sub₀ hqR, zpow_one, zpow_natCast]
      push_cast
      rfl
    have htpow : t ^ ((2 : ℤ) - 2 * (g : ℤ)) = t ^ 2 / t ^ (2 * g) := by
      rw [zpow_sub₀ ht, show (2 * (g : ℤ)) = ((2 * g : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
      norm_cast
    rw [hpow, htpow, eval_inv_mul_eq hqC hLc0 hLcdeg hLcsymm ht]
    have h1 : (1 : ℂ) - t ≠ 0 := left_ne_zero_of_mul hev
    have h2 : (1 : ℂ) - q * t ≠ 0 := right_ne_zero_of_mul hev
    have h3 : (q : ℂ) * t - 1 ≠ 0 := fun h ↦ h2 (by linear_combination -h)
    have h4 : t - 1 ≠ 0 := fun h ↦ h1 (by linear_combination -h)
    have e1 : (1 : ℂ) - (q * t)⁻¹ = (q * t - 1) / (q * t) := by field_simp
    have e2 : (1 : ℂ) - q * (q * t)⁻¹ = (t - 1) / t := by field_simp
    rw [e1, e2]
    field_simp
    ring
  · intro i h1 h2
    obtain rfl : i = 1 := by omega
    simp only [pow_one, show 2 * 1 - 1 = 1 by rfl, if_true]
    exact (roots_reverse_map_div hqC hLc0 hLcdeg hLcsymm).symm
  · -- Hypothèse de Riemann.
    intro i h1 h2
    obtain rfl : i = 1 := by omega
    simp only [if_true]
    intro a ha
    have hPmonic : L.reverse.Monic := by
      rw [Monic, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero (by simp [hL0]), hL0]
    have hLt : L.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (.inr (by simp [hL0]))
    have hdegP : L.reverse.natDegree = 2 * AlgebraicCurve.genusFF K F := by
      rw [reverse_natDegree, hLt, Nat.sub_zero, hLnat, hgenus]
    have h0P : L.reverse.coeff 0 = (q : ℤ) ^ AlgebraicCurve.genusFF K F := by
      have := hLsymm 0 (Nat.zero_le _)
      rw [Nat.sub_zero, pow_zero, mul_one, hL0, mul_one] at this
      rw [coeff_zero_reverse, leadingCoeff, hLnat, this, hgenus]
    have hrootsP : (L.reverse.map (Int.castRingHom ℂ)).roots = α₁ := by
      rw [← reverse_map_of_injective _ hinj]
    have hprod : PowerSeries.map (algebraMap ℚ ℂ) (zetaOfCounts N) * oneSubProd {1, (q : ℂ)} =
        oneSubProd α₁ := by
      have h := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hrat
      rw [map_mul] at h
      rw [← coe_oneSubProd α₁, ← hfac]
      convert h using 2
      · simp only [oneSubProd, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
          Multiset.prod_cons, Multiset.prod_singleton, map_one, one_mul]
        simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.map_mul,
          Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X,
          Polynomial.coe_mul, map_mul, map_sub, map_one, PowerSeries.map_X,
          Polynomial.map_natCast, map_natCast]
        have hc : ((q : ℚ[X]) : PowerSeries ℚ) = (q : PowerSeries ℚ) := by
          rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_natCast]
        rw [hc, map_natCast]
      · rw [hLc, Polynomial.polynomial_map_coe, Polynomial.polynomial_map_coe,
          ← RingHom.comp_apply, ← PowerSeries.map_comp]
        congr 2
    have hfix : ∀ n : ℕ, 0 < n →
        (Nat.card (Function.fixedPoints
            (AlgebraicCurve.Place.restrictAlong φ hφi)^[n]) : ℂ) =
          (q : ℂ) ^ n + 1 -
            (((L.reverse.map (Int.castRingHom ℂ)).roots.map fun z ↦ z ^ n).sum) := by
      intro n hn
      rw [(AlgebraicCurve.finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors
        k K F₀ F hfg hgen φ hφi hφ n hn).2, ← placeCount, ← hN n hn,
        cast_count_eq_of_map_zetaOfCounts_mul N hprod hn, hrootsP]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton, one_pow]
      ring
    have hRH := AlgebraicCurve.norm_eq_sqrt_of_mem_roots_of_natCard_fixedPoints_restrictAlong_eq
      k K F₀ F hfg hgen φ hφi hφ L.reverse hPmonic hdegP h0P hfix
    rw [hrootsP] at hRH
    rw [hRH a ha, Real.sqrt_eq_rpow, Nat.cast_one]

end Main

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/CurveSetup.lean` -/

section

/-!
# Des hypothèses sur `X` au corps de fonctions `F₀` (partie C)

Pour `f : X ⟶ Spec k` lisse de dimension relative 1, géométriquement irréductible et projectif :
* **C1** `f` est propre ;
* **C2** `f` est géométriquement intègre, donc `X` est intègre ;
* **C3** `F₀ = X.functionField` (muni de `baseToFunctionField f`) est un corps de fonctions de
  courbe (`IsCurveOver`), essentiellement de type fini sur `k` ;
* **C4** `F₀` est engendré, comme corps, par un nombre fini d'éléments (`hfg`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

attribute [local instance] MvPolynomial.gradedAlgebra

section Proper

variable {k : Type} [Field k]

/-- Le morphisme `Spec 𝒜₀ ⟶ Spec k` est fini : `k → 𝒜₀` est surjectif, car les polynômes
homogènes de degré 0 sont les constantes. -/
theorem surjective_algebraMap_grade_zero (N : ℕ) :
    Function.Surjective (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)) := by
  intro x
  have hx : (x : MvPolynomial (Fin (N + 1)) k) ∈ (1 : Submodule k _) := by
    rw [← MvPolynomial.homogeneousSubmodule_zero]
    exact x.2
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hx
  exact ⟨y, Subtype.ext hy⟩

/-- **C1.** Un `k`-schéma projectif est propre. -/
theorem isProper_of_isProjectiveOver {X : Scheme} (f : X ⟶ Spec (.of k))
    (h : IsProjectiveOver k f) : IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.Finite.of_surjective _ (surjective_algebraMap_grade_zero N)
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
      (MvPolynomial (Fin (N + 1)) k) :=
    haveI : IsScalarTower k (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (MvPolynomial (Fin (N + 1)) k) :=
      IsScalarTower.of_algebraMap_eq (R := k)
        (S := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k 0)
        (A := MvPolynomial (Fin (N + 1)) k) fun _ ↦ rfl
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  unfold projectiveSpace.toSpec
  infer_instance

end Proper

section Integral

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- **C2.** Une courbe lisse géométriquement irréductible est géométriquement intègre. -/
theorem geometricallyIntegral_of_curve [SmoothOfRelativeDimension 1 f]
    [GeometricallyIrreducible f] : GeometricallyIntegral f := by
  have := AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected f
  exact AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected f

/-- **C2.** Le schéma `X` est intègre. -/
theorem isIntegral_of_curve [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    [IsProper f] : IsIntegral X := by
  have := geometricallyIntegral_of_curve f
  exact AlgebraicGeometry.isIntegral_of_smoothOfRelativeDimension_one_of_geometricallyIntegral f

/-- **C3.** Le corps de fonctions est un corps de fonctions de courbe sur `k`. -/
theorem isCurveOver_functionField [IsIntegral X] [SmoothOfRelativeDimension 1 f] :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    AlgebraicCurve.IsCurveOver k X.functionField :=
  letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
    f (RingEquiv.refl _) fun _ ↦ rfl

end Integral

section FiniteGeneration

/-- **C4.** Un corps essentiellement de type fini est engendré, comme corps, par une partie
finie. -/
theorem exists_finset_adjoin_eq_top_of_essFiniteType {k F : Type*} [Field k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] :
    ∃ s : Finset F, IntermediateField.adjoin k (s : Set F) = ⊤ := by
  obtain ⟨s, hs⟩ := Algebra.EssFiniteType.cond (R := k) (S := F)
  refine ⟨s, eq_top_iff.mpr fun x _ ↦ ?_⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective
    ((IsUnit.submonoid F).comap (algebraMap (Algebra.adjoin k (s : Set F)) F)) x
  have hle : ∀ y : Algebra.adjoin k (s : Set F),
      (y : F) ∈ IntermediateField.adjoin k (s : Set F) := fun y ↦
    IntermediateField.algebra_adjoin_le_adjoin k _ y.2
  have hb : algebraMap (Algebra.adjoin k (s : Set F)) F (b : Algebra.adjoin k (s : Set F)) ≠ 0 :=
    (b.2 : IsUnit _).ne_zero
  have hx : IsLocalization.mk' F a b = algebraMap _ F a /
      algebraMap _ F (b : Algebra.adjoin k (s : Set F)) := by
    rw [eq_div_iff hb, IsLocalization.mk'_spec]
  change IsLocalization.mk' F a b ∈ _
  rw [hx]
  exact div_mem (hle a) (hle b)

end FiniteGeneration

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/CurveBaseChange.lean` -/

section

/-!
# Extension des constantes et Frobenius (partie D)

Soit `F₀ / k` le corps de fonctions de `X`, `K` une clôture algébrique de `k` et `F` le corps de
fonctions de `X_K`. Le projet FLT fournit un morphisme injectif `Φ : K ⊗_k F₀ → F` dont `F` est le
corps des fractions.
* **D3** `K ⊗_k F₀` est déjà un corps (intègre et entier sur `F₀`), donc `Φ` est bijectif et `F`
  est engendré par `K` et `F₀` (`hgen`) ;
* **D4** le Frobenius `φ = id_K ⊗ (x ↦ x^q)`, transporté par `Φ`, vérifie `φ(x) = x^q` sur `F₀` ;
* **D5** `φ` est entier : `F₀` est entier sur `φ(F)` (racine de `Y^q - φ(x)`) et `K ⊆ φ(F)`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace WeilConjectures.Bridge

section Algebraic

variable {k K F₀ F : Type*} [Field k] [Field K] [Field F₀] [Field F]
  [Algebra k K] [Algebra k F₀] [Algebra K F]

/-- La structure de `F₀`-algèbre sur `F` induite par `Φ : K ⊗_k F₀ → F`. -/
noncomputable abbrev tensorAlgebra (Φ : K ⊗[k] F₀ →ₐ[K] F) : Algebra F₀ F :=
  (Φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom).toAlgebra

theorem tensorAlgebra_apply_tmul (Φ : K ⊗[k] F₀ →ₐ[K] F) (a : K) (x : F₀) :
    letI := tensorAlgebra Φ
    Φ (a ⊗ₜ x) = algebraMap K F a * algebraMap F₀ F x := by
  let := tensorAlgebra Φ
  have h : a ⊗ₜ[k] x = (a ⊗ₜ[k] (1 : F₀)) * ((1 : K) ⊗ₜ[k] x) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul]
  congr 1
  rw [← Φ.commutes a, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

/-- **D3.** `K ⊗_k F₀` est un corps, donc `Φ` est surjectif. -/
theorem surjective_of_injective_isFractionRing [Algebra.IsAlgebraic k K]
    (Φ : K ⊗[k] F₀ →ₐ[K] F) (hinj : Function.Injective Φ)
    (hfrac : letI := Φ.toRingHom.toAlgebra; IsFractionRing (K ⊗[k] F₀) F) :
    Function.Surjective Φ := by
  let := Φ.toRingHom.toAlgebra
  have : IsDomain (K ⊗[k] F₀) := hinj.isDomain Φ
  let c := Algebra.TensorProduct.comm k K F₀
  have : IsDomain (F₀ ⊗[k] K) := (hinj.comp c.symm.injective).isDomain (Φ.toRingHom.comp
    c.symm.toRingEquiv.toRingHom)
  have : Algebra.IsIntegral k K := Algebra.IsAlgebraic.isIntegral
  have hF : IsField (F₀ ⊗[k] K) := isField_of_isIntegral_of_isField' (R := F₀) (Field.toIsField F₀)
  have hfield : IsField (K ⊗[k] F₀) := c.toMulEquiv.isField hF
  exact (IsFractionRing.surjective_iff_isField (R := K ⊗[k] F₀) (K := F)).mpr hfield

/-- **D3.** `F` est engendré par `K` et l'image de `F₀`. -/
theorem adjoin_range_eq_top (Φ : K ⊗[k] F₀ →ₐ[K] F) (hsurj : Function.Surjective Φ) :
    letI := tensorAlgebra Φ
    IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  let := tensorAlgebra Φ
  refine eq_top_iff.mpr fun y hy ↦ ?_
  clear hy
  obtain ⟨t, rfl⟩ := hsurj y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a x =>
    rw [tensorAlgebra_apply_tmul]
    exact mul_mem (IntermediateField.algebraMap_mem _ a)
      (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  | add t u ht hu => rw [map_add]; exact add_mem ht hu

/-- **D4, D5.** Le Frobenius `K`-linéaire de `F`. -/
theorem exists_frobenius [Fintype k] (Φ : K ⊗[k] F₀ →ₐ[K] F) (hinj : Function.Injective Φ)
    (hsurj : Function.Surjective Φ) :
    letI := tensorAlgebra Φ
    ∃ (φ : F →ₐ[K] F) (_ : φ.toRingHom.IsIntegral),
      ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Fintype.card k) := by
  let := tensorAlgebra Φ
  let e : K ⊗[k] F₀ ≃ₐ[K] F := AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let fr : K ⊗[k] F₀ →ₐ[K] K ⊗[k] F₀ :=
    Algebra.TensorProduct.map (AlgHom.id K K) (FiniteField.frobeniusAlgHom k F₀)
  let φ : F →ₐ[K] F := (e.toAlgHom.comp fr).comp e.symm.toAlgHom
  have hφ : ∀ x : F₀, φ (algebraMap F₀ F x) = algebraMap F₀ F (x ^ Fintype.card k) := by
    intro x
    have h1 : algebraMap F₀ F x = e ((1 : K) ⊗ₜ x) := rfl
    have h2 : algebraMap F₀ F (x ^ Fintype.card k) = e ((1 : K) ⊗ₜ (x ^ Fintype.card k)) := rfl
    rw [h1, h2]
    simp [φ, fr, Algebra.TensorProduct.map_tmul]
  refine ⟨φ, fun y ↦ ?_, hφ⟩
  have hK : ∀ a : K, φ.toRingHom.IsIntegralElem (algebraMap K F a) := fun a ↦ by
    have : algebraMap K F a = φ.toRingHom (algebraMap K F a) := (φ.commutes a).symm
    rw [this]
    exact RingHom.isIntegralElem_map _
  have hF₀ : ∀ x : F₀, φ.toRingHom.IsIntegralElem (algebraMap F₀ F x) := fun x ↦ by
    refine ⟨Polynomial.X ^ Fintype.card k - Polynomial.C (algebraMap F₀ F x),
      Polynomial.monic_X_pow_sub_C _ Fintype.card_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    change _ - φ (algebraMap F₀ F x) = 0
    rw [hφ, map_pow, sub_self]
  obtain ⟨t, rfl⟩ := hsurj y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | tmul a x => rw [tensorAlgebra_apply_tmul]; exact (hK a).mul _ (hF₀ x)
  | add t u ht hu => rw [map_add]; exact ht.add _ hu

end Algebraic

section Scheme

variable {k : Type} [Field k] [Finite k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- **Partie D.** Le changement de base de `X` à une clôture algébrique `K` de `k` fournit toutes
les données de « Frobenius » demandées par les nœuds FLT. -/
theorem exists_frobenius_data [IsIntegral X] [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    ∃ (K F : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : Field F) (_ : Algebra K F)
      (_ : Algebra X.functionField F) (_ : AlgebraicCurve.IsCurveOver K F),
      IntermediateField.adjoin K (Set.range (algebraMap X.functionField F)) = ⊤ ∧
      ∃ (φ : F →ₐ[K] F) (_ : φ.toRingHom.IsIntegral),
        ∀ x : X.functionField,
          φ (algebraMap X.functionField F x) = algebraMap X.functionField F (x ^ Nat.card k) := by
  let := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  have := Fintype.ofFinite k
  let K := AlgebraicClosure k
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Algebra K (pullback f s).functionField :=
    (AlgebraicCurve.baseToFunctionField (pullback.snd f s)).toAlgebra
  obtain ⟨hcurve, -, -⟩ :=
    SmoothProperCurve.exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed k f K s
  obtain ⟨Φ, hinj, hfrac, -⟩ :=
    exists_algHom_tensorProduct_functionField_pullback_injective_isFractionRing K f
  have hsurj := surjective_of_injective_isFractionRing Φ hinj hfrac
  obtain ⟨φ, hφi, hφ⟩ := exists_frobenius Φ hinj hsurj
  refine ⟨K, (pullback f s).functionField, inferInstance, inferInstance, inferInstance,
    (AlgebraicCurve.baseToFunctionField (pullback.snd f s)).toAlgebra, tensorAlgebra Φ, hcurve,
    adjoin_range_eq_top Φ hsurj, φ, hφi, ?_⟩
  simpa [Nat.card_eq_fintype_card] using hφ

end Scheme

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/CurvesReduction.lean` -/

section

/-!
# Réduction de `weil_conjectures_curves` au comptage des points (parties C, D, F, G, H)

Les parties C et D construisent, à partir de `f : X ⟶ Spec k`, le corps de fonctions `F₀`, son
extension des constantes `F` et le Frobenius `φ` ; le théorème conditionnel des parties F, G, H
conclut. Il ne reste qu'une hypothèse, la **partie E** :
`N_m = ∑_{d ∣ m} d · #{places de F₀ de degré d}` pour `N = pointCount p f`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

/-- **Réduction à la partie E.** -/
theorem curvesConclusion_of_pointCount_eq (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k]
    [CharP k p] (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f)
    (hE : ∀ _ : IsIntegral X,
      letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
      ∀ m, 0 < m → pointCount p f m = placeCount k X.functionField m) :
    CurvesConclusion (Nat.card k) (zetaFunction p f) := by
  have : IsProper f := isProper_of_isProjectiveOver f hproj
  have : GeometricallyIntegral f := geometricallyIntegral_of_curve f
  have hI : IsIntegral X := isIntegral_of_curve f
  let := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  have : AlgebraicCurve.IsCurveOver k X.functionField := isCurveOver_functionField f
  have : Algebra.EssFiniteType k X.functionField := AlgebraicCurve.essFiniteType_functionField f
  obtain ⟨K, F, _, _, _, _, _, _, hgen, φ, hφi, hφ⟩ := exists_frobenius_data f
  exact curvesConclusion_of_functionField k K X.functionField F
    exists_finset_adjoin_eq_top_of_essFiniteType hgen φ hφi hφ (hE hI)

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/PointsResidue.lean` -/

section

/-!
# Points d'un `k`-schéma à valeurs dans un corps (partie E1)

Pour `f : X ⟶ Spec k` et un corps `L` qui est une `k`-algèbre, les `k`-morphismes
`Spec L ⟶ X` sont en bijection avec les couples `(x, ψ)` où `x ∈ X` et
`ψ : κ(x) →ₐ[k] L`. C'est `Scheme.SpecToEquivOfField` de Mathlib, où l'on lit la condition
« au-dessus de `k` » sur le morphisme de corps résiduels.
-/

set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- Le morphisme structural `k → κ(x)` : sections globales, puis germe en `x`, puis résidu. -/
noncomputable def residueStructure (x : X) : CommRingCat.of k ⟶ X.residueField x :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x

/-- La structure de `k`-algèbre sur le corps résiduel `κ(x)`. -/
noncomputable abbrev residueAlgebra (x : X) : Algebra k (X.residueField x) :=
  (residueStructure f x).hom.toAlgebra

@[reassoc]
theorem fromSpecResidueField_appTop (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  convert Category.id_comp (X.residue x) using 2
  rw [Category.assoc]
  convert (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv_hom_id using 2
  convert Category.id_comp _
  convert (Spec (X.presheaf.stalk x)).presheaf.map_id _
  exact Subsingleton.elim _ _

/-- La condition « au-dessus de `k` » se lit sur le morphisme de corps résiduels. -/
theorem comp_eq_SpecMap_iff {L : Type} [Field L] [Algebra k L] (x : X)
    (ψ : X.residueField x ⟶ CommRingCat.of L) :
    (Spec.map ψ ≫ X.fromSpecResidueField x) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ↔
      residueStructure f x ≫ ψ = CommRingCat.ofHom (algebraMap k L) := by
  have key : ∀ g₁ g₂ : Spec (.of L) ⟶ Spec (.of k), g₁ = g₂ ↔
      (Scheme.ΓSpecIso (.of k)).inv ≫ g₁.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom =
        (Scheme.ΓSpecIso (.of k)).inv ≫ g₂.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom := by
    intro g₁ g₂
    refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ext_of_isAffine ?_⟩
    rwa [cancel_epi, cancel_mono] at h
  rw [key]
  simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc, fromSpecResidueField_appTop_assoc, residueStructure]

/-- Les `k`-morphismes `κ(x) → L` sont les morphismes de corps qui prolongent `k → L`. -/
noncomputable def residueHomEquiv {L : Type} [Field L] [Algebra k L] (x : X) :
    {ψ : X.residueField x ⟶ CommRingCat.of L //
        residueStructure f x ≫ ψ = CommRingCat.ofHom (algebraMap k L)} ≃
      (letI := residueAlgebra f x; X.residueField x →ₐ[k] L) :=
  letI := residueAlgebra f x
  { toFun := fun ψ ↦
      { ψ.1.hom with
        commutes' := fun r ↦ by
          have := congrArg (fun g ↦ g.hom r) ψ.2
          simpa [RingHom.algebraMap_toAlgebra] using this }
    invFun := fun φ ↦ ⟨CommRingCat.ofHom φ.toRingHom, by
      ext r
      change φ ((residueStructure f x).hom r) = algebraMap k L r
      exact φ.commutes r⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- Réorganisation d'un sous-type de type somme. -/
def sigmaSubtypeEquiv {α : Type*} {β : α → Type*} (P : ∀ a, β a → Prop) :
    {σ : Σ a, β a // P σ.1 σ.2} ≃ Σ a, {b : β a // P a b} where
  toFun σ := ⟨σ.1.1, σ.1.2, σ.2⟩
  invFun σ := ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **E1.** Les `k`-points de `X` à valeurs dans un corps `L` : un point `x` de `X` et un
`k`-plongement `κ(x) → L`. -/
noncomputable def pointsOverEquiv (L : Type) [Field L] [Algebra k L] :
    {g : Spec (.of L) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L))} ≃
      Σ x : X, (letI := residueAlgebra f x; X.residueField x →ₐ[k] L) :=
  ((Equiv.subtypeEquiv (Scheme.SpecToEquivOfField L X) fun g ↦ by
      conv_lhs => rw [← (Scheme.SpecToEquivOfField L X).symm_apply_apply g]
      exact comp_eq_SpecMap_iff f _ _).trans
    (sigmaSubtypeEquiv fun x ψ ↦
      residueStructure f x ≫ ψ = CommRingCat.ofHom (algebraMap k L))).trans
    (Equiv.sigmaCongrRight fun x ↦ residueHomEquiv f x)

/-- **E2.** Le nombre de `k`-plongements d'un corps `E` dans `𝔽_{q^m}` vaut `[E : k]` si ce degré
divise `m`, et `0` sinon (un degré infini vaut `0` par convention de `Module.finrank`). -/
theorem natCard_algHom_extension (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [Finite k]
    [CharP k p] (E : Type*) [Field E] [Algebra k E] (m : ℕ) [NeZero m] :
    Nat.card (E →ₐ[k] FiniteField.Extension k p m) =
      if Module.finrank k E ∣ m then Module.finrank k E else 0 := by
  have hL := FiniteField.finrank_extension k p m
  split_ifs with h
  · exact FiniteField.natCard_algHom_of_finrank_dvd (by rw [hL]; exact h)
  · have : IsEmpty (E →ₐ[k] FiniteField.Extension k p m) := by
      rw [← not_nonempty_iff, FiniteField.nonempty_algHom_iff_finrank_dvd, hL]
      exact h
    exact Nat.card_of_isEmpty

/-- **E1 + E2** : `N_m` est le cardinal de `Σ x, (κ(x) →ₐ[k] 𝔽_{q^m})`. -/
theorem pointCount_eq_natCard_sigma (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p] (m : ℕ)
    [NeZero m] :
    pointCount p f m = Nat.card (Σ x : X, (letI := residueAlgebra f x;
      X.residueField x →ₐ[k] FiniteField.Extension k p m)) := by
  rw [pointCount_of_neZero, pointsOver]
  exact Nat.card_congr (pointsOverEquiv f _)

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/PointsPlaces.lean` -/

section

/-!
# La place associée à un point fermé (partie E3)

Pour une courbe lisse `f : X ⟶ Spec k` (`X` intègre), un point `x` dont le corps résiduel est fini
sur `k` est fermé (`X` est de Jacobson), et l'image de sa tige dans `F₀ = X.functionField` est
l'anneau d'une place `v_x` (nœud FLT `exists_place_range_stalk_eq`, valable sur tout corps).
Le corps résiduel de `v_x` est `κ(x)`, comme `k`-algèbre : `deg v_x = [κ(x) : k]`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- `Spec κ(x) ⟶ X ⟶ Spec k` est `Spec` du morphisme structural `k → κ(x)`. -/
theorem fromSpecResidueField_comp (x : X) :
    letI := residueAlgebra f x
    X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.residueField x))) := by
  let := residueAlgebra f x
  have h := (comp_eq_SpecMap_iff f (L := X.residueField x) x (𝟙 _)).mpr rfl
  rw [Spec.map_id] at h
  exact (Category.id_comp _).symm.trans h

/-- **E3 (a).** Un point de corps résiduel fini sur `k` est fermé. -/
theorem isClosed_singleton_of_finite [LocallyOfFiniteType f] (x : X)
    (h : letI := residueAlgebra f x; Module.Finite k (X.residueField x)) :
    IsClosed ({x} : Set X) := by
  let := residueAlgebra f x
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  rw [isClosed_singleton_iff_locallyOfFiniteType]
  have : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := by
    rw [fromSpecResidueField_comp, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finite_algebraMap.mpr h).finiteType
  exact locallyOfFiniteType_of_comp _ f

section Place

variable [IsIntegral X] [SmoothOfRelativeDimension 1 f]

/-- **E3 (b).** La place de `F₀` associée à un point fermé : l'image de sa tige. -/
noncomputable def placeOf (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    AlgebraicCurve.Place k X.functionField :=
  (AlgebraicCurve.exists_place_range_stalk_eq f x hx).choose

theorem range_placeOf (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    (algebraMap (X.presheaf.stalk x) X.functionField).range =
      (placeOf f x hx).toValuationSubring.toSubring :=
  (AlgebraicCurve.exists_place_range_stalk_eq f x hx).choose_spec

/-- La tige en `x` est isomorphe à l'anneau de la place `v_x`. -/
noncomputable def stalkEquivPlace (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    X.presheaf.stalk x ≃+* (placeOf f x hx).toValuationSubring :=
  letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  RingEquiv.ofBijective
    ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
      (placeOf f x hx).toValuationSubring fun s ↦ by
        have : algebraMap (X.presheaf.stalk x) X.functionField s ∈
            (placeOf f x hx).toValuationSubring.toSubring := by
          rw [← range_placeOf f x hx]; exact ⟨s, rfl⟩
        exact this)
    ⟨fun a b h ↦ IsFractionRing.injective (X.presheaf.stalk x) X.functionField
        (congrArg Subtype.val h),
      fun y ↦ by
        have : (y : X.functionField) ∈
            (algebraMap (X.presheaf.stalk x) X.functionField).range := by
          rw [range_placeOf f x hx]; exact y.2
        obtain ⟨s, hs⟩ := this
        exact ⟨s, Subtype.ext hs⟩⟩

theorem stalkEquivPlace_apply (x : X) (hx : IsClosed ({x} : Set X))
    (s : X.presheaf.stalk x) :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    ((stalkEquivPlace f x hx s : (placeOf f x hx).toValuationSubring) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField s :=
  rfl

/-- **E3 (c).** Le degré de la place `v_x` est le degré résiduel `[κ(x) : k]`. -/
theorem deg_placeOf (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    letI := residueAlgebra f x
    (placeOf f x hx).deg = Module.finrank k (X.residueField x) := by
  let := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  let := residueAlgebra f x
  let e : X.residueField x ≃+* (placeOf f x hx).ResidueField :=
    IsLocalRing.ResidueField.mapEquiv (stalkEquivPlace f x hx)
  have he : ∀ a : k, e (algebraMap k (X.residueField x) a) =
      algebraMap k (placeOf f x hx).ResidueField a := by
    intro a
    have hxT : x ∈ (⊤ : X.Opens) := trivial
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, hxT⟩⟩
    let t := f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)
    have h1 : algebraMap k (X.residueField x) a =
        IsLocalRing.residue (X.presheaf.stalk x) (X.presheaf.germ ⊤ x hxT t) := rfl
    have h2 : stalkEquivPlace f x hx (X.presheaf.germ ⊤ x hxT t) =
        algebraMap k (placeOf f x hx).toValuationSubring a := by
      apply Subtype.ext
      rw [stalkEquivPlace_apply, Scheme.algebraMap_germ_eq_germToFunctionField,
        AlgebraicCurve.Place.coe_algebraMap]
      rfl
    rw [h1]
    change IsLocalRing.ResidueField.mapEquiv (stalkEquivPlace f x hx) _ = _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    erw [h2]
    rfl
  exact ((AlgEquiv.ofRingEquiv (f := e) he).toLinearEquiv.finrank_eq).symm

end Place

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/PointsCount.lean` -/

section

/-!
# Comptage des points par les places (parties E4, E5)

* **E4** Pour une courbe propre et lisse `X` (intègre), `x ↦ v_x` est une bijection entre les points
  fermés de `X` et les places de `F₀` (nœuds FLT `eq_of_range_stalk_eq` et
  `exists_closedPoint_range_stalk_eq`).
* **E5** `N_m = ∑_{d ∣ m} d · #{places de degré d}` : un `k`-point sur `𝔽_{q^m}` est un point
  `x` et un plongement `κ(x) → 𝔽_{q^m}` (E1) ; seuls les points fermés en portent (E3), et une
  place de degré `d` en porte `d` si `d ∣ m`, aucun sinon (E2).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

/-- Les `k`-plongements du corps résiduel en `x` dans `L`. -/
abbrev ResidueHom (L : Type) [Field L] [Algebra k L] (x : X) : Type :=
  letI := residueAlgebra f x
  X.residueField x →ₐ[k] L

section Bijection

variable [IsIntegral X] [SmoothOfRelativeDimension 1 f] [IsProper f]

/-- **E4.** Points fermés de `X` et places de `F₀`. -/
noncomputable def closedPointsEquivPlace :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    {x : X // IsClosed ({x} : Set X)} ≃ AlgebraicCurve.Place k X.functionField :=
  letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  Equiv.ofBijective (fun x ↦ placeOf f x.1 x.2)
    ⟨fun x y h ↦ Subtype.ext (AlgebraicCurve.eq_of_range_stalk_eq f x.1 y.1 (by
        rw [range_placeOf f x.1 x.2, range_placeOf f y.1 y.2]
        exact congrArg (fun v : AlgebraicCurve.Place k X.functionField ↦
          v.toValuationSubring.toSubring) h)),
      fun v ↦ by
        obtain ⟨x, hx, hr⟩ := AlgebraicCurve.exists_closedPoint_range_stalk_eq f v
        refine ⟨⟨x, hx⟩, AlgebraicCurve.Place.ext ?_⟩
        have h := (range_placeOf f x hx).symm.trans hr
        ext z
        exact SetLike.ext_iff.mp h z⟩

theorem closedPointsEquivPlace_apply (x : {x : X // IsClosed ({x} : Set X)}) :
    closedPointsEquivPlace f x = placeOf f x.1 x.2 :=
  rfl

end Bijection

section Count

/-- Regrouper les places de degré divisant `m` selon leur degré. -/
theorem sum_deg_eq_placeCount (F₀ : Type) [Field F₀] [Algebra k F₀] {m : ℕ} (hm : m ≠ 0)
    (hS : {v : AlgebraicCurve.Place k F₀ | v.deg ∣ m}.Finite) :
    ∑ v ∈ hS.toFinset, v.deg = placeCount k F₀ m := by
  rw [placeCount, ← Finset.sum_fiberwise_of_maps_to (g := AlgebraicCurve.Place.deg)
    (t := m.divisors) (fun v hv ↦ Nat.mem_divisors.mpr ⟨(hS.mem_toFinset.mp hv), hm⟩)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [Finset.sum_congr rfl (fun v hv ↦ (Finset.mem_filter.mp hv).2), Finset.sum_const,
    smul_eq_mul, mul_comm]
  congr 1
  rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
  congr 1
  ext v
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨h ▸ (Nat.mem_divisors.mp hd).1, h⟩

variable (p : ℕ) [Fact p.Prime] [Finite k] [CharP k p]

/-- **E5 (a).** Seul un point fermé porte un `k`-point à valeurs dans `𝔽_{q^m}`. -/
theorem isClosed_of_residueHom [LocallyOfFiniteType f] (m : ℕ) [NeZero m] {x : X}
    (φ : ResidueHom f (FiniteField.Extension k p m) x) : IsClosed ({x} : Set X) := by
  let := residueAlgebra f x
  exact isClosed_singleton_of_finite f x
    (Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective)

variable [IsIntegral X] [SmoothOfRelativeDimension 1 f] [IsProper f]

/-- **E5.** `N_m = ∑_{d ∣ m} d · #{places de degré d}`. -/
theorem pointCount_eq_placeCount (m : ℕ) [NeZero m] :
    letI := (AlgebraicCurve.baseToFunctionField f).toAlgebra
    ∀ [AlgebraicCurve.IsCurveOver k X.functionField]
      [Algebra.EssFiniteType k X.functionField],
      pointCount p f m = placeCount k X.functionField m := by
  let := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  intro _ _
  let L := FiniteField.Extension k p m
  let e := closedPointsEquivPlace f
  have hdeg : ∀ v : AlgebraicCurve.Place k X.functionField,
      (letI := residueAlgebra f (e.symm v).1
       Module.finrank k (X.residueField (e.symm v).1)) = v.deg := by
    intro v
    have h := deg_placeOf f (e.symm v).1 (e.symm v).2
    rw [← closedPointsEquivPlace_apply, Equiv.apply_symm_apply] at h
    exact h.symm
  have hS : {v : AlgebraicCurve.Place k X.functionField | v.deg ∣ m}.Finite := by
    refine (Set.Finite.biUnion (Nat.divisors m).finite_toSet fun d _ ↦
      AlgebraicCurve.Place.finite_setOf_deg_eq k X.functionField d).subset ?_
    intro v hv
    exact Set.mem_biUnion (Nat.mem_divisors.mpr ⟨hv, NeZero.ne m⟩) rfl
  let : Fintype {v : AlgebraicCurve.Place k X.functionField // v.deg ∣ m} := hS.fintype
  let T : AlgebraicCurve.Place k X.functionField → Type := fun v ↦ ResidueHom f L (e.symm v).1
  have hsupp : ∀ v, Nonempty (T v) → v.deg ∣ m := by
    intro v ⟨φ⟩
    let := residueAlgebra f (e.symm v).1
    have h := FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨φ⟩
    rwa [FiniteField.finrank_extension, hdeg] at h
  let E₁ : (Σ x : X, ResidueHom f L x) ≃
      Σ c : {x : X // IsClosed ({x} : Set X)}, ResidueHom f L c.1 :=
    { toFun := fun σ ↦ ⟨⟨σ.1, isClosed_of_residueHom f p m σ.2⟩, σ.2⟩
      invFun := fun σ ↦ ⟨σ.1.1, σ.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let E₃ : (Σ v, T v) ≃ Σ v : {v : AlgebraicCurve.Place k X.functionField // v.deg ∣ m}, T v.1 :=
    { toFun := fun σ ↦ ⟨⟨σ.1, hsupp σ.1 ⟨σ.2⟩⟩, σ.2⟩
      invFun := fun σ ↦ ⟨σ.1.1, σ.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcard : ∀ v : {v : AlgebraicCurve.Place k X.functionField // v.deg ∣ m},
      Nat.card (T v.1) = v.1.deg := by
    intro v
    let := residueAlgebra f (e.symm v.1).1
    have h := natCard_algHom_extension p (k := k) (X.residueField (e.symm v.1).1) m
    rw [hdeg, if_pos v.2] at h
    exact h
  have hfinite : ∀ v : {v : AlgebraicCurve.Place k X.functionField // v.deg ∣ m},
      Finite (T v.1) := by
    intro v
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    rintro h
    exact NeZero.ne m (Nat.eq_zero_of_zero_dvd (h ▸ v.2))
  rw [pointCount_eq_natCard_sigma f p m, Nat.card_congr ((E₁.trans (Equiv.sigmaCongrLeft' e)).trans E₃),
    Nat.card_sigma, Finset.sum_congr rfl fun v _ ↦ hcard v,
    ← sum_deg_eq_placeCount X.functionField (NeZero.ne m) hS]
  exact (Finset.sum_subtype hS.toFinset (fun v ↦ hS.mem_toFinset) _).symm

end Count

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/CurvesWeil.lean` -/

section

/-!
# Les conjectures de Weil pour une courbe (cas `n = 1`)

Assemblage : la réduction des parties C, D, F, G, H (`curvesConclusion_of_pointCount_eq`) et le
comptage des points par les places (partie E, `pointCount_eq_placeCount`).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

namespace WeilConjectures.Bridge

/-- **`weil_conjectures_curves`**, sous la forme `CurvesConclusion (Nat.card k) (zetaFunction p f)`,
qui est définitionnellement la conclusion de l'énoncé de la plateforme. -/
theorem weil_conjectures_curves_proof (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k]
    [CharP k p] (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    CurvesConclusion (Nat.card k) (zetaFunction p f) := by
  refine curvesConclusion_of_pointCount_eq p k X f hproj fun hI ↦ ?_
  have : IsProper f := isProper_of_isProjectiveOver f hproj
  let := (AlgebraicCurve.baseToFunctionField f).toAlgebra
  have : AlgebraicCurve.IsCurveOver k X.functionField := isCurveOver_functionField f
  have : Algebra.EssFiniteType k X.functionField := AlgebraicCurve.essFiniteType_functionField f
  intro m hm
  have : NeZero m := ⟨hm.ne'⟩
  exact pointCount_eq_placeCount f p m

end WeilConjectures.Bridge

end

/-! ## La solution (énoncé recopié tel quel de la plateforme) -/

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem solution (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p]
    (X : Scheme.{0}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    (hproj : IsProjectiveOver k f) :
    ∃ (P : ℕ → ℤ[X]) (α : ℕ → Multiset ℂ),
      zetaFunction p f *
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
        ∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd,
            ((P i).map (Int.castRingHom ℚ) : PowerSeries ℚ) ∧
      P 0 = 1 - Polynomial.X ∧
      P (2 * 1) = 1 - C ((Nat.card k : ℤ) ^ 1) * Polynomial.X ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 →
        (P i).map (Int.castRingHom ℂ) = ((α i).map fun a => 1 - C a * Polynomial.X).prod ∧
        ∀ a ∈ α i, a ≠ 0) ∧
      (∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        ∀ t : ℂ, t ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, aeval t (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
              aeval (((Nat.card k : ℂ) ^ 1 * t)⁻¹) (P i)) ≠ 0 →
          (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd,
                aeval (((Nat.card k : ℂ) ^ 1 * t)⁻¹) (P i)) /
              (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even,
                aeval (((Nat.card k : ℂ) ^ 1 * t)⁻¹) (P i)) =
            ε * (((Nat.card k : ℝ) ^ ((1 : ℝ) *
                ((∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ) : ℤ) : ℝ)
                  / 2) : ℝ) : ℂ) *
              t ^ (∑ i ∈ Finset.range (2 * 1 + 1), (-1 : ℤ) ^ i * ((P i).natDegree : ℤ)) *
              ((∏ i ∈ (Finset.range (2 * 1 + 1)).filter Odd, aeval t (P i)) /
                (∏ i ∈ (Finset.range (2 * 1 + 1)).filter Even, aeval t (P i)))) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 →
        α (2 * 1 - i) = (α i).map fun a => (Nat.card k : ℂ) ^ 1 / a) ∧
      (∀ i, 1 ≤ i → i ≤ 2 * 1 - 1 → ∀ a ∈ α i,
        ‖a‖ = (Nat.card k : ℝ) ^ ((i : ℝ) / 2)) :=
  WeilConjectures.Bridge.weil_conjectures_curves_proof p k X f hproj
