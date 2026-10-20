-- Prove2me | solution 1 for WeilConjectures.projectiveSpace_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-19T21:03:04.889871+00:00
-- url     : https://prove2.me/submissions/56c29ecc-b807-4ff0-aaf4-321703b928f3

import Mathlib
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

/-!
# Solution de `WeilConjectures.projectiveSpace_zeta` (fichier autonome)

FICHIER ENGENDRÉ par `scripts/assemble_projectiveSpace_zeta.py` à partir de la bibliothèque
`Bridge` : ne pas modifier à la main.

Il n'importe que Mathlib et les deux définitions de la plateforme ; les lemmes intermédiaires sont
recopiés depuis `Bridge/` (espace de noms `WeilConjectures.Bridge`).
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

/-! ## Recopié de `Bridge/Chart.lean` -/

/-!
# Algèbre des cartes affines de `ℙⁿ_k` (partie B1)

Soit `𝒜 = k[X₀, …, Xₙ]` gradué par le degré total, et `Chart k n i = 𝒜_(Xᵢ)` la partie de
degré zéro du localisé en `Xᵢ` (`HomogeneousLocalization.Away`). C'est l'anneau de la carte
`D₊(Xᵢ) ≅ Spec 𝒜_(Xᵢ)` de `Proj 𝒜`.

On décrit ici ses morphismes vers une `k`-algèbre `L` : un morphisme d'anneaux
`φ : 𝒜_(Xᵢ) →+* L` compatible à `k` est déterminé par les valeurs `φ (Xⱼ / Xᵢ)`, et ces valeurs
sont un vecteur quelconque `v` avec `vᵢ = 1` :

`awayHomEquiv : {φ // φ compatible à k} ≃ {v : Fin (n+1) → L // v i = 1}`.

L'ingrédient clé est la déshomogénéisation (`eval₂_ratio_eq_mk`) : pour `x` homogène de degré
`m`, `x / Xᵢ^m = x(X₀/Xᵢ, …, Xₙ/Xᵢ)` dans `𝒜_(Xᵢ)`.

La compatibilité à `k` est formulée par des morphismes d'anneaux plutôt que par une structure de
`k`-algèbre sur `𝒜_(Xᵢ)`, pour coller à la flèche structurale `projectiveSpace.toSpec` de la
plateforme (qui passe par `algebraMap k (𝒜 0)`).
-/

noncomputable section

open MvPolynomial HomogeneousLocalization

namespace WeilConjectures.Bridge

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k] (n : ℕ)

/-- La graduation de `k[X₀, …, Xₙ]` par le degré total. -/
abbrev Grading : ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

theorem X_mem_grading (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) k) ∈ Grading k n 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k j)

/-- L'anneau de la carte `D₊(Xᵢ)` : la partie de degré zéro de `k[X₀, …, Xₙ][1/Xᵢ]`. -/
abbrev Chart (i : Fin (n + 1)) : Type :=
  Away (Grading k n) (X i : MvPolynomial (Fin (n + 1)) k)

variable {k n}

/-- La fonction coordonnée `Xⱼ / Xᵢ` sur la carte `D₊(Xᵢ)`. -/
def ratio (i j : Fin (n + 1)) : Chart k n i :=
  Away.mk (Grading k n) (X_mem_grading k n i) 1 (X j) (by simpa using X_mem_grading k n j)

variable (k n) in
/-- La flèche structurale `k → 𝒜_(Xᵢ)`, via `k → 𝒜 0 → 𝒜_(Xᵢ)` comme dans `projectiveSpace.toSpec`. -/
def chartBase (i : Fin (n + 1)) : k →+* Chart k n i :=
  (algebraMap (Grading k n 0) (Chart k n i)).comp (algebraMap k (Grading k n 0))

/-- **Déshomogénéisation.** Pour `x` homogène de degré `m`, `x / Xᵢ^m` est la valeur de `x` en
les coordonnées `Xⱼ / Xᵢ`. -/
theorem eval₂_ratio_eq_mk (i : Fin (n + 1)) (m : ℕ) (x : MvPolynomial (Fin (n + 1)) k)
    (hx : x ∈ Grading k n (m • 1)) :
    eval₂ (chartBase k n i) (ratio i) x = Away.mk (Grading k n) (X_mem_grading k n i) m x hx := by
  let ι := algebraMap (MvPolynomial (Fin (n + 1)) k)
    (Localization.Away (X i : MvPolynomial (Fin (n + 1)) k))
  let ν := algebraMap (Chart k n i) (Localization.Away (X i : MvPolynomial (Fin (n + 1)) k))
  have hxi : (X i : MvPolynomial (Fin (n + 1)) k) ∈ Submonoid.powers (X i) := Submonoid.mem_powers _
  let u : Localization.Away (X i : MvPolynomial (Fin (n + 1)) k) :=
    IsLocalization.mk' _ (1 : MvPolynomial (Fin (n + 1)) k) ⟨X i, hxi⟩
  have hbase : ν.comp (chartBase k n i) = ι.comp (algebraMap k _) := by
    ext c
    change Localization.mk ((algebraMap k (Grading k n 0) c : MvPolynomial (Fin (n + 1)) k)) 1 = _
    rw [Localization.mk_one_eq_algebraMap]
    rfl
  have hratio : ∀ j, ν (ratio i j) = ι (X j) * u := by
    intro j
    change Localization.mk _ _ = _
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
    congr 2
    exact Subtype.ext (pow_one _)
  have hrhs : ν (Away.mk (Grading k n) (X_mem_grading k n i) m x hx) = ι x * u ^ m := by
    change Localization.mk _ _ = _
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, ← IsLocalization.mk'_pow, one_pow]
    rfl
  have hhom : x.IsHomogeneous m := by
    simpa using (mem_homogeneousSubmodule _ _).mp hx
  apply val_injective
  rw [← HomogeneousLocalization.algebraMap_apply, ← HomogeneousLocalization.algebraMap_apply]
  change ν _ = ν _
  rw [eval₂_comp_left, hbase, hrhs]
  simp_rw [Function.comp_def, hratio]
  conv_lhs => rw [x.as_sum]
  conv_rhs => rw [x.as_sum]
  rw [eval₂_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hdeg : ∑ j, s j = m := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hhom (mem_support_iff.mp hs)
  rw [eval₂_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, map_mul, map_prod,
    map_pow, RingHom.comp_apply, MvPolynomial.algebraMap_eq]
  ring


/-- Deux morphismes `𝒜_(Xᵢ) → L` compatibles à `k` et égaux sur les `Xⱼ / Xᵢ` sont égaux. -/
theorem chart_hom_ext {L : Type*} [CommRing L] [Algebra k L] {i : Fin (n + 1)}
    {φ ψ : Chart k n i →+* L} (hφ : φ.comp (chartBase k n i) = algebraMap k L)
    (hψ : ψ.comp (chartBase k n i) = algebraMap k L) (h : ∀ j, φ (ratio i j) = ψ (ratio i j)) :
    φ = ψ := by
  ext z
  obtain ⟨m, x, hx, rfl⟩ := Away.mk_surjective (Grading k n) (X_mem_grading k n i) z
  rw [← eval₂_ratio_eq_mk i m x hx, eval₂_comp_left, eval₂_comp_left, hφ, hψ]
  congr 1
  funext j
  exact h j

variable {L : Type*} [CommRing L] [Algebra k L]

/-- Évaluation en un vecteur `v` avec `vᵢ = 1` : `x / Xᵢ^m ↦ x(v)`. -/
def chartEval (i : Fin (n + 1)) (v : Fin (n + 1) → L) (hv : v i = 1) : Chart k n i →+* L :=
  (IsLocalization.Away.lift (S := Localization.Away (X i : MvPolynomial (Fin (n + 1)) k))
      (X i : MvPolynomial (Fin (n + 1)) k)
      (g := (aeval v : MvPolynomial (Fin (n + 1)) k →ₐ[k] L).toRingHom)
      (by simp [hv])).comp
    (algebraMap (Chart k n i) (Localization.Away (X i : MvPolynomial (Fin (n + 1)) k)))

theorem chartEval_ratio (i : Fin (n + 1)) (v : Fin (n + 1) → L) (hv : v i = 1) (j : Fin (n + 1)) :
    chartEval (k := k) i v hv (ratio i j) = v j := by
  simp [chartEval, ratio, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec, hv]

theorem chartEval_comp_base (i : Fin (n + 1)) (v : Fin (n + 1) → L) (hv : v i = 1) :
    (chartEval (k := k) i v hv).comp (chartBase k n i) = algebraMap k L := by
  ext c
  have h : val ((algebraMap (Grading k n 0) (Chart k n i)) ((algebraMap k (Grading k n 0)) c)) =
      algebraMap (MvPolynomial (Fin (n + 1)) k)
        (Localization.Away (X i : MvPolynomial (Fin (n + 1)) k)) (algebraMap k _ c) := by
    change Localization.mk ((algebraMap k (Grading k n 0) c : MvPolynomial (Fin (n + 1)) k)) 1 = _
    rw [Localization.mk_one_eq_algebraMap]
    rfl
  simp [chartEval, chartBase, h, IsLocalization.Away.lift_eq]

theorem ratio_self (i : Fin (n + 1)) : ratio (k := k) i i = 1 := by
  apply val_injective
  simp [ratio]

variable (k n L) in
/-- **Morphismes de la carte `D₊(Xᵢ)` vers `L`.** Un morphisme `𝒜_(Xᵢ) → L` compatible à `k`
équivaut au vecteur de ses valeurs sur les `Xⱼ / Xᵢ`, qui vaut `1` en `i`. -/
def awayHomEquiv (i : Fin (n + 1)) :
    {φ : Chart k n i →+* L // φ.comp (chartBase k n i) = algebraMap k L} ≃
      {v : Fin (n + 1) → L // v i = 1} where
  toFun φ := ⟨fun j ↦ φ.1 (ratio i j), by simp only [ratio_self, map_one]⟩
  invFun v := ⟨chartEval i v.1 v.2, chartEval_comp_base i v.1 v.2⟩
  left_inv φ := by
    have hv : (fun j ↦ φ.1 (ratio i j)) i = 1 := by simp only [ratio_self, map_one]
    exact Subtype.ext (chart_hom_ext (chartEval_comp_base i _ hv) φ.2 fun j ↦ chartEval_ratio i _ hv j)
  right_inv v := Subtype.ext <| funext fun j ↦ chartEval_ratio i v.1 v.2 j

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/ProjectivePoints.lean` -/

/-!
# Points de `ℙⁿ_k` à valeurs dans un corps, carte par carte (parties A3 et B2)

`projectiveSpace k n = Proj k[X₀, …, Xₙ]` (définition de la plateforme) est recouvert par les
cartes `D₊(Xᵢ)`, images des immersions ouvertes `chartι i : Spec 𝒜_(Xᵢ) ⟶ ℙⁿ`. Pour un corps `L`
qui est une `k`-algèbre :

* tout morphisme `Spec L ⟶ ℙⁿ` tombe dans une carte (`exists_forall_mem_basicOpen`) ;
* un point tombant dans `D₊(Xᵢ)` vient d'un unique morphisme `φ : 𝒜_(Xᵢ) →+* L`
  (`chartPoint`, `chartPoint_injective`, `exists_chartPoint`), et il est au-dessus de `k`
  exactement quand `φ` est compatible à `k` (`chartPoint_over_iff`) ;
* ce point est dans `D₊(Xⱼ)` si et seulement si `φ (Xⱼ / Xᵢ) ≠ 0`
  (`chartPoint_mem_basicOpen_iff`).

Avec `awayHomEquiv` (`Bridge/Chart.lean`), un point de la carte `i` est donc un vecteur `v` avec
`vᵢ = 1`, et il est dans `D₊(Xⱼ)` si et seulement si `vⱼ ≠ 0`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace WeilConjectures.Bridge

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type} [Field k] {n : ℕ}

/-! ## A3. Cartes et flèche structurale -/

variable (k n) in
/-- L'immersion ouverte de la carte `D₊(Xᵢ) ≅ Spec 𝒜_(Xᵢ)` dans `ℙⁿ_k`. -/
abbrev chartι (i : Fin (n + 1)) : Spec (.of (Chart k n i)) ⟶ projectiveSpace k n :=
  Proj.awayι (Grading k n) (X i) (X_mem_grading k n i) zero_lt_one

/-- Sur la carte `i`, la flèche structurale de la plateforme est `Spec` de `chartBase`. -/
theorem chartι_toSpec (i : Fin (n + 1)) :
    chartι k n i ≫ projectiveSpace.toSpec k n = Spec.map (CommRingCat.ofHom (chartBase k n i)) := by
  rw [projectiveSpace.toSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

variable (k n) in
/-- Les cartes `D₊(Xᵢ)` recouvrent `ℙⁿ_k`. -/
theorem iSup_basicOpen_X :
    ⨆ i, Proj.basicOpen (Grading k n) (X i : MvPolynomial (Fin (n + 1)) k) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i ↦ ⟨1, X_mem_grading k n i⟩
  · suffices h : ∀ p, p ∈ Algebra.adjoin (Grading k n 0)
        (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)) from
      eq_top_iff.mpr fun p _ ↦ h p
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact Subalgebra.algebraMap_mem _
        (⟨C a, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ a)⟩ : Grading k n 0)
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-! ## B2. Points dans une carte -/

variable {L : Type} [Field L]

/-- Le point de `ℙⁿ` à valeurs dans `L` défini par un morphisme de l'anneau de la carte `i`. -/
def chartPoint (i : Fin (n + 1)) (φ : Chart k n i →+* L) : Spec (.of L) ⟶ projectiveSpace k n :=
  Spec.map (CommRingCat.ofHom φ) ≫ chartι k n i

theorem chartPoint_toSpec (i : Fin (n + 1)) (φ : Chart k n i →+* L) :
    chartPoint i φ ≫ projectiveSpace.toSpec k n =
      Spec.map (CommRingCat.ofHom (φ.comp (chartBase k n i))) := by
  rw [chartPoint, Category.assoc, chartι_toSpec, ← Spec.map_comp]
  rfl

/-- Le point `chartPoint i φ` est au-dessus de `k` si et seulement si `φ` est compatible à `k`. -/
theorem chartPoint_over_iff [Algebra k L] (i : Fin (n + 1)) (φ : Chart k n i →+* L) :
    chartPoint i φ ≫ projectiveSpace.toSpec k n = Spec.map (CommRingCat.ofHom (algebraMap k L)) ↔
      φ.comp (chartBase k n i) = algebraMap k L := by
  rw [chartPoint_toSpec, Spec.map_inj]
  exact ⟨fun h ↦ by simpa using congrArg CommRingCat.Hom.hom h, fun h ↦ by rw [h]⟩

theorem chartPoint_injective (i : Fin (n + 1)) :
    Function.Injective (chartPoint (k := k) (L := L) i) := by
  intro φ ψ h
  rw [chartPoint, chartPoint, cancel_mono, Spec.map_inj] at h
  simpa using congrArg CommRingCat.Hom.hom h

/-- Un point dont l'image est dans `D₊(Xᵢ)` vient de la carte `i`. -/
theorem exists_chartPoint (x : Spec (.of L) ⟶ projectiveSpace k n) (i : Fin (n + 1))
    (hx : ∀ p, x.base p ∈ Proj.basicOpen (Grading k n) (X i : MvPolynomial (Fin (n + 1)) k)) :
    ∃ φ, chartPoint i φ = x := by
  have H : Set.range x.base ⊆ Set.range (chartι k n i).base := by
    rintro _ ⟨p, rfl⟩
    have := hx p
    rw [← Proj.opensRange_awayι (Grading k n) (X i) (X_mem_grading k n i) zero_lt_one] at this
    exact this
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift (chartι k n i) x H)
  exact ⟨ψ.hom, by rw [chartPoint, CommRingCat.ofHom_hom, hψ, IsOpenImmersion.lift_fac]⟩

/-- Tout point de `ℙⁿ` à valeurs dans un corps tombe dans une carte. -/
theorem exists_forall_mem_basicOpen (x : Spec (.of L) ⟶ projectiveSpace k n) :
    ∃ i, ∀ p, x.base p ∈ Proj.basicOpen (Grading k n) (X i : MvPolynomial (Fin (n + 1)) k) := by
  obtain ⟨p₀⟩ := (inferInstance : Nonempty (PrimeSpectrum L))
  have h : x.base p₀ ∈ (⊤ : (projectiveSpace k n).Opens) := trivial
  rw [← iSup_basicOpen_X k n, TopologicalSpace.Opens.mem_iSup] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun p ↦ by rwa [Subsingleton.elim p p₀]⟩

theorem ratio_eq_isLocalizationElem (i j : Fin (n + 1)) :
    ratio (k := k) i j = Away.isLocalizationElem (X_mem_grading k n i) (X_mem_grading k n j) := by
  apply val_injective
  simp [ratio]

/-- **Critère d'appartenance à une carte.** Le point de la carte `i` défini par `φ` est dans
`D₊(Xⱼ)` si et seulement si `φ (Xⱼ / Xᵢ) ≠ 0`. -/
theorem chartPoint_mem_basicOpen_iff (i j : Fin (n + 1)) (φ : Chart k n i →+* L)
    (p : Spec (.of L)) :
    (chartPoint i φ).base p ∈ Proj.basicOpen (Grading k n) (X j : MvPolynomial (Fin (n + 1)) k) ↔
      φ (ratio i j) ≠ 0 := by
  have hpre : chartPoint i φ ⁻¹ᵁ Proj.basicOpen (Grading k n) (X j) =
      PrimeSpectrum.basicOpen (φ (ratio i j)) := by
    rw [chartPoint, Scheme.Hom.comp_preimage,
      Proj.awayι_preimage_basicOpen (Grading k n) (X_mem_grading k n i) zero_lt_one
        (X_mem_grading k n j) zero_lt_one, ← ratio_eq_isLocalizationElem, SpecMap_preimage_basicOpen]
    rfl
  rw [← Scheme.Hom.mem_preimage, hpre]
  change φ (ratio i j) ∉ (p : PrimeSpectrum L).asIdeal ↔ _
  have hbot : (p : PrimeSpectrum L).asIdeal = ⊥ :=
    haveI := (p : PrimeSpectrum L).isPrime
    Ideal.eq_bot_of_prime _
  rw [hbot, Ideal.mem_bot]

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/ProjectiveCount.lean` -/

/-!
# Nombre de points de `ℙⁿ_k` à valeurs dans un corps fini (partie B3′)

On partitionne les points `Spec L ⟶ ℙⁿ_k` au-dessus de `k` selon la *première* carte `D₊(Xᵢ)`
qui les contient. Les points de première carte `i` sont en bijection avec les vecteurs
`v : Fin (n+1) → L` tels que `vᵢ = 1` et `vⱼ = 0` pour `j < i` (`projectivePointsEquiv`), et il y
en a `#L ^ (n - i)`. D'où

`#ℙⁿ(L) = ∑_{i ≤ n} #L ^ (n - i) = ∑_{i ≤ n} #L ^ i`  (`natCard_projectivePoints`).

On évite ainsi le quotient par les scalaires : seules servent la description d'une carte
(`awayHomEquiv`, `exists_chartPoint`) et le critère d'appartenance `chartPoint_mem_basicOpen_iff`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace WeilConjectures.Bridge

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type} [Field k] {n : ℕ} {L : Type} [Field L] [Algebra k L]

variable (k n L) in
/-- Les points de `ℙⁿ_k` à valeurs dans `L`, au-dessus de `k` (le sous-type de `pointsOver`). -/
abbrev ProjectivePoints : Type :=
  {x : Spec (.of L) ⟶ projectiveSpace k n //
    x ≫ projectiveSpace.toSpec k n = Spec.map (CommRingCat.ofHom (algebraMap k L))}

variable (n L) in
/-- Les vecteurs normalisés de « première coordonnée non nulle » `i` : `vᵢ = 1`, `vⱼ = 0` pour
`j < i`. -/
abbrev NormalizedVectors (i : Fin (n + 1)) : Type :=
  {v : Fin (n + 1) → L // v i = 1 ∧ ∀ j, j < i → v j = 0}

/-- Le point de `ℙⁿ` associé à un vecteur normalisé, via la carte `i`. -/
def pointOfVector (iv : Σ i : Fin (n + 1), NormalizedVectors n L i) : ProjectivePoints k n L :=
  ⟨chartPoint iv.1 (chartEval iv.1 iv.2.1 iv.2.2.1),
    (chartPoint_over_iff _ _).mpr (chartEval_comp_base _ _ _)⟩

/-- Le point associé à `⟨i, v⟩` est dans `D₊(Xⱼ)` si et seulement si `vⱼ ≠ 0`. -/
theorem pointOfVector_mem_iff (iv : Σ i : Fin (n + 1), NormalizedVectors n L i) (j : Fin (n + 1))
    (p : Spec (.of L)) :
    (pointOfVector (k := k) iv).1.base p ∈
        Proj.basicOpen (Grading k n) (X j : MvPolynomial (Fin (n + 1)) k) ↔ iv.2.1 j ≠ 0 := by
  rw [pointOfVector, chartPoint_mem_basicOpen_iff, chartEval_ratio]

/-- L'indice `i` est l'unique indice de carte contenant le point, sans carte antérieure. -/
theorem pointOfVector_first (iv : Σ i : Fin (n + 1), NormalizedVectors n L i) (p : Spec (.of L)) :
    (pointOfVector (k := k) iv).1.base p ∈
        Proj.basicOpen (Grading k n) (X iv.1 : MvPolynomial (Fin (n + 1)) k) ∧
      ∀ j < iv.1, (pointOfVector (k := k) iv).1.base p ∉
        Proj.basicOpen (Grading k n) (X j : MvPolynomial (Fin (n + 1)) k) := by
  refine ⟨(pointOfVector_mem_iff iv _ p).mpr (by simp [iv.2.2.1]), fun j hj ↦ ?_⟩
  rw [pointOfVector_mem_iff, not_not]
  exact iv.2.2.2 j hj

theorem pointOfVector_injective :
    Function.Injective (pointOfVector (k := k) (n := n) (L := L)) := by
  rintro ⟨i, v⟩ ⟨i', v'⟩ h
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum L))
  have hi : i = i' := by
    have h1 := pointOfVector_first (k := k) ⟨i, v⟩ p
    have h2 := pointOfVector_first (k := k) ⟨i', v'⟩ p
    rw [h] at h1
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact absurd h1.1 (h2.2 i hlt)
    · exact heq
    · exact absurd h2.1 (h1.2 i' hgt)
  subst hi
  have hφ := chartPoint_injective i (congrArg Subtype.val h)
  have hv : v.1 = v'.1 := funext fun j ↦ by
    rw [← chartEval_ratio (k := k) i v.1 v.2.1 j, hφ, chartEval_ratio]
  rw [Subtype.ext hv]

theorem pointOfVector_surjective :
    Function.Surjective (pointOfVector (k := k) (n := n) (L := L)) := by
  classical
  rintro ⟨x, hx⟩
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum L))
  have hex : ∃ i, ∀ q, x.base q ∈ Proj.basicOpen (Grading k n) (X i : MvPolynomial _ k) :=
    exists_forall_mem_basicOpen x
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun i ↦
    ∀ q, x.base q ∈ Proj.basicOpen (Grading k n) (X i : MvPolynomial (Fin (n + 1)) k)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := S.min' hS
  have hi : ∀ q, x.base q ∈ Proj.basicOpen (Grading k n) (X i : MvPolynomial _ k) := by
    exact (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hmin : ∀ j < i, ¬ ∀ q, x.base q ∈ Proj.basicOpen (Grading k n) (X j : MvPolynomial _ k) :=
    fun j hj hjx ↦ (S.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjx⟩)).not_gt hj
  obtain ⟨φ, hφx⟩ := exists_chartPoint x i hi
  have hcomp : φ.comp (chartBase k n i) = algebraMap k L :=
    (chartPoint_over_iff i φ).mp (hφx ▸ hx)
  let v := awayHomEquiv k n L i ⟨φ, hcomp⟩
  have hφ : chartEval i v.1 v.2 = φ :=
    congrArg Subtype.val ((awayHomEquiv k n L i).left_inv ⟨φ, hcomp⟩)
  refine ⟨⟨i, v.1, v.2, fun j hj ↦ ?_⟩, Subtype.ext ?_⟩
  · by_contra hne
    refine hmin j hj fun q ↦ ?_
    rw [← hφx]
    exact (chartPoint_mem_basicOpen_iff i j φ q).mpr hne
  · simp only [pointOfVector]
    rw [hφ, hφx]

variable (k n L) in
/-- **Paramétrage des points de `ℙⁿ(L)`** par la première carte et un vecteur normalisé. -/
def projectivePointsEquiv :
    (Σ i : Fin (n + 1), NormalizedVectors n L i) ≃ ProjectivePoints k n L :=
  Equiv.ofBijective _ ⟨pointOfVector_injective, pointOfVector_surjective⟩

variable (n L) in
/-- Un vecteur normalisé de première coordonnée `i` est la donnée libre de ses coordonnées
d'indice `> i`. -/
def normalizedVectorsEquiv (i : Fin (n + 1)) :
    NormalizedVectors n L i ≃ ({j : Fin (n + 1) // i < j} → L) where
  toFun v j := v.1 j.1
  invFun w := ⟨fun j ↦ if h : i < j then w ⟨j, h⟩ else if j = i then 1 else 0,
    by simp, fun j hj ↦ by simp [hj.not_gt, hj.ne]⟩
  left_inv v := by
    ext j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h]
    · simp [v.2.1]
    · simp [h.not_gt, h.ne, v.2.2 j h]
  right_inv w := by
    funext j
    simp [j.2]

theorem natCard_normalizedVectors [Finite L] (i : Fin (n + 1)) :
    Nat.card (NormalizedVectors n L i) = Nat.card L ^ (n - i) := by
  rw [Nat.card_congr (normalizedVectorsEquiv n L i), Nat.card_fun]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  omega

/-- **Nombre de points de `ℙⁿ` à valeurs dans un corps fini `L`.** -/
theorem natCard_projectivePoints [Finite L] :
    Nat.card (ProjectivePoints k n L) = ∑ i ∈ Finset.range (n + 1), Nat.card L ^ i := by
  rw [← Nat.card_congr (projectivePointsEquiv k n L), Nat.card_sigma]
  simp_rw [natCard_normalizedVectors]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ Nat.card L ^ (n - i)), ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  congr 1
  omega

end WeilConjectures.Bridge

end

/-! ## Recopié de `Bridge/ProjectiveSpaceZeta.lean` -/

section

/-!
# `projectiveSpace_zeta` (parties B4 à B6)

* B4 : `N_m(ℙⁿ) = ∑_{i ≤ n} q^{i m}`, par `natCard_projectivePoints` appliqué à
  `L = 𝔽_{q^m} = FiniteField.Extension k p m`, de cardinal `q^m`.
* B5 : la série zêta est donc celle d'une somme de comptages géométriques `m ↦ (qⁱ)^m`, produit
  des `(1 - qⁱ T)⁻¹` (`zetaOfCounts_sum`, `zetaOfCounts_pow_mul`).

Le fichier soumissible `Solutions/Sol_projectiveSpace_zeta.lean` est engendré à partir de la
bibliothèque `Bridge` par `scripts/assemble_projectiveSpace_zeta.py`.
-/

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

namespace WeilConjectures.Bridge

theorem projectiveSpace_zeta_proof (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) :
    (∀ m : ℕ, 1 ≤ m →
      pointCount p (projectiveSpace.toSpec k n) m = ∑ i ∈ Finset.range (n + 1), Nat.card k ^ (i * m)) ∧
    zetaFunction p (projectiveSpace.toSpec k n) *
      ∏ i ∈ Finset.range (n + 1), (1 - PowerSeries.C ((Nat.card k : ℚ) ^ i) * PowerSeries.X) = 1 := by
  -- B4 : le comptage
  have hcount : ∀ m : ℕ, 1 ≤ m →
      pointCount p (projectiveSpace.toSpec k n) m =
        ∑ i ∈ Finset.range (n + 1), Nat.card k ^ (i * m) := by
    intro m hm
    have : NeZero m := ⟨by omega⟩
    rw [Bridge.pointCount_of_neZero]
    change Nat.card (Bridge.ProjectivePoints k n (FiniteField.Extension k p m)) = _
    rw [Bridge.natCard_projectivePoints, FiniteField.natCard_extension]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← pow_mul, mul_comm]
  refine ⟨hcount, ?_⟩
  -- B5 : la fonction zêta
  have hcongr : zetaOfCounts (pointCount p (projectiveSpace.toSpec k n)) =
      zetaOfCounts (∑ i ∈ Finset.range (n + 1), fun m ↦ (Nat.card k ^ i) ^ m) := by
    refine Bridge.zetaOfCounts_congr fun m hm ↦ ?_
    rw [hcount m hm, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← pow_mul]
  rw [Bridge.zetaFunction_eq, hcongr, Bridge.zetaOfCounts_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ ↦ ?_
  have h := Bridge.zetaOfCounts_pow_mul (Nat.card k ^ i)
  push_cast at h
  exact h

end WeilConjectures.Bridge

end

/-! ## La solution (énoncé recopié tel quel de la plateforme) -/

open AlgebraicGeometry CategoryTheory Polynomial
open WeilConjectures

theorem solution (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Finite k] [CharP k p] (n : ℕ) :
    (∀ m : ℕ, 1 ≤ m →
      pointCount p (projectiveSpace.toSpec k n) m = ∑ i ∈ Finset.range (n + 1), Nat.card k ^ (i * m)) ∧
    zetaFunction p (projectiveSpace.toSpec k n) *
      ∏ i ∈ Finset.range (n + 1), (1 - PowerSeries.C ((Nat.card k : ℚ) ^ i) * PowerSeries.X) = 1 :=
  WeilConjectures.Bridge.projectiveSpace_zeta_proof p k n
