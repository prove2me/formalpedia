-- Prove2me | solution 1 for PhilipponMultiplicity.masser_wustholz_terminal_retained_cut
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T08:04:31.73516+00:00
-- url     : https://prove2.me/submissions/3479ae64-62b0-4056-b41b-b23205231a46

import Theorems.Thm_PhilipponMultiplicity_connected_projective_closure_degree_bound
import Definitions.Def_P2M_Util
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_HilbertGrowth
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Mathlib
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.KrullDimension

section
-- Reused implementation: Solutions.PhilipponHypersurfaceHeight

set_option autoImplicit false

/-- In a Noetherian ring, a component of a principal cut of a prime has
relative height exactly one, provided the equation is outside that prime. -/
theorem Ideal.height_map_quotient_eq_one_of_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (x : R) (hx : x ∉ p)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    (q.map (Ideal.Quotient.mk p)).height = 1 := by
  let : p.IsPrime := hp
  apply le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hq)
  rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro heq
  have hspan : Ideal.span {x} ≤ q := le_sup_right.trans hq.le
  have hxq : x ∈ q := hspan (Ideal.subset_span (Set.mem_singleton x))
  have hmem := Ideal.mem_map_of_mem (Ideal.Quotient.mk p) hxq
  rw [heq, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hx hmem

end


section
-- Reused implementation: Solutions.PolynomialFiltrationGrowth

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PolynomialGrowth
variable {K σ τ A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The actual image of the total-degree subspace under an algebra map. -/
def filtration (f : MvPolynomial σ K →ₐ[K] A) (n : ℕ) : Submodule K A :=
  (restrictTotalDegree σ K n).map f.toLinearMap

instance filtration_finite [Finite σ] (f : MvPolynomial σ K →ₐ[K] A) (n : ℕ) :
    Module.Finite K (filtration f n) := by
  unfold filtration
  infer_instance

theorem filtration_mono (f : MvPolynomial σ K →ₐ[K] A) : Monotone (filtration f) := by
  intro m n hmn
  apply Submodule.map_mono
  intro P hP
  exact (mem_restrictTotalDegree σ n P).mpr (((mem_restrictTotalDegree σ m P).mp hP).trans hmn)

theorem filtration_mul_mem (f : MvPolynomial σ K →ₐ[K] A) {m n : ℕ} {x y : A}
    (hx : x ∈ filtration f m) (hy : y ∈ filtration f n) : x * y ∈ filtration f (m + n) := by
  obtain ⟨P, hP, rfl⟩ := hx
  obtain ⟨Q, hQ, rfl⟩ := hy
  refine ⟨P * Q, ?_, map_mul f P Q⟩
  exact (mem_restrictTotalDegree σ (m + n) _).mpr
    ((totalDegree_mul P Q).trans (Nat.add_le_add
      ((mem_restrictTotalDegree σ m P).mp hP) ((mem_restrictTotalDegree σ n Q).mp hQ)))

theorem totalDegree_aeval_le [Fintype τ] (v : τ → MvPolynomial σ K)
    (L : ℕ) (hv : ∀ i, (v i).totalDegree ≤ L) (P : MvPolynomial τ K) :
    (aeval v P).totalDegree ≤ L * P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro e he
  rw [aeval_monomial]
  have hp : (∏ i, v i ^ e i).totalDegree ≤ L * e.degree := by
    calc
      _ ≤ ∑ i, (v i ^ e i).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ i, e i * L := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hv i))
      _ = L * e.degree := by rw [← Finset.sum_mul, Finsupp.degree_eq_sum, Nat.mul_comm]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact ((totalDegree_mul _ _).trans (by
    simpa [Finsupp.degree_apply, Finsupp.sum] using hp)).trans
    (Nat.mul_le_mul_left L (le_totalDegree he))

/-- Degree boxes have exactly the expected number of monomials. -/
theorem finrank_restrictDegree [Fintype σ] (n : ℕ) :
    Module.finrank K (restrictDegree σ K n) = (n + 1) ^ Fintype.card σ := by
  classical
  let S := {e : σ →₀ ℕ // ∀ i, e i ≤ n}
  let E : S ≃ (σ → Fin (n + 1)) :=
    { toFun := fun e i => ⟨e.1 i, Nat.lt_succ_of_le (e.2 i)⟩
      invFun := fun d => ⟨Finsupp.equivFunOnFinite.symm (fun i => (d i).val),
        fun i => Nat.le_of_lt_succ (d i).isLt⟩
      left_inv := fun e => by apply Subtype.ext; ext i; rfl
      right_inv := fun d => by funext i; apply Fin.ext; rfl }
  change Module.finrank K (restrictSupport K {e : σ →₀ ℕ | ∀ i, e i ≤ n}) = _
  exact (Module.finrank_eq_card_basis ((basisRestrictSupport K _).reindex E)).trans (by simp)

theorem finrank_restrictTotalDegree_le [Fintype σ] (n : ℕ) :
    Module.finrank K (restrictTotalDegree σ K n) ≤ (n + 1) ^ Fintype.card σ := by
  rw [← finrank_restrictDegree (K := K)]
  exact Submodule.finrank_mono (restrictTotalDegree_le_restrictDegree σ K n)

theorem restrictDegree_le_restrictTotalDegree [Fintype σ] (n : ℕ) :
    restrictDegree σ K n ≤ restrictTotalDegree σ K (Fintype.card σ * n) := by
  classical
  intro P hP
  apply (mem_restrictTotalDegree σ _ P).mpr
  rw [totalDegree, Finset.sup_le_iff]
  intro e he
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (mem_restrictDegree σ P n).mp hP e he i)
  simpa [Finsupp.sum, ← Finsupp.degree_eq_sum, Finsupp.degree_apply] using h

/-- Algebraically independent normalization monomials give a lower bound
in the original coordinate filtration. -/
theorem filtration_lower_of_injective [Fintype σ] [Fintype τ]
    (f : MvPolynomial σ K →ₐ[K] A) (hf : Function.Surjective f)
    (g : MvPolynomial τ K →ₐ[K] A) (hg : Function.Injective g) :
    ∃ L : ℕ, 0 < L ∧ ∀ n : ℕ, (n + 1) ^ Fintype.card τ ≤
      Module.finrank K (filtration f (L * n)) := by
  classical
  choose v hv using fun i : τ => hf (g (X i))
  let D := Finset.univ.sup (fun i => (v i).totalDegree)
  have hD (i : τ) : (v i).totalDegree ≤ D :=
    Finset.le_sup (f := fun i => (v i).totalDegree) (Finset.mem_univ i)
  have hcomp : f.comp (aeval v) = g := by
    ext i
    simpa using hv i
  refine ⟨D * Fintype.card τ + 1, by omega, fun n => ?_⟩
  have hmap (P : restrictDegree τ K n) : g P.val ∈ filtration f ((D * Fintype.card τ + 1) * n) := by
    refine ⟨aeval v P.val, ?_, ?_⟩
    · apply (mem_restrictTotalDegree σ _ _).mpr
      calc
        (aeval v P.val).totalDegree ≤ D * P.val.totalDegree := totalDegree_aeval_le v D hD _
        _ ≤ D * (Fintype.card τ * n) := Nat.mul_le_mul_left D
          ((mem_restrictTotalDegree τ _ _).mp (restrictDegree_le_restrictTotalDegree n P.property))
        _ ≤ (D * Fintype.card τ + 1) * n := by nlinarith
    · exact congrArg (fun h : MvPolynomial τ K →ₐ[K] A => h P.val) hcomp
  let l : restrictDegree τ K n →ₗ[K] filtration f ((D * Fintype.card τ + 1) * n) :=
    (g.toLinearMap.domRestrict _).codRestrict _ hmap
  have hl : Function.Injective l := by
    intro P Q hpq
    apply Subtype.ext
    exact hg (congrArg Subtype.val hpq)
  have h := LinearMap.finrank_le_finrank_of_injective hl
  rwa [finrank_restrictDegree] at h

end PolynomialGrowth

end
end


section
-- Reused implementation: Solutions.FiniteModuleFiltrationGrowth

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PolynomialGrowth
variable {K σ τ A ι : Type*} [Field K] [CommRing A] [Algebra K A]
variable [Fintype ι]

def coefficientMap (g : MvPolynomial τ K →ₐ[K] A) (u : ι → A) (n : ℕ) :
    (ι → restrictTotalDegree τ K n) →ₗ[K] A where
  toFun := fun v => ∑ j, g (v j).val * u j
  map_add' v w := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by simp [map_smul, smul_mul_assoc, Finset.smul_sum]

def moduleFiltration (g : MvPolynomial τ K →ₐ[K] A) (u : ι → A) (n : ℕ) : Submodule K A :=
  LinearMap.range (coefficientMap g u n)

instance moduleFiltration_finite [Finite τ]
    (g : MvPolynomial τ K →ₐ[K] A) (u : ι → A) (n : ℕ) :
    Module.Finite K (moduleFiltration g u n) := by
  unfold moduleFiltration
  infer_instance

theorem moduleFiltration_mono (g : MvPolynomial τ K →ₐ[K] A) (u : ι → A) :
    Monotone (moduleFiltration g u) := by
  intro m n hmn x hx
  obtain ⟨v, rfl⟩ := hx
  refine ⟨fun j => ⟨(v j).val, ?_⟩, rfl⟩
  exact (mem_restrictTotalDegree τ n _).mpr
    (((mem_restrictTotalDegree τ m _).mp (v j).property).trans hmn)

theorem finrank_moduleFiltration_le [Fintype τ]
    (g : MvPolynomial τ K →ₐ[K] A) (u : ι → A) (n : ℕ) :
    Module.finrank K (moduleFiltration g u n) ≤
      Fintype.card ι * (n + 1) ^ Fintype.card τ := by
  calc
    _ ≤ Module.finrank K (ι → restrictTotalDegree τ K n) :=
      (coefficientMap g u n).finrank_range_le
    _ = Fintype.card ι * Module.finrank K (restrictTotalDegree τ K n) := by
      rw [Module.finrank_pi_fintype]; simp
    _ ≤ _ := Nat.mul_le_mul_left _ (finrank_restrictTotalDegree_le n)

theorem moduleFiltration_mul_generator
    (f : MvPolynomial σ K →ₐ[K] A) (g : MvPolynomial τ K →ₐ[K] A)
    (u : ι → A) (b : σ → ι → ι → MvPolynomial τ K) (D : ℕ)
    (hb : ∀ i j, ∑ k, g (b i j k) * u k = f (X i) * u j)
    (hD : ∀ i j k, (b i j k).totalDegree ≤ D)
    (i : σ) (n : ℕ) {x : A} (hx : x ∈ moduleFiltration g u n) :
    f (X i) * x ∈ moduleFiltration g u (n + D) := by
  classical
  obtain ⟨v, rfl⟩ := hx
  let w : ι → restrictTotalDegree τ K (n + D) := fun k =>
    ⟨∑ j, (v j).val * b i j k, (mem_restrictTotalDegree τ _ _).mpr (by
      apply (totalDegree_finsetSum _ _).trans
      apply Finset.sup_le
      intro j hj
      exact (totalDegree_mul _ _).trans (Nat.add_le_add
        ((mem_restrictTotalDegree τ n _).mp (v j).property) (hD i j k)))⟩
  refine ⟨w, ?_⟩
  change (∑ k, g (∑ j, (v j).val * b i j k) * u k) =
    f (X i) * ∑ j, g (v j).val * u j
  simp_rw [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ k, (g (v j).val * g (b i j k)) * u k) =
        g (v j).val * ∑ k, g (b i j k) * u k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = f (X i) * (g (v j).val * u j) := by rw [hb i j]; ring

/-- A finite polynomial-module presentation provides polynomial upper growth
for every original finite coordinate system. -/
theorem filtration_upper_of_finite [Fintype σ] [Fintype τ]
    (f : MvPolynomial σ K →ₐ[K] A)
    (g : MvPolynomial τ K →ₐ[K] A) (hg : g.Finite) :
    ∃ t E D : ℕ, ∀ n : ℕ, Module.finrank K (filtration f n) ≤
      t * (E + D * n + 1) ^ Fintype.card τ := by
  classical
  let B := MvPolynomial τ K
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : Module.Finite B A := hg
  obtain ⟨t, u, hu⟩ := Module.Finite.exists_fin (R := B) (M := A)
  have repr (x : A) : ∃ v : Fin t → B, ∑ j, g (v j) * u j = x := by
    obtain ⟨v, hv⟩ := (span_range_eq_top_iff_surjective_fintypeLinearCombination B u).mp hu x
    simp only [Fintype.linearCombination_apply, Algebra.smul_def] at hv
    change (∑ j, g (v j) * u j) = x at hv
    exact ⟨v, hv⟩
  obtain ⟨v₀, hv₀⟩ := repr 1
  choose b hb using fun (i : σ) (j : Fin t) => repr (f (X i) * u j)
  let E := Finset.univ.sup (fun j => (v₀ j).totalDegree)
  let D := Finset.univ.sup (fun ijk : σ × Fin t × Fin t => (b ijk.1 ijk.2.1 ijk.2.2).totalDegree)
  have hE (j : Fin t) : (v₀ j).totalDegree ≤ E :=
    Finset.le_sup (f := fun j => (v₀ j).totalDegree) (Finset.mem_univ j)
  have hD (i : σ) (j k : Fin t) : (b i j k).totalDegree ≤ D :=
    Finset.le_sup (f := fun ijk : σ × Fin t × Fin t =>
      (b ijk.1 ijk.2.1 ijk.2.2).totalDegree) (Finset.mem_univ (i, j, k))
  have hone : (1 : A) ∈ moduleFiltration g u E := by
    refine ⟨fun j => ⟨v₀ j, (mem_restrictTotalDegree τ E _).mpr (hE j)⟩, hv₀⟩
  have hmon (e : σ →₀ ℕ) : f (monomial e 1) ∈ moduleFiltration g u (E + D * e.degree) := by
    induction e using Finsupp.induction with
    | zero => simpa using hone
    | @single_add i k e hi hk ih =>
      have hpow : ∀ k : ℕ, f (monomial e 1 * X i ^ k) ∈
          moduleFiltration g u (E + D * (e.degree + k)) := by
        intro k
        induction k with
        | zero => simpa using ih
        | succ k hrec =>
          have h := moduleFiltration_mul_generator f g u b D hb hD i _ hrec
          convert h using 1 <;> simp [pow_succ, map_mul, Nat.mul_add] <;> ring
      simp only [map_add, Finsupp.degree_single]
      rw [add_comm (Finsupp.single i k) e, monomial_add_single]
      simpa only [Nat.add_comm] using hpow k
  have hle (n : ℕ) : filtration f n ≤ moduleFiltration g u (E + D * n) := by
    rintro x ⟨P, hP, rfl⟩
    rw [P.as_sum, map_sum]
    apply Submodule.sum_mem
    intro e he
    have h := moduleFiltration_mono g u
      (Nat.add_le_add_left (Nat.mul_le_mul_left D
        ((le_totalDegree he).trans ((mem_restrictTotalDegree σ n P).mp hP))) E) (hmon e)
    have hs := (moduleFiltration g u (E + D * n)).smul_mem (coeff e P) h
    change f (monomial e (coeff e P)) ∈ _
    simpa only [← map_smul, smul_monomial, smul_eq_mul, mul_one] using hs
  refine ⟨t, E, D, fun n => ?_⟩
  exact (Submodule.finrank_mono (hle n)).trans (by
    simpa using finrank_moduleFiltration_le g u (E + D * n))

end PolynomialGrowth

end
end


section
-- Reused implementation: Solutions.NoetherIntegralDimension

/-! Reused integral-extension dimension proof from the accepted public altitude
source, submission 9f4900bf-796d-5f87-b671-c949b384b42f. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace PolynomialGrowth.IntegralDimension

private lemma NoetherIntegralDimension_exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := NoetherIntegralDimension_exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)


end PolynomialGrowth.IntegralDimension

end


section
-- Reused implementation: Solutions.NoetherNormalizationFiltration

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PolynomialGrowth
variable {K σ A : Type*} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]

/-- Noether normalization controls the actual filtration for any finite set
of algebra generators, with exponent equal to prime-chain Krull dimension. -/
theorem normalization_filtration_bounds [Fintype σ] [Algebra.FiniteType K A]
    (f : MvPolynomial σ K →ₐ[K] A) (hf : Function.Surjective f) :
    ∃ r L : ℕ, 0 < L ∧ ringKrullDim A = ((r : ℕ) : WithBot ℕ∞) ∧
      ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
        c * (n : ℚ) ^ r ≤ (Module.finrank K (filtration f (L * n)) : ℚ) ∧
        (Module.finrank K (filtration f n) : ℚ) ≤ C * ((n + 1 : ℕ) : ℚ) ^ r := by
  obtain ⟨r, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  have hdim : ringKrullDim A = ((r : ℕ) : WithBot ℕ∞) := by
    letI : Algebra (MvPolynomial (Fin r) K) A := g.toRingHom.toAlgebra
    letI : Algebra.IsIntegral (MvPolynomial (Fin r) K) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
    have h :=
      IntegralDimension.ringKrullDim_eq_of_isIntegral_of_injective
        (R := MvPolynomial (Fin r) K) (S := A) hg
    rw [← h, MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨L, hL, hlo⟩ := filtration_lower_of_injective f hf g hg
  obtain ⟨t, E, D, hhi⟩ := filtration_upper_of_finite f g hfin
  refine ⟨r, L, hL, hdim, 1, ((t + 1) * (E + D + 1) ^ r : ℕ), by norm_num,
    by positivity, fun n => ?_⟩
  constructor
  · rw [one_mul]
    exact_mod_cast (show n ^ r ≤ Module.finrank K (filtration f (L * n)) from
      (Nat.pow_le_pow_left (Nat.le_succ n) r).trans (by simpa using hlo n))
  · have hscale : E + D * n + 1 ≤ (E + D + 1) * (n + 1) := by nlinarith
    have hbound : Module.finrank K (filtration f n) ≤
        ((t + 1) * (E + D + 1) ^ r) * (n + 1) ^ r := by
      calc
        _ ≤ t * (E + D * n + 1) ^ r := by simpa using hhi n
        _ ≤ (t + 1) * ((E + D + 1) * (n + 1)) ^ r :=
          Nat.mul_le_mul (Nat.le_succ t) (Nat.pow_le_pow_left hscale r)
        _ = _ := by rw [mul_pow]; ring
    exact_mod_cast hbound

end PolynomialGrowth

end
end


section
-- Reused implementation: Solutions.PhilipponProjectiveGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isClosed_zero {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    @IsClosed _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | MvPolynomial.eval p.rep P = 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isClosed_zero _ _
    (singleBlock_isHomogeneous hP)).preimage hcont
  convert h using 1
  ext p
  change MvPolynomial.eval p.rep P = 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => p) = 0
  simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
  rfl

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

theorem projective_extension_locallyClosed (g₂ g₃ : ℂ) :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p _ => p) (projectiveSpace ℂ 4).zariskiTopology)
      {p : Projectivization ℂ (Fin 5 → ℂ) |
        MvPolynomial.eval p.rep extensionQuadric = 0 ∧
        MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
        (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)} := by
  letI := TopologicalSpace.induced (fun (p : Projectivization ℂ (Fin 5 → ℂ)) =>
    (fun _ => p : (projectiveSpace ℂ 4).Point)) (projectiveSpace ℂ 4).zariskiTopology
  have hq : extensionQuadric.IsHomogeneous 2 := by
    exact ((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X ℂ 4)).sub
      ((MvPolynomial.isHomogeneous_X ℂ 2).mul (MvPolynomial.isHomogeneous_X ℂ 3)) |>.sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow 2 1 2)
  have hc : (extensionCubic g₂ g₃).IsHomogeneous 3 := by
    exact (((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X_pow 2 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((MvPolynomial.isHomogeneous_C_mul_X_pow g₂ 0 2).mul
          (MvPolynomial.isHomogeneous_X ℂ 1)) |>.add
        (MvPolynomial.isHomogeneous_C_mul_X_pow g₃ 0 3)
  convert
    ((projective_isClosed_zero hq).inter (projective_isClosed_zero hc)).isLocallyClosed.inter
      ((projective_isOpen_coordinate (K := ℂ) (0 : Fin 5)).union
        (projective_isOpen_coordinate (K := ℂ) (2 : Fin 5))).isLocallyClosed using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, and_assoc]

theorem projective_extension_fiber_action_regular (g₂ g₃ u : ℂ)
    (F : ProjectiveExtensionFiberModel g₂ g₃) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => extensionProjectivePoint p)
      (fun p => fun _ => extensionProjectivePoint (F.action u p)) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3 + MvPolynomial.C u * MvPolynomial.X 0,
      MvPolynomial.X 4 + MvPolynomial.C u * MvPolynomial.X 2]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 0))
    · exact (MvPolynomial.isHomogeneous_X ℂ 4).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 2))
  · intro p
    have heq : (fun j => MvPolynomial.eval (extensionProjectivePoint p).rep (P j)) =
        extensionFiberShear u (extensionProjectivePoint p).rep := by
      ext j
      fin_cases j <;> simp [P, extensionFiberShear]
    obtain ⟨h, hh⟩ := F.action_coords u p
    exact ⟨by simpa only [heq] using h, by simpa only [heq] using hh.symm⟩

end WeierstrassEllipticZeta
end
end


section
-- Reused implementation: Solutions.PhilipponPointHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i

theorem exists_form_nonzero_at (p : M.Point) (D : M.FactorIndex → ℕ) :
    ∃ Q : M.CoordinateRing, M.IsHomogeneous Q D ∧ M.eval Q p ≠ 0 := by
  classical
  have hj (i : M.FactorIndex) : ∃ j, (p i).rep j ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using
      (Projectivization.rep_nonzero (p i))
  choose j hj using hj
  let d : M.Variable →₀ ℕ := Finsupp.equivFunOnFinite.symm
    (fun v => if v.2 = j v.1 then D v.1 else 0)
  refine ⟨monomial d 1, ?_, ?_⟩
  · intro m hm i
    have hm' : m = d := Finset.mem_singleton.mp (support_monomial_subset hm)
    subst m
    simp [d]
  · change MvPolynomial.eval (M.coordinate p) (monomial d 1) ≠ 0
    rw [eval_monomial]
    simp only [one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    dsimp [d]
    split_ifs with h
    · apply pow_ne_zero
      change (p v.1).rep v.2 ≠ 0
      rw [h]
      exact hj v.1
    · simp

/-- The genuine multigraded quotient Hilbert function of a projective point is one. -/
theorem hilbertFunction_singleton (p : M.Point) (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) D = 1 := by
  classical
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal {p}
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := (aeval (M.coordinate p) : M.CoordinateRing →ₐ[K] K).toLinearMap.domRestrict V
  have hker : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ M.eval P.val p = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro h
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_singleton p)
    · intro h
      apply Ideal.subset_span
      refine ⟨⟨D, (M.degreePiece_iff P.val D).mp P.property⟩, ?_⟩
      rintro x rfl
      exact h
  obtain ⟨Q, hQ, hQp⟩ := M.exists_form_nonzero_at p D
  have hQg : Q ∈ V := (M.degreePiece_iff Q D).mpr hQ
  have hg : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr (by
    intro c
    refine ⟨⟨(c / M.eval Q p) • Q, V.smul_mem _ hQg⟩, ?_⟩
    change MvPolynomial.eval (M.coordinate p) ((c / M.eval Q p) • Q) = c
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
    change (c / M.eval Q p) * M.eval Q p = c
    exact div_mul_cancel₀ _ hQp)
  let E := f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)
  have hdim := E.finrank_eq
  have hf : LinearMap.range f = Hilbert.quotientPiece K M.factorCount M.ambientDimension I D := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  rw [hf, hg, finrank_top, Module.finrank_self] at hdim
  exact hdim

theorem hilbertPolynomial_singleton (p : M.Point) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) = 1 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro D _
  rw [M.hilbertFunction_singleton]
  simp

theorem degreeValue_singleton (p : M.Point) (D : M.FactorIndex → ℕ) :
    Hilbert.degreeValue K M.factorCount M.ambientDimension (M.vanishingIdeal {p}) D = 1 := by
  simp [Hilbert.degreeValue, Hilbert.degreeForm, M.hilbertPolynomial_singleton]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
theorem hilbertDegreeForm_singleton {K : Type*} [Field K]
    (G : EmbeddedGroupProduct K) (x : G.Point) (D : G.FactorIndex → ℕ) :
    hilbertDegreeForm G {x} D = 1 := by
  unfold hilbertDegreeForm EmbeddedGroupProduct.vanishingIdeal
  rw [Set.image_singleton]
  exact_mod_cast G.ambient.degreeValue_singleton (G.embedding x) D
end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponAnalyticUnitOrder

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Multiplication preserves a vanishing finite jet. -/
theorem iteratedFDeriv_mul_eq_zero_of_vanishing_jet
    {f u : E → K} {x : E} {n : ℕ}
    (hf : ContDiffAt K n f x) (hu : ContDiffAt K n u x)
    (hz : ∀ i ≤ n, iteratedFDeriv K i f x = 0) :
    iteratedFDeriv K n (fun y => u y * f y) x = 0 := by
  obtain ⟨s, hs, hopen, hxs⟩ := eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and (hu.eventually (by simp)))
  have hfs : ContDiffOn K n f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have hus : ContDiffOn K n u s := fun y hy => (hs y hy).2.contDiffWithinAt
  have hbound := norm_iteratedFDerivWithin_mul_le hus hfs hopen.uniqueDiffOn hxs
    (le_refl (n : ℕ∞ω))
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hxs] at hbound
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv K i u x‖ * ‖iteratedFDeriv K (n - i) f x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz (n - i) (Nat.sub_le _ _)]
  rw [hsum] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

def jetOrder (f : E → K) (x : E) : WithTop ℕ :=
  sInf ((fun n : ℕ => (n : WithTop ℕ)) '' {n | iteratedFDeriv K n f x ≠ 0})

theorem natCast_le_jetOrder_iff {f : E → K} {x : E} {n : ℕ} :
    (n : WithTop ℕ) ≤ jetOrder f x ↔
      ∀ i < n, iteratedFDeriv K i f x = 0 := by
  constructor
  · intro h i hi
    by_contra hne
    have hle : jetOrder f x ≤ (i : WithTop ℕ) := sInf_le ⟨i, hne, rfl⟩
    have : n ≤ i := by exact_mod_cast h.trans hle
    omega
  · intro h
    apply le_sInf
    rintro _ ⟨i, hi, rfl⟩
    by_contra! hlt
    have hin : i < n := by exact_mod_cast hlt
    exact hi (h i hin)

theorem jetOrder_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g) :
    jetOrder f x = jetOrder g x := by
  unfold jetOrder
  congr 3
  ext n
  rw [(h.iteratedFDeriv K n).eq_of_nhds]

/-- An analytic unit does not change the order defined by iterated Fréchet derivatives. -/
theorem jetOrder_mul_unit [CompleteSpace K] {f u : E → K} {x : E}
    (hf : AnalyticAt K f x) (hu : AnalyticAt K u x) (hu0 : u x ≠ 0) :
    jetOrder (fun y => u y * f y) x = jetOrder f x := by
  apply WithTop.eq_of_forall_coe_le_iff
  intro n
  change ((n : WithTop ℕ) ≤ jetOrder (fun y => u y * f y) x) ↔
    (n : WithTop ℕ) ≤ jetOrder f x
  rw [natCast_le_jetOrder_iff, natCast_le_jetOrder_iff]
  have hunit : ∀ᶠ y in 𝓝 x, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hinv : (fun y => (u y)⁻¹ * (u y * f y)) =ᶠ[𝓝 x] f := by
    filter_upwards [hunit] with y hy
    simp [hy]
  constructor
  · intro h i hi
    have hz := iteratedFDeriv_mul_eq_zero_of_vanishing_jet
      (hu.mul hf).contDiffAt (hu.inv hu0).contDiffAt
      (fun j hj => h j (hj.trans_lt hi))
    change iteratedFDeriv K i (fun y => (u y)⁻¹ * (u y * f y)) x = 0 at hz
    rw [(hinv.iteratedFDeriv K i).eq_of_nhds] at hz
    exact hz
  · intro h i hi
    exact iteratedFDeriv_mul_eq_zero_of_vanishing_jet hf.contDiffAt hu.contDiffAt
      (fun j hj => h j (hj.trans_lt hi))

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponProjectiveContact

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

private theorem PhilipponProjectiveContact_coordinate_ratio {K : Type*} [Field K] {ι : Type*}
    {f g : ι → K} {hf : f ≠ 0} {hg : g ≠ 0}
    (h : Projectivization.mk K f hf = Projectivization.mk K g hg)
    (j : ι) (hj : g j ≠ 0) :
    f j / g j ≠ 0 ∧ ∀ k, f k = (f j / g j) * g k := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K f g hf hg).mp h
  have hj' : f j = (a : K) * g j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  have hratio : f j / g j = (a : K) := by rw [hj']; exact mul_div_cancel_right₀ _ hj
  rw [hratio]
  refine ⟨a.ne_zero, ?_⟩
  intro k
  simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm

/-- Locally equal projective lifts change a multihomogeneous pullback by an analytic unit. -/
theorem MultiProjectiveSpace.jetOrder_eq_of_projective_lifts
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (f g : E → M.Variable → K) (x : E)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) x)
    (hg : ∀ v, AnalyticAt K (fun z => g z v) x)
    (hrep : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i, j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i, j⟩) hgi) :
    jetOrder (fun z => MvPolynomial.eval (f z) P) x = jetOrder (fun z => MvPolynomial.eval (g z) P) x := by
  classical
  have hpivot (i : M.FactorIndex) : ∃ j, g x ⟨i, j⟩ ≠ 0 := by
    obtain ⟨_, hgi, _⟩ := hrep.self_of_nhds i
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hgi
  choose j hj using hpivot
  let a (z : E) (i : M.FactorIndex) := f z ⟨i, j i⟩ / g z ⟨i, j i⟩
  let u (z : E) := ∏ i, a z i ^ D i
  have ha (i : M.FactorIndex) : AnalyticAt K (fun z => a z i) x :=
    (hf _).div (hg _) (hj i)
  have hu : AnalyticAt K u x := by
    exact Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow (D i))
  have hax (i : M.FactorIndex) : a x i ≠ 0 := by
    obtain ⟨hfi, hgi, heq⟩ := hrep.self_of_nhds i
    exact (PhilipponProjectiveContact_coordinate_ratio heq (j i) (hj i)).1
  have hux : u x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hax i))
  have hjnear : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex, g z ⟨i, j i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (hg _).continuousAt.eventually_ne (hj i)
  have hfg : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 x]
      (fun z => u z * MvPolynomial.eval (g z) P) := by
    filter_upwards [hrep, hjnear] with z hz hjz
    have hcoords : f z = fun v => a z v.1 * g z v := by
      funext v
      obtain ⟨hfi, hgi, heq⟩ := hz v.1
      exact (PhilipponProjectiveContact_coordinate_ratio heq (j v.1) (hjz v.1)).2 v.2
    rw [hcoords, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x := by
    change AnalyticAt K (fun z => aeval (g z) P) x
    exact AnalyticAt.aeval_mvPolynomial hg P
  exact (jetOrder_congr hfg).trans (jetOrder_mul_unit hgP hu hux)

private theorem PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact PhilipponProjectiveContact_completeSpace_of_isometric_ringEquiv e he

/-- The independence assertion in Philippon's definition of contact order, p. 358. -/
theorem projective_lift_contact_invariance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : IsMultihomogeneousOfDegree G P D)
    (f : A.ParameterSpace → G.ambient.Variable → K)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) 0)
    (hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
          G.embedding (g + A.map ⟨z, hz⟩) i) :
    vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
      {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0}) := by
  letI : CompleteSpace K := hK.completeSpace
  apply G.ambient.jetOrder_eq_of_projective_lifts P D hP
    (A.lift g) f 0 (A.lift_analytic g) hf
  filter_upwards [A.lift_represents g, hrep] with z hz hfz
  obtain ⟨hz, hAz⟩ := hz
  obtain ⟨hfz, hFz⟩ := hfz
  intro i
  obtain ⟨hA, heqA⟩ := hAz i
  obtain ⟨hF, heqF⟩ := hFz i
  exact ⟨hA, hF, heqA.trans heqF.symm⟩

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponAnalyticContainment

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_lift_eq_zero_of_mem_vanishingIdeal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} {p : M.Point} (hp : p ∈ V)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal V) :
    MvPolynomial.eval v P = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hideal : M.vanishingIdeal V ≤ RingHom.ker (MvPolynomial.eval v) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hz⟩
    change MvPolynomial.eval v Q = 0
    rw [hv', M.eval_block_scale Q D hD (M.coordinate p) (fun i => (a i : K)),
      show MvPolynomial.eval (M.coordinate p) Q = 0
      from hz p hp, mul_zero]
  exact hideal hP

/-- Containment forces every defining equation to have zero first derivative along A. -/
theorem analyticCodimension_eq_zero_of_carrier_subset
    {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hsub : A.carrier ⊆ H.carrier) : analyticCodimension A H.carrier = 0 := by
  have hker : A.tangentKernel H.carrier = ⊤ := by
    apply top_unique
    intro t _
    apply (Submodule.mem_iInf _).mpr
    intro P
    have hpull : A.pullback P.val 0 =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
      filter_upwards [A.lift_represents 0] with z hz
      obtain ⟨hz, hlift⟩ := hz
      have hmem : A.map ⟨z, hz⟩ ∈ H.carrier :=
        hsub (AddSubgroup.subset_closure ⟨⟨z, hz⟩, rfl⟩)
      apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hmem) (A.lift 0 z) _ P.property
      intro i
      obtain ⟨h, he⟩ := hlift i
      exact ⟨h, by simpa only [zero_add] using he⟩
    change fderiv K (A.pullback P.val 0) 0 t = 0
    rw [hpull.fderiv_eq]
    simp
  unfold analyticCodimension
  rw [hker, finrank_top]
  simp [AnalyticSubgroup.ParameterSpace]

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponAdditiveSubgroups

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)

theorem AlgebraicSubgroup.mem_of_homogeneous_equations
    {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    (H : AlgebraicSubgroup G) (x : G.Point)
    (hx : ∀ (P : G.CoordinateRing) (D : G.FactorIndex → ℕ),
      G.ambient.IsHomogeneous P D →
      (∀ y ∈ H.carrier, G.ambient.eval P (G.embedding y) = 0) →
      G.ambient.eval P (G.embedding x) = 0) : x ∈ H.carrier := by
  letI := G.ambient.zariskiTopology
  letI := G.zariskiTopology
  have hcl : @closure _ G.zariskiTopology H.carrier =
      G.embedding ⁻¹' G.ambient.zeroLocus (G.vanishingIdeal H.carrier) := by
    ext y
    rw [EmbeddedGroupProduct.zariskiTopology, closure_induced,
      ← G.ambient.zeroLocus_vanishingIdeal_eq_closure]
    rfl
  have hclosed : closure H.carrier = H.carrier := H.isClosed.closure_eq
  rw [← hclosed, hcl]
  intro P hP
  have hideal : G.vanishingIdeal H.carrier ≤
      RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hQ⟩
    exact hx Q D hD (fun y hy => hQ _ ⟨y, hy, rfl⟩)
  exact hideal hP

/-- Closed algebraic subgroups pull back to linear subspaces under additive
parametrizations with affine-linear projective coordinates, in characteristic zero. -/
theorem AlgebraicSubgroup.smul_mem_of_affine_linear_lift
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G)
    (q : V →+ G.Point) (b : G.ambient.Variable → K)
    (ell : G.ambient.Variable → V →ₗ[K] K)
    (hrep : ∀ v : V, ∀ i : G.FactorIndex,
      ∃ h : (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) ≠ 0,
        Projectivization.mk K (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) h =
          G.embedding (q v) i)
    (v : V) (hv : q v ∈ H.carrier) (c : K) : q (c • v) ∈ H.carrier := by
  classical
  apply H.mem_of_homogeneous_equations
  intro P D hP hzero
  let F : MvPolynomial (Fin 1) K := eval₂ C
    (fun j => C (b j) + C (ell j v) * X 0) P
  have hEval (a : K) : MvPolynomial.eval (fun _ : Fin 1 => a) F =
      MvPolynomial.eval (fun j => b j + ell j (a • v)) P := by
    dsimp only [F]
    rw [← eval_assoc]
    apply congrArg (fun w => MvPolynomial.eval w P)
    funext j
    simp [map_smul, mul_comm]
  have hF : F = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin 1 => Set.range (fun n : ℕ => (n : K)))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro w hw
    obtain ⟨n, hn⟩ := hw 0 (Set.mem_univ _)
    have hw' : w = fun _ => (n : K) := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hn.symm
    rw [hw', hEval, map_zero]
    apply (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (q ((n : K) • v)))
      (fun j => b j + ell j ((n : K) • v)) (hrep _) P D hP).mpr
    apply hzero
    change q ((n : K) • v) ∈ H.toAddSubgroup
    simpa only [Nat.cast_smul_eq_nsmul K, map_nsmul] using H.toAddSubgroup.nsmul_mem hv n
  have hfinal := hEval c
  rw [hF, map_zero] at hfinal
  exact (G.ambient.eval_eq_zero_iff_of_lift (G.embedding (q (c • v)))
    (fun j => b j + ell j (c • v)) (hrep _) P D hP).mp hfinal.symm

/-- In the additive cases, the actual preimage subgroup is a vector subspace;
linearity is proved from closedness and the coordinate formulas. -/
theorem AlgebraicSubgroup.exists_linear_pullback_of_affine_linear_lift
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    {G : EmbeddedGroupProduct K} (H : AlgebraicSubgroup G)
    (q : V →+ G.Point) (b : G.ambient.Variable → K)
    (ell : G.ambient.Variable → V →ₗ[K] K)
    (hrep : ∀ v : V, ∀ i : G.FactorIndex,
      ∃ h : (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) ≠ 0,
        Projectivization.mk K (fun j => b ⟨i, j⟩ + ell ⟨i, j⟩ v) h =
          G.embedding (q v) i) :
    ∃ W : Submodule K V, ∀ v, v ∈ W ↔ q v ∈ H.carrier := by
  refine ⟨{
    carrier := {v | q v ∈ H.carrier}
    zero_mem' := by
      change q 0 ∈ H.toAddSubgroup
      rw [map_zero]
      exact H.toAddSubgroup.zero_mem
    add_mem' := ?_
    smul_mem' := ?_
  }, fun _ => Iff.rfl⟩
  · intro v w hv hw
    change q (v + w) ∈ H.toAddSubgroup
    rw [map_add]
    exact H.toAddSubgroup.add_mem hv hw
  · intro c v hv
    exact H.smul_mem_of_affine_linear_lift q b ell hrep v hv c

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponHomogeneousOperations

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Reused implementation: Solutions.PhilipponParametrizedHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Compute a genuine quotient Hilbert function through a parametrization whose
polynomial kernel agrees with the homogeneous equations of the image. -/
theorem hilbertFunction_eq_finrank_image
    {T A : Type*} [CommRing A] [Algebra K A]
    (p : T → M.Point) (φ : M.CoordinateRing →ₐ[K] A) (D : M.FactorIndex → ℕ)
    (hker : ∀ P : M.CoordinateRing, M.IsHomogeneous P D →
      (φ P = 0 ↔ ∀ t, M.eval P (p t) = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        φ.toLinearMap) := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal (Set.range p)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := φ.toLinearMap.domRestrict V
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ φ P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hker P.val ((M.degreePiece_iff _ _).mp P.property)]
    constructor
    · intro h t
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self t)
    · intro h
      exact Ideal.subset_span ⟨⟨D, (M.degreePiece_iff _ _).mp P.property⟩,
        by rintro x ⟨t, rfl⟩; exact h t⟩
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have hg : LinearMap.range g = V.map φ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf, hg] at he
  exact he

/-- Univariate polynomial parametrizations compute the same kernel as their
projective image; arbitrary nonzero homogeneous lifts are allowed. -/
theorem hilbertFunction_eq_finrank_polynomial_image [Infinite K]
    (p : K → M.Point) (v : M.Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        (MvPolynomial.aeval v).toLinearMap) := by
  apply M.hilbertFunction_eq_finrank_image p (MvPolynomial.aeval v) D
  intro P hP
  have hev (t : K) : (MvPolynomial.aeval v P : Polynomial K).eval t =
      MvPolynomial.eval (fun j => (v j).eval t) P := by
    clear hP
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P j hP => simp [hP]
  constructor
  · intro hz t
    apply (M.eval_eq_zero_iff_of_lift (p t) (fun j => (v j).eval t) (hrep t) P D hP).mp
    rw [← hev, hz, Polynomial.eval_zero]
  · intro hz
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_zero, hev]
    exact (M.eval_eq_zero_iff_of_lift (p t) (fun j => (v j).eval t) (hrep t) P D hP).mpr (hz t)

/-- A blockwise polynomial parametrization bounds the univariate degree of
every homogeneous section by its weighted sum of block degrees. -/
theorem polynomial_image_natDegree_le
    (v : M.Variable → Polynomial K) (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) :
    (MvPolynomial.aeval v P : Polynomial K).natDegree ≤ ∑ i, D i * δ i := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  change ((Polynomial.C (MvPolynomial.coeff d P)) * _).natDegree ≤ _
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  change (d.prod (fun j n => v j ^ n)).natDegree ≤ _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ j : M.Variable, (v j ^ d j).natDegree ≤ ∑ j : M.Variable, d j * δ j.1 := by
      apply Finset.sum_le_sum
      intro j _
      exact (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hv j))
    _ = ∑ i, D i * δ i := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ y, d ⟨i, y⟩ * δ i) = _
      rw [← Finset.sum_mul, hP d hd i]

/-- A degree upper bound and lifts of the powers of X determine the full
homogeneous section image, rather than only bounding its dimension. -/
theorem polynomial_image_eq_degreeLT
    (v : M.Variable → Polynomial K) (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (hlift : ∀ k ≤ ∑ i, D i * δ i, ∃ P : M.CoordinateRing,
      M.IsHomogeneous P D ∧ MvPolynomial.aeval v P = Polynomial.X ^ k) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        (MvPolynomial.aeval v).toLinearMap =
      Polynomial.degreeLT K ((∑ i, D i * δ i) + 1) := by
  classical
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
    exact Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr
      (M.polynomial_image_natDegree_le v δ D hv P ((M.degreePiece_iff _ _).mp hP)))
  · rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
    intro Q hQ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨P, hP, heq⟩ := hlift k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    exact ⟨P, (M.degreePiece_iff _ _).mpr hP, heq⟩

/-- Exact Hilbert function for a polynomially parametrized projective locus
when all powers through the expected degree have homogeneous lifts. -/
theorem hilbertFunction_polynomial_parametrization [Infinite K]
    (p : K → M.Point) (v : M.Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (hlift : ∀ k ≤ ∑ i, D i * δ i, ∃ P : M.CoordinateRing,
      M.IsHomogeneous P D ∧ MvPolynomial.aeval v P = Polynomial.X ^ k) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = (∑ i, D i * δ i) + 1 := by
  rw [M.hilbertFunction_eq_finrank_polynomial_image p v hrep D,
    M.polynomial_image_eq_degreeLT v δ D hv hlift,
    (Polynomial.degreeLTEquiv K _).finrank_eq]
  simp

/-- The powers of X have homogeneous lifts for a line whose projections to
both projective factors are either constant or linear. -/
theorem binary_linear_parametrization_lifts
    (N : Fin 2 → ℕ) (v : (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).Variable →
      Polynomial K) (δ : Fin 2 → ℕ) (hδ : ∀ i, δ i ≤ 1)
    (U V : Fin 2 → (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).CoordinateRing)
    (hU : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (U i)
      (fun j => if j = i then 1 else 0))
    (hV : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (V i)
      (fun j => if j = i then 1 else 0))
    (hUeval : ∀ i, MvPolynomial.aeval v (U i) = 1)
    (hVeval : ∀ i, MvPolynomial.aeval v (V i) = Polynomial.X ^ δ i)
    (D : Fin 2 → ℕ) (k : ℕ) (hk : k ≤ ∑ i, D i * δ i) :
    ∃ P : (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).CoordinateRing,
      (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous P D ∧
        MvPolynomial.aeval v P = Polynomial.X ^ k := by
  let M : MultiProjectiveSpace K := ⟨2, by decide, N⟩
  let a := min k (D 0 * δ 0)
  let b := k - a
  have ha : a ≤ D 0 := (min_le_right _ _).trans (by simpa using Nat.mul_le_mul_left (D 0) (hδ 0))
  have hb : b ≤ D 1 := by
    have hc : b ≤ D 1 * δ 1 := by
      simp only [Fin.sum_univ_two] at hk
      dsimp [a, b]
      omega
    exact hc.trans (by simpa using Nat.mul_le_mul_left (D 1) (hδ 1))
  have hab : a + b = k := by dsimp [a, b]; omega
  have haδ : δ 0 * a = a := by
    have := hδ 0
    interval_cases h : δ 0
    · simp [a, h]
    · simp
  have hbδ : δ 1 * b = b := by
    have hc : b ≤ D 1 * δ 1 := by
      simp only [Fin.sum_univ_two] at hk
      dsimp [a, b]
      omega
    have := hδ 1
    interval_cases h : δ 1
    · have : b = 0 := by simpa [h] using hc
      simp [this]
    · simp
  let P := (V 0 ^ a * U 0 ^ (D 0 - a)) * (V 1 ^ b * U 1 ^ (D 1 - b))
  refine ⟨P, ?_, ?_⟩
  · have hp := (((hV 0).pow M a).mul M ((hU 0).pow M (D 0 - a))).mul M
      (((hV 1).pow M b).mul M ((hU 1).pow M (D 1 - b)))
    convert hp using 1
    funext i
    fin_cases i <;> simp <;> omega
  · dsimp [P]
    simp only [map_mul, map_pow, hUeval, hVeval, one_pow, mul_one, ← pow_add, ← pow_mul]
    rw [haδ, hbδ, hab]

/-- Recover the actual Hilbert polynomial of an affine line in a product of
two projective spaces from its coordinate parametrization. -/
theorem binary_linear_parametrization_hilbertPolynomial [Infinite K]
    (N : Fin 2 → ℕ) (p : K → (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).Point)
    (v : (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (δ : Fin 2 → ℕ) (hδ : ∀ i, δ i ≤ 1)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (U V : Fin 2 → (MultiProjectiveSpace.mk 2 (by decide) N (K := K)).CoordinateRing)
    (hU : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (U i)
      (fun j => if j = i then 1 else 0))
    (hV : ∀ i, (MultiProjectiveSpace.mk 2 (by decide) N).IsHomogeneous (V i)
      (fun j => if j = i then 1 else 0))
    (hUeval : ∀ i, MvPolynomial.aeval v (U i) = 1)
    (hVeval : ∀ i, MvPolynomial.aeval v (V i) = Polynomial.X ^ δ i) :
    Hilbert.hilbertPolynomial K 2 N
      ((MultiProjectiveSpace.mk 2 (by decide) N).vanishingIdeal (Set.range p)) =
        MvPolynomial.C (δ 0 : ℚ) * MvPolynomial.X 0 +
          MvPolynomial.C (δ 1 : ℚ) * MvPolynomial.X 1 + 1 := by
  let M : MultiProjectiveSpace K := ⟨2, by decide, N⟩
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, ?_⟩
  intro D _
  rw [M.hilbertFunction_polynomial_parametrization p v hrep δ D hv
    (binary_linear_parametrization_lifts N v δ hδ U V hU hV hUeval hVeval D)]
  change _ = (((∑ i : Fin 2, D i * δ i) + 1 : ℕ) : ℚ)
  simp [Fin.sum_univ_two, mul_comm]

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] {p : ℕ} {N : Fin p → ℕ}

/-- A nonzero linear top part of a Hilbert polynomial is exactly its degree form. -/
theorem degreeForm_of_hilbertPolynomial_linear
    (I : Ideal (CoordinateRing K p N)) (R : MvPolynomial (Fin p) ℚ)
    (hR : R.IsHomogeneous 1) (hne : R ≠ 0)
    (hP : hilbertPolynomial K p N I = R + 1) :
    degreeForm K p N I = R := by
  have hd : (R + 1).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
    · exact hR.totalDegree hne
    · simp [hR.totalDegree hne]
  simp only [degreeForm, hP, hd, Nat.factorial_one, Nat.cast_one, one_smul, map_add]
  rw [MvPolynomial.homogeneousComponent_eq_self hR,
    MvPolynomial.homogeneousComponent_eq_zero 1 1 (by simp : (1 : MvPolynomial (Fin p) ℚ).totalDegree < 1), add_zero]

end PhilipponMultiplicity.Hilbert
end
end


section
-- Reused implementation: Solutions.PhilipponRegularMapTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

/-- Two projective lifts represent the same point precisely when all their
two-by-two cross products vanish. -/
theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Reused implementation: Solutions.SeparatedFunctionProducts

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace SeparatedFunctionProducts

variable {K ι : Type*} [Field K] [Fintype ι]
  {X κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Linear independence of functions is preserved by taking products in
separate variables. The underlying sets need not be finite or nonempty. -/
theorem linearIndependent (f : ∀ i, κ i → X i → K)
    (hf : ∀ i, LinearIndependent K (f i)) :
    LinearIndependent K (fun j : ∀ i, κ i => fun x : ∀ i, X i => ∏ i, f i (j i) (x i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  let L : MultilinearMap K (fun i => κ i → K) K :=
    ∑ k : ∀ i, κ i, c k •
      (MultilinearMap.mkPiRing K ι 1).compLinearMap
        (fun i => LinearMap.proj (k i))
  have hL : L = 0 := by
    apply MultilinearMap.ext_of_span_eq_top
      (fun i => span_flip_eq_top_iff_linearIndependent.mpr (hf i))
    intro x
    have h := congrFun hc x
    simpa [L, MultilinearMap.sum_apply, MultilinearMap.smul_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply,
      LinearMap.proj_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
      flip] using h
  have h := DFunLike.congr_fun hL (fun i => Pi.single (j i) (1 : K))
  simpa [L, MultilinearMap.sum_apply, MultilinearMap.smul_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply,
    LinearMap.proj_apply, Pi.single_apply, Fintype.prod_ite_zero,
    ← funext_iff, smul_eq_mul] using h

/-- The space spanned by separated products has dimension equal to the product
of the dimensions of the individual spaces of functions. -/
theorem finrank_span_products (W : ∀ i, Submodule K (X i → K))
    [∀ i, Module.Finite K (W i)] :
    Module.finrank K (Submodule.span K
      (Set.range (fun w : ∀ i, W i => fun x : ∀ i, X i => ∏ i, (w i).val (x i)))) =
      ∏ i, Module.finrank K (W i) := by
  classical
  let b (i : ι) := Module.finBasis K (W i)
  let μ : MultilinearMap K (fun i => W i) ((∀ i, X i) → K) :=
    MultilinearMap.pi (fun x => (MultilinearMap.mkPiRing K ι 1).compLinearMap
      (fun i => (LinearMap.proj (x i)).comp (W i).subtype))
  have hμeval (w : ∀ i, W i) : μ w = fun x => ∏ i, (w i).val (x i) := by
    ext x
    simp [μ, MultilinearMap.mkPiRing_apply]
  let S := Submodule.span K (Set.range
    (fun j : ∀ i, Fin (Module.finrank K (W i)) => μ (fun i => b i (j i))))
  have hμ (w : ∀ i, W i) : μ w ∈ S := by
    have hz : S.mkQ.compMultilinearMap μ = 0 := by
      apply Module.Basis.ext_multilinear b
      intro j
      change S.mkQ (μ (fun i => b i (j i))) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span (Set.mem_range_self j)
    have h := DFunLike.congr_fun hz w
    exact (Submodule.Quotient.mk_eq_zero S).mp h
  have hspan : Submodule.span K (Set.range
      (fun w : ∀ i, W i => fun x : ∀ i, X i => ∏ i, (w i).val (x i))) = S := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change (fun x => ∏ i, (w i).val (x i)) ∈ S
      rw [← hμeval w]
      exact hμ w
    · apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply Submodule.subset_span
      refine ⟨fun i => b i (j i), ?_⟩
      ext x
      simp [μ, MultilinearMap.mkPiRing_apply]
  rw [hspan]
  have hlin (i : ι) : LinearIndependent K (fun j => (b i j : X i → K)) :=
    (b i).linearIndependent.map' (W i).subtype (Submodule.ker_subtype _)
  have hprod := linearIndependent (fun i j => (b i j : X i → K)) hlin
  have hprod' : LinearIndependent K
      (fun j : ∀ i, Fin (Module.finrank K (W i)) => μ (fun i => b i (j i))) := by
    simpa only [hμeval] using hprod
  rw [show Module.finrank K S = Fintype.card (∀ i, Fin (Module.finrank K (W i)))
    from finrank_span_eq_card hprod']
  simp [Fintype.card_pi]

end SeparatedFunctionProducts

end
end


section
-- Reused implementation: Solutions.PhilipponProductHilbert

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_total {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : P.IsHomogeneous (∑ i, D i) := by
  intro a ha
  change (Finsupp.weight (fun _ : M.Variable => (1 : ℕ))) a = _
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => hP a (mem_support_iff.mpr ha) i)

instance degreePiece_finite (D : M.FactorIndex → ℕ) :
    Module.Finite K (Hilbert.degreePiece K M.factorCount M.ambientDimension D) := by
  let W := MvPolynomial.homogeneousSubmodule M.Variable K (∑ i, D i)
  letI : Module.Finite K W := Module.Finite.of_fg
    (MvPolynomial.homogeneousSubmodule_fg _ _ _)
  have hle : Hilbert.degreePiece K M.factorCount M.ambientDimension D ≤ W := by
    intro P hP
    exact M.homogeneous_total ((M.degreePiece_iff P D).mp hP)
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

def evaluationMap {X : Type*} (p : X → M.Point) : M.CoordinateRing →ₐ[K] (X → K) :=
  AlgHom.pi (fun x => MvPolynomial.aeval (M.coordinate (p x)))

@[simp] theorem evaluationMap_apply {X : Type*} (p : X → M.Point)
    (P : M.CoordinateRing) (x : X) : M.evaluationMap p P x = M.eval P (p x) := rfl

def sectionSpace {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Submodule K (X → K) :=
  (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
    (M.evaluationMap p).toLinearMap

instance sectionSpace_finite {X : Type*} (p : X → M.Point) (D : M.FactorIndex → ℕ) :
    Module.Finite K (M.sectionSpace p D) := by
  unfold sectionSpace
  infer_instance

theorem hilbertFunction_eq_sectionSpace {X : Type*} (p : X → M.Point)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = Module.finrank K (M.sectionSpace p D) := by
  apply M.hilbertFunction_eq_finrank_image p (M.evaluationMap p) D
  intro P _
  exact funext_iff

def includeBlock (i : M.FactorIndex) :
    (projectiveSpace K (M.ambientDimension i)).Variable → M.Variable :=
  fun v => ⟨i, v.2⟩

theorem homogeneous_includeBlock (i : M.FactorIndex)
    {P : (projectiveSpace K (M.ambientDimension i)).CoordinateRing} {d : ℕ}
    (hP : (projectiveSpace K (M.ambientDimension i)).IsHomogeneous P (fun _ => d)) :
    M.IsHomogeneous (rename (M.includeBlock i) P) (Pi.single i d) := by
  classical
  have h := hP.eval₂_blocks M (projectiveSpace K (M.ambientDimension i))
    (fun v => X (M.includeBlock i v)) (fun _ => Pi.single i 1)
    (fun v => by
      convert M.isHomogeneous_X (M.includeBlock i v) using 1
      ext j
      simp [includeBlock, Pi.single_apply])
  convert h using 1
  · rw [rename_eq_aeval]
    rfl
  · funext j
    simp [Pi.single_apply, projectiveSpace]

theorem sectionSpace_product (X : M.FactorIndex → Type*)
    (p : ∀ i, X i → Projectivization K (Fin (M.ambientDimension i + 1) → K))
    (D : M.FactorIndex → ℕ) :
    M.sectionSpace (fun x i => p i (x i)) D =
      Submodule.span K (Set.range (fun w : ∀ i,
        (projectiveSpace K (M.ambientDimension i)).sectionSpace
          (fun x _ => p i x) (fun _ => D i) =>
        fun x : ∀ i, X i => ∏ i, (w i).val (x i))) := by
  classical
  let W (i : M.FactorIndex) := (projectiveSpace K (M.ambientDimension i)).sectionSpace
    (fun x _ => p i x) (fun _ => D i)
  let S := Submodule.span K (Set.range
    (fun w : ∀ i, W i => fun x : ∀ i, X i => ∏ i, (w i).val (x i)))
  change _ = S
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    have hPD := (M.degreePiece_iff P D).mp hP
    rw [P.as_sum, map_sum]
    apply S.sum_mem
    intro a ha
    let a' (i : M.FactorIndex) : (projectiveSpace K (M.ambientDimension i)).Variable →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm (fun v => a ⟨i, v.2⟩)
    have hmono (i : M.FactorIndex) :
        (projectiveSpace K (M.ambientDimension i)).IsHomogeneous
          (monomial (a' i) (1 : K)) (fun _ => D i) := by
      intro b hb j
      have hb' : b = a' i := Finset.mem_singleton.mp (support_monomial_subset hb)
      subst b
      simpa [a', projectiveSpace] using hPD a ha i
    let w (i : M.FactorIndex) : W i :=
      ⟨(projectiveSpace K (M.ambientDimension i)).evaluationMap (fun x _ => p i x)
          (monomial (a' i) 1),
        ⟨monomial (a' i) 1,
          ((projectiveSpace K (M.ambientDimension i)).degreePiece_iff _ _).mpr (hmono i), rfl⟩⟩
    have hw : (fun x : ∀ i, X i => ∏ i, (w i).val (x i)) ∈ S :=
      Submodule.subset_span (Set.mem_range_self w)
    convert S.smul_mem (coeff a P) hw using 1
    ext x
    change M.eval (monomial a (coeff a P)) (fun i => p i (x i)) = _
    simp only [eval, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    simp [w, evaluationMap_apply, eval, eval_monomial, a', coordinate,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma, projectiveSpace]
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hrep (i : M.FactorIndex) :
        ∃ Q : (projectiveSpace K (M.ambientDimension i)).CoordinateRing,
          (projectiveSpace K (M.ambientDimension i)).IsHomogeneous Q (fun _ => D i) ∧
          (projectiveSpace K (M.ambientDimension i)).evaluationMap (fun x _ => p i x) Q =
            (w i).val := by
      obtain ⟨Q, hQ, heq⟩ := (w i).property
      exact ⟨Q, ((projectiveSpace K (M.ambientDimension i)).degreePiece_iff _ _).mp hQ, heq⟩
    choose Q hQ heq using hrep
    refine ⟨∏ i, rename (M.includeBlock i) (Q i), ?_, ?_⟩
    · apply (M.degreePiece_iff _ _).mpr
      have h := M.isHomogeneous_prod Finset.univ (fun i => rename (M.includeBlock i) (Q i))
        (fun i => Pi.single i (D i)) (fun i _ => M.homogeneous_includeBlock i (hQ i))
      convert h using 1
      ext j
      simp [Pi.single_apply]
    · ext x
      change M.eval (∏ i, rename (M.includeBlock i) (Q i)) (fun i => p i (x i)) = _
      simp only [eval, map_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [← heq i]
      simp only [evaluationMap_apply, eval, eval_rename]
      congr 1

/-- Exact multiplicativity of the quotient Hilbert function for products of
projective sets, before any Hilbert-polynomial existence theorem is used. -/
theorem hilbertFunction_product (X : M.FactorIndex → Type*)
    (p : ∀ i, X i → Projectivization K (Fin (M.ambientDimension i + 1) → K))
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range (fun x : ∀ i, X i => fun i => p i (x i)))) D =
      ∏ i, Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
          (Set.range (fun x : X i => fun _ => p i x))) (fun _ => D i) := by
  rw [M.hilbertFunction_eq_sectionSpace, M.sectionSpace_product,
    SeparatedFunctionProducts.finrank_span_products]
  apply Finset.prod_congr rfl
  intro i _
  exact ((projectiveSpace K (M.ambientDimension i)).hilbertFunction_eq_sectionSpace
    (fun x _ => p i x) (fun _ => D i)).symm

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity
open SectionThree

theorem product_projective_hilbert_function (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (d : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (productCarrier M V)) d =
      ∏ i, Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
        ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
          (V i).carrierInSingleFactor) (fun _ => d i) := by
  have hi (i : M.FactorIndex) :
      Set.range (fun x : (V i).carrier => fun _ : Fin 1 => x.val) =
        (V i).carrierInSingleFactor := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hp : Set.range (fun x : ∀ i, (V i).carrier => fun i => (x i).val) =
      productCarrier M V := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩ i
      exact (v i).property
    · intro h
      exact ⟨fun i => ⟨x i, h i⟩, rfl⟩
  have h := M.hilbertFunction_product
    (fun i => (V i).carrier) (fun _ x => x.val) d
  rw [hp] at h
  refine h.trans (Finset.prod_congr rfl ?_)
  intro i _
  exact congrArg (fun S => Hilbert.hilbertFunction K 1 (fun _ => M.ambientDimension i)
    ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal S) (fun _ => d i)) (hi i)

/-- Existence for the ordinary projective factors and the proved exact Hilbert
function identity determine the multigraded Hilbert polynomial of the product. -/
theorem product_projective_hilbert_polynomial_of_exists (K : Type*) [Field K]
    (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hexists : ∀ i, ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => M.ambientDimension i)
      ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
        (V i).carrierInSingleFactor) P) :
    Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)) := by
  classical
  have hspec (i : M.FactorIndex) := Hilbert.hilbertPolynomial_spec
    K 1 (fun _ => M.ambientDimension i)
    ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
      (V i).carrierInSingleFactor) (hexists i)
  choose d₀ hd₀ using hspec
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun i => d₀ i 0, ?_⟩
  intro d hd
  rw [map_prod, product_projective_hilbert_function, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [eval_rename]
  apply hd₀ i (fun _ => d i)
  intro j
  fin_cases j
  exact hd i

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponColonHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem component_mul_homogeneous
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (Q : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)
      (P * Q) =
    P * weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d Q := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hP' : P ∈ weightedHomogeneousSubmodule K w D :=
    (M.degreePiece_iff P D).mpr hP
  have hh := DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K w) (b := Q) (j := d) hP'
  change ((MvPolynomial.decompose' K w (P * Q)) (D + d) : M.CoordinateRing) =
    P * ((MvPolynomial.decompose' K w Q) d : M.CoordinateRing) at hh
  simpa only [MvPolynomial.decompose'_apply] using hh

instance quotientPiece_finite_colon (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

/-- Colon by a multihomogeneous element preserves the actual grading. -/
theorem homogeneous_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I.colon {P}) := by
  intro Q hQ d
  rw [Submodule.mem_colon_singleton, smul_eq_mul] at hQ ⊢
  have h := hI (P * Q) (by simpa [mul_comm] using hQ) (D + d)
  rw [component_mul_homogeneous M hP Q d, mul_comm] at h
  exact h

/-- The cyclic exact sequence, with the multiplication kernel removed by
passing to the colon quotient, works without a regularity hypothesis. -/
theorem hilbertFunction_colon_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension (I.colon {P}) d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by
  classical
  let J := I ⊔ Ideal.span {P}
  let C := I.colon {P}
  let U := quotientPiece K M.factorCount M.ambientDimension C d
  let W := quotientPiece K M.factorCount M.ambientDimension I (D + d)
  let V := quotientPiece K M.factorCount M.ambientDimension J (D + d)
  let mulP : (M.CoordinateRing ⧸ C) →ₗ[K] (M.CoordinateRing ⧸ I) :=
    (C.restrictScalars K).liftQ
      ((Ideal.Quotient.mkₐ K I).toLinearMap.comp (LinearMap.mulLeft K P)) (by
        intro Q hQ
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        change Q ∈ I.colon {P} at hQ
        change P * Q ∈ I
        simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hQ)
  have mulP_mk (Q : M.CoordinateRing) :
      mulP (Ideal.Quotient.mk C Q) = Ideal.Quotient.mk I (P * Q) := rfl
  have mulP_inj : Function.Injective mulP := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
  let f : U →ₗ[K] W :=
    (mulP.domRestrict U).codRestrict W (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨P * Q, ((M.degreePiece_iff P D).mpr hP).mul hQ, rfl⟩)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact mulP_inj (congrArg Subtype.val hxy)
  let q : (M.CoordinateRing ⧸ I) →ₐ[K] (M.CoordinateRing ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) (by
      intro x hx
      exact (le_sup_left : I ≤ J) hx)
  let g : W →ₗ[K] V :=
    (q.toLinearMap.domRestrict W).codRestrict V (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, Q, hQ, rfl⟩
    exact ⟨⟨Ideal.Quotient.mk I Q, ⟨Q, hQ, rfl⟩⟩, rfl⟩
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨Q, hQ, hQx⟩ := x.property
      have hQJ : Q ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hx' := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
        change q x.val = 0 at hx'
        rw [← hQx] at hx'
        exact hx'
      obtain ⟨a, b, hb, heq⟩ :=
        Ideal.mem_span_singleton_sup.mp (show Q ∈ Ideal.span {P} ⊔ I by
          simpa only [sup_comm] using hQJ)
      let a' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) d a
      let b' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) (D + d) b
      have hb' : b' ∈ I := hI b hb (D + d)
      have hproj : P * a' + b' = Q := by
        have hh := congrArg
          (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)) heq
        rw [map_add, mul_comm a P, component_mul_homogeneous M hP a d,
          IsWeightedHomogeneous.weightedHomogeneousComponent_same hQ] at hh
        exact hh
      refine ⟨⟨Ideal.Quotient.mk C a', ⟨a', weightedHomogeneousComponent_mem _ _ _, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change Ideal.Quotient.mk I (P * a') = x.val
      change Ideal.Quotient.mk I Q = x.val at hQx
      rw [← hQx, ← hproj, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb', add_zero]
    · rintro ⟨y, rfl⟩
      obtain ⟨Q, hQ, hQy⟩ := y.property
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change q (mulP y.val) = 0
      rw [← hQy]
      change Ideal.Quotient.mk J (P * Q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact J.mul_mem_right Q ((le_sup_right : Ideal.span {P} ≤ J)
        (Ideal.subset_span (Set.mem_singleton P)))
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponPrimeFiltration

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d

/-- The homogeneous product criterion also detects ordinary primality for
the block grading. A lexicographic order is used only to apply that criterion. -/
theorem prime_of_homogeneous_products (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤)
    (hmul : ∀ P Q : M.CoordinateRing, (∃ D, M.IsHomogeneous P D) →
      (∃ E, M.IsHomogeneous Q E) → P * Q ∈ I → P ∈ I ∨ Q ∈ I) : I.IsPrime := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply]
    have heq : weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
      ext e
      simp only [coeff_weightedHomogeneousComponent]
      rfl
    rw [heq]
    exact hI f hf (ofLex d)
  apply hIg.isPrime_of_homogeneous_mem_or_mem hne
  rintro P Q ⟨D, hP⟩ ⟨E, hQ⟩ hPQ
  apply hmul P Q _ _ hPQ
  · exact ⟨ofLex D, (M.degreePiece_iff P (ofLex D)).mp hP⟩
  · exact ⟨ofLex E, (M.degreePiece_iff Q (ofLex E)).mp hQ⟩

/-- A proper homogeneous quotient contains a shifted homogeneous cyclic
submodule whose annihilator is prime. This is the prime-filtration step. -/
theorem exists_homogeneous_prime_colon (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hne : I ≠ ⊤) :
    ∃ P : M.CoordinateRing, ∃ D : M.FactorIndex → ℕ,
      M.IsHomogeneous P D ∧ P ∉ I ∧ (I.colon {P}).IsPrime := by
  classical
  let S : Ideal M.CoordinateRing → Prop :=
    fun J => ∃ P D, M.IsHomogeneous P D ∧ P ∉ I ∧ J = I.colon {P}
  have hS : ∃ J, S J := by
    refine ⟨I.colon {(1 : M.CoordinateRing)}, 1, 0, ?_, ?_, rfl⟩
    · exact (M.degreePiece_iff 1 0).mp (isWeightedHomogeneous_one K _)
    · exact (Ideal.ne_top_iff_one I).mp hne
  obtain ⟨J, hJ, hmax⟩ := exists_maximal_of_wellFoundedGT S hS
  obtain ⟨P, D, hP, hPI, rfl⟩ := hJ
  refine ⟨P, D, hP, hPI, prime_of_homogeneous_products M _
    (homogeneous_colon M I hI P D hP) ?_ ?_⟩
  · simpa using hPI
  · intro A B hA hB hAB
    by_cases hBP : B * P ∈ I
    · exact Or.inr (Submodule.mem_colon_singleton.mpr hBP)
    · left
      obtain ⟨E, hB⟩ := hB
      have hBP_hom : M.IsHomogeneous (B * P) (E + D) := by
        exact (M.degreePiece_iff (B * P) (E + D)).mp
          (((M.degreePiece_iff B E).mpr hB).mul ((M.degreePiece_iff P D).mpr hP))
      have hle : I.colon {P} ≤ I.colon {B * P} := by
        intro x hx
        rw [Submodule.mem_colon_singleton, smul_eq_mul] at hx ⊢
        simpa only [mul_left_comm] using I.mul_mem_left B hx
      have hge := hmax ⟨B * P, E + D, hBP_hom, hBP, rfl⟩ hle
      apply hge
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hAB ⊢
      simpa only [mul_assoc] using hAB

/-- A finite chain from a homogeneous ideal to the unit ideal, with each
successive quotient generated by one homogeneous element and having prime
annihilator. Thus every cyclic factor is a shifted prime quotient. -/
theorem homogeneous_prime_filtration (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    ∃ n : ℕ, ∃ J : Fin (n + 1) → Ideal M.CoordinateRing,
      ∃ P : Fin n → M.CoordinateRing, ∃ D : Fin n → M.FactorIndex → ℕ,
      J 0 = I ∧ J (Fin.last n) = ⊤ ∧
      (∀ j, IsMultihomogeneousIdeal M (J j)) ∧
      (∀ j, M.IsHomogeneous (P j) (D j) ∧ P j ∉ J j.castSucc ∧
        J j.succ = J j.castSucc ⊔ Ideal.span {P j} ∧
        ((J j.castSucc).colon {P j}).IsPrime) := by
  classical
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases htop : I = ⊤
    · subst I
      refine ⟨0, fun _ => ⊤, Fin.elim0, Fin.elim0, rfl, rfl, ?_, ?_⟩
      · intro j f hf d
        trivial
      · intro j; exact Fin.elim0 j
    · obtain ⟨P, D, hP, hPI, hprime⟩ := exists_homogeneous_prime_colon M I hI htop
      have hlt : I < I ⊔ Ideal.span {P} := by
        apply lt_of_le_of_ne le_sup_left
        intro heq
        apply hPI
        rw [heq]
        exact (le_sup_right : Ideal.span {P} ≤ I ⊔ Ideal.span {P})
          (Ideal.subset_span (Set.mem_singleton P))
      obtain ⟨n, J, Q, E, hfirst, hlast, hhom, hstep⟩ :=
        ih _ hlt (homogeneous_sup_span M I hI P D hP)
      refine ⟨n + 1, Fin.cons I J, Fin.cons P Q, Fin.cons D E, rfl, ?_, ?_, ?_⟩
      · change J (Fin.last n) = ⊤
        exact hlast
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact hI
        · exact hhom i
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero] using
            (show M.IsHomogeneous P D ∧ P ∉ I ∧ J 0 = I ⊔ Ideal.span {P} ∧
              (I.colon {P}).IsPrime from ⟨hP, hPI, hfirst, hprime⟩)
        · simpa only [Fin.cons_succ, Fin.castSucc_succ] using hstep i

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponStandardMonomials

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.StandardMonomials

variable {K σ Γ : Type*} [Field K] [AddCommMonoid Γ]

def initialExponents (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    Set (σ →₀ ℕ) :=
  {e | ∃ f ∈ I, f ≠ 0 ∧ m.degree f = e}

theorem initialExponents_upper (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    IsUpperSet (initialExponents m I) := by
  classical
  intro a b hab ha
  obtain ⟨f, hf, hf0, rfl⟩ := ha
  refine ⟨monomial (b - m.degree f) (1 : K) * f, I.mul_mem_left _ hf,
    mul_ne_zero (by simp) hf0, ?_⟩
  rw [m.degree_mul (by simp) hf0, m.degree_monomial]
  simpa using tsub_add_cancel_of_le hab

theorem normal_representative (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, f - r ∈ I ∧
      ∀ e ∈ r.support, e ∉ initialExponents m I := by
  classical
  let B := {g : MvPolynomial σ K // g ∈ I ∧ g ≠ 0}
  obtain ⟨g, r, heq, _, hr⟩ := m.div
    (b := fun b : B => b.val)
    (fun b => isUnit_iff_ne_zero.mpr (m.leadingCoeff_ne_zero_iff.mpr b.property.2)) f
  refine ⟨r, ?_, ?_⟩
  · rw [heq, add_sub_cancel_right]
    change g.sum (fun b c => c * b.val) ∈ I
    exact I.sum_mem (fun b _ => I.mul_mem_left _ b.property.1)
  · intro e he ⟨b, hb, hb0, hbe⟩
    exact hr e he ⟨b, hb, hb0⟩ (le_of_eq hbe)

theorem weighted_normal_representative (m : MonomialOrder σ)
    (w : σ → Γ) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ d, weightedHomogeneousComponent w d f ∈ I)
    (d : Γ) (f : MvPolynomial σ K) (hf : f.IsWeightedHomogeneous w d) :
    ∃ r : MvPolynomial σ K, f - r ∈ I ∧ r.IsWeightedHomogeneous w d ∧
      ∀ e ∈ r.support, e ∉ initialExponents m I := by
  classical
  obtain ⟨r, hfr, hr⟩ := normal_representative m I f
  refine ⟨weightedHomogeneousComponent w d r, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  · have h := hI (f - r) hfr d
    simpa only [map_sub, weightedHomogeneousComponent_of_mem hf, if_true] using h
  · intro e he
    rw [support_weightedHomogeneousComponent] at he
    exact hr e (Finset.mem_filter.mp he).1

theorem normal_piece_equiv (m : MonomialOrder σ) (w : σ → Γ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ d, weightedHomogeneousComponent w d f ∈ I) (d : Γ) :
    Nonempty ((restrictSupport K {e | Finsupp.weight w e = d ∧
        e ∉ initialExponents m I}) ≃ₗ[K]
      ((weightedHomogeneousSubmodule K w d).map
        (Ideal.Quotient.mkₐ K I).toLinearMap)) := by
  classical
  let S : Set (σ →₀ ℕ) := {e | Finsupp.weight w e = d ∧ e ∉ initialExponents m I}
  let V := restrictSupport K S
  let W := (weightedHomogeneousSubmodule K w d).map (Ideal.Quotient.mkₐ K I).toLinearMap
  have memV (f : MvPolynomial σ K) : f ∈ V ↔ ∀ e ∈ f.support, e ∈ S := Iff.rfl
  have homog {f : MvPolynomial σ K} (hf : f ∈ V) : f.IsWeightedHomogeneous w d := by
    intro e he
    exact ((memV f).mp hf e (mem_support_iff.mpr he)).1
  let q : V →ₗ[K] W :=
    { toFun := fun f => ⟨Ideal.Quotient.mk I f.val, ⟨f.val, homog f.property, rfl⟩⟩
      map_add' := by intro f g; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c f; apply Subtype.ext; exact (Ideal.Quotient.mkₐ K I).toLinearMap.map_smul c f.val }
  have hqinj : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro f hf
    have hIf : f.val ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact congrArg Subtype.val hf
    have hf0 : f.val = 0 := by
      by_contra hn
      exact ((memV f.val).mp f.property (m.degree f.val)
        ((m.degree_mem_support_iff f.val).mpr hn)).2 ⟨f.val, hIf, hn, rfl⟩
    exact Subtype.ext hf0
  have hqsurj : Function.Surjective q := by
    rintro ⟨x, f, hf, rfl⟩
    obtain ⟨r, hfr, hr, hs⟩ := weighted_normal_representative m w I hI d f hf
    refine ⟨⟨r, (memV r).mpr (fun e he => ⟨hr (mem_support_iff.mp he), hs e he⟩)⟩, ?_⟩
    apply Subtype.ext
    exact (Ideal.Quotient.eq.mpr hfr).symm
  exact ⟨LinearEquiv.ofBijective q ⟨hqinj, hqsurj⟩⟩

theorem weighted_finrank_eq (m : MonomialOrder σ) (w : σ → Γ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ d, weightedHomogeneousComponent w d f ∈ I) (d : Γ) :
    Module.finrank K ((weightedHomogeneousSubmodule K w d).map
      (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {e : σ →₀ ℕ // Finsupp.weight w e = d ∧ e ∉ initialExponents m I} := by
  obtain ⟨e⟩ := normal_piece_equiv m w I hI d
  rw [← e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

/-- Dickson's lemma supplies finitely many forbidden monomial divisors. -/
theorem upperSet_finite_generators [Finite σ] (U : Set (σ →₀ ℕ)) (hU : IsUpperSet U) :
    ∃ s : Finset (σ →₀ ℕ), ∀ e, e ∈ U ↔ ∃ a ∈ s, a ≤ e := by
  classical
  have hp : U.IsPWO := Set.isPWO_of_wellQuasiOrderedLE U
  have ha : IsAntichain (· ≤ ·) {a | Minimal (· ∈ U) a} := by
    intro a ha b hb hab hle
    exact hab (le_antisymm hle (hb.2 ha.1 hle))
  have hs := ha.finite_of_partiallyWellOrderedOn
    (Set.isPWO_of_wellQuasiOrderedLE {a | Minimal (· ∈ U) a})
  refine ⟨hs.toFinset, fun e => ⟨?_, ?_⟩⟩
  · intro he
    obtain ⟨a, hae, ha⟩ := hp.exists_le_minimal he
    exact ⟨a, hs.mem_toFinset.mpr ha, hae⟩
  · rintro ⟨a, ha, hae⟩
    exact hU hae (hs.mem_toFinset.mp ha).1

end PhilipponMultiplicity.StandardMonomials

namespace PhilipponMultiplicity

/-- Every actual multigraded quotient piece is counted by standard monomials
avoiding finitely many forbidden divisors. No radicality assumption is used. -/
theorem multigraded_hilbert_function_standard_monomials
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ s : Finset (M.Variable →₀ ℕ), ∀ d : M.FactorIndex → ℕ,
      Hilbert.hilbertFunction K M.factorCount M.ambientDimension I d =
        Nat.card {e : M.Variable →₀ ℕ //
          Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) e = d ∧
          ∀ a ∈ s, ¬ a ≤ e} := by
  classical
  obtain ⟨instOrder, instWF⟩ := exists_wellFoundedGT M.Variable
  let m : MonomialOrder M.Variable := MonomialOrder.lex
  obtain ⟨s, hs⟩ := StandardMonomials.upperSet_finite_generators
    (StandardMonomials.initialExponents m I) (StandardMonomials.initialExponents_upper m I)
  refine ⟨s, fun d => ?_⟩
  rw [Hilbert.hilbertFunction, Hilbert.quotientPiece, Hilbert.degreePiece,
    StandardMonomials.weighted_finrank_eq m _ I hI d]
  simp only [hs, not_exists, not_and]

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponMonomialCells

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable {α : Type*} [Fintype α]

abbrev Free (B : ℕ) (b : α → Fin (B + 1)) := {x : α // (b x : ℕ) = B}

def Cell (B : ℕ) (b : α → Fin (B + 1)) :=
  {f : α → ℕ // ∀ x, min (f x) B = (b x : ℕ)}

def cellEquiv (B : ℕ) (b : α → Fin (B + 1)) : Cell B b ≃ (Free B b → ℕ) where
  toFun f x := f.val x.val - B
  invFun u := ⟨fun x => (b x : ℕ) + if h : (b x : ℕ) = B then u ⟨x,h⟩ else 0, by
    intro x
    have hbx := (b x).isLt
    dsimp only
    split_ifs with h
    · omega
    · omega⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have hx := f.property x
    have hbx := (b x).isLt
    dsimp
    split_ifs with h
    · omega
    · omega
  right_inv u := by
    funext x
    simp [x.property]

theorem cellEquiv_symm_sum (B : ℕ) (b : α → Fin (B + 1)) (u : Free B b → ℕ) :
    ∑ x, ((cellEquiv B b).symm u).val x =
      (∑ x, (b x : ℕ)) + ∑ x, u x := by
  classical
  change (∑ x, ((b x : ℕ) + if h : (b x : ℕ) = B then u ⟨x,h⟩ else 0)) = _
  rw [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr_set {x | (b x : ℕ) = B} _ u
    (fun x hx => by simp only [Set.mem_setOf_eq] at hx; simp [hx])
    (fun x hx => by simp only [Set.mem_setOf_eq] at hx; simp [hx])

def degreeCellEquiv (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) ≤ d) :
    {f : Cell B b // ∑ x, f.val x = d} ≃
      {u : Free B b → ℕ // ∑ x, u x = d - ∑ x, (b x : ℕ)} where
  toFun f := ⟨cellEquiv B b f.val, by
    have h := cellEquiv_symm_sum B b (cellEquiv B b f.val)
    rw [Equiv.symm_apply_apply, f.property] at h
    omega⟩
  invFun u := ⟨(cellEquiv B b).symm u.val, by
    rw [cellEquiv_symm_sum, u.property]
    omega⟩
  left_inv f := by apply Subtype.ext; exact (cellEquiv B b).symm_apply_apply f.val
  right_inv u := by apply Subtype.ext; exact (cellEquiv B b).apply_symm_apply u.val

instance degreeCell_finite (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ) :
    Finite {f : Cell B b // ∑ x, f.val x = d} := by
  classical
  haveI : Finite {f : α → ℕ // ∑ x, f x = d} :=
    Finite.of_equiv (Sym α d) (Sym.equivNatSumOfFintype α d)
  apply Finite.of_injective
    (fun f : {f : Cell B b // ∑ x, f.val x = d} =>
      (⟨f.val.val, f.property⟩ : {f : α → ℕ // ∑ x, f x = d}))
  intro f g h
  have hh : f.val.val = g.val.val :=
    congrArg (fun x : {f : α → ℕ // ∑ x, f x = d} => x.val) h
  exact Subtype.ext (Subtype.ext hh)

def flatCellEquiv (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ) :
    {f : α → ℕ // (∀ x, min (f x) B = (b x : ℕ)) ∧ ∑ x, f x = d} ≃
      {f : Cell B b // ∑ x, f.val x = d} where
  toFun f := ⟨⟨f.val, f.property.1⟩, f.property.2⟩
  invFun f := ⟨f.val.val, f.val.property, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance flatCell_finite (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ) :
    Finite {f : α → ℕ // (∀ x, min (f x) B = (b x : ℕ)) ∧ ∑ x, f x = d} :=
  Finite.of_equiv _ (flatCellEquiv B b d).symm

theorem degreeCell_card (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) ≤ d) :
    Nat.card {f : Cell B b // ∑ x, f.val x = d} =
      (Nat.card (Free B b)).multichoose (d - ∑ x, (b x : ℕ)) := by
  classical
  rw [Nat.card_congr (degreeCellEquiv B b d hd)]
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Free B b) _)]
  exact Sym.natCard_sym_eq_multichoose _ _

theorem degreeCell_card_pos (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) ≤ d) (hr : 0 < Nat.card (Free B b)) :
    Nat.card {f : Cell B b // ∑ x, f.val x = d} =
      (d - (∑ x, (b x : ℕ)) + (Nat.card (Free B b) - 1)).choose
        (Nat.card (Free B b) - 1) := by
  rw [degreeCell_card B b d hd, Nat.multichoose_eq]
  have hh : Nat.card (Free B b) + (d - ∑ x, (b x : ℕ)) - 1 =
      d - (∑ x, (b x : ℕ)) + (Nat.card (Free B b) - 1) := by omega
  rw [hh, ← Nat.choose_symm (show d - (∑ x, (b x : ℕ)) ≤
    d - (∑ x, (b x : ℕ)) + (Nat.card (Free B b) - 1) by omega)]
  simp

theorem degreeCell_card_zero (B : ℕ) (b : α → Fin (B + 1)) (d : ℕ)
    (hd : (∑ x, (b x : ℕ)) < d) (hr : Nat.card (Free B b) = 0) :
    Nat.card {f : Cell B b // ∑ x, f.val x = d} = 0 := by
  rw [degreeCell_card B b d hd.le, hr]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show d - ∑ x, (b x : ℕ) ≠ 0 by omega)
  rw [hn]
  exact Nat.multichoose_zero_succ n

end PhilipponMultiplicity.MonomialCells

end
end


section
-- Reused implementation: Solutions.PhilipponMonomialPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)
abbrev Pattern (B : ℕ) := ∀ i : Fin p, Fin (N i + 1) → Fin (B + 1)

def Avoid (s : Finset (Var p N →₀ ℕ)) (f : Var p N → ℕ) : Prop :=
  ∀ a ∈ s, ¬ ∀ v, a v ≤ f v

theorem weight_apply (e : Var p N →₀ ℕ) (i : Fin p) :
    Finsupp.weight (Hilbert.blockWeight p N) e i = ∑ j, e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : Fin p, ∑ j : Fin (N b + 1),
    e ⟨b,j⟩ • Hilbert.blockWeight p N ⟨b,j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem exists_bound (s : Finset (Var p N →₀ ℕ)) :
    ∃ B : ℕ, ∀ a ∈ s, ∀ v, a v ≤ B := by
  classical
  refine ⟨s.sup (fun a => Finset.univ.sup a), ?_⟩
  intro a ha v
  exact (Finset.le_sup (f := a) (Finset.mem_univ v)).trans
    (Finset.le_sup (f := fun a : Var p N →₀ ℕ => Finset.univ.sup a) ha)

theorem avoid_cap (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (f : Var p N → ℕ) :
    Avoid p N s (fun v => min (f v) B) ↔ Avoid p N s f := by
  constructor
  · intro h a ha hle
    exact h a ha (fun v => le_min (hle v) (hB a ha v))
  · intro h a ha hle
    exact h a ha (fun v => (hle v).trans (min_le_left _ _))

abbrev GoodPattern (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :=
  {b : Pattern p N B // Avoid p N s (fun v => (b v.1 v.2 : ℕ))}

instance goodPatternFintype (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :
    Fintype (GoodPattern p N s B) := by classical exact Subtype.fintype _

abbrev DegreeCellProduct (B : ℕ) (b : Pattern p N B) (d : Fin p → ℕ) :=
  ∀ i : Fin p, {f : Fin (N i + 1) → ℕ //
    (∀ j, min (f j) B = (b i j : ℕ)) ∧ ∑ j, f j = d i}

def partitionEquiv (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (d : Fin p → ℕ) :
    {e : Var p N →₀ ℕ // Finsupp.weight (Hilbert.blockWeight p N) e = d ∧
      ∀ a ∈ s, ¬ a ≤ e} ≃
    Σ b : GoodPattern p N s B, DegreeCellProduct p N B b.val d where
  toFun e :=
    ⟨⟨fun i j => ⟨min (e.val ⟨i,j⟩) B, Nat.lt_succ_of_le (min_le_right _ _)⟩,
      (avoid_cap p N s B hB e.val).mpr e.property.2⟩,
      fun i => ⟨fun j => e.val ⟨i,j⟩, (fun j => rfl), by
        rw [← weight_apply p N e.val i, e.property.1]⟩⟩
  invFun q :=
    ⟨Finsupp.equivFunOnFinite.symm (fun v => (q.2 v.1).val v.2), by
      constructor
      · funext i
        rw [weight_apply]
        exact (q.2 i).property.2
      · intro a ha hae
        apply q.1.property a ha
        intro v
        have h := (q.2 v.1).property.1 v.2
        change a v ≤ (q.1.val v.1 v.2 : ℕ)
        rw [← h]
        exact le_min (hae v) (hB a ha v)⟩
  left_inv e := by
    apply Subtype.ext
    ext v
    rfl
  right_inv q := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i j
      apply Fin.ext
      exact (q.2 i).property.1 j
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      apply (Subtype.heq_iff_coe_eq ?_).mpr
      · rfl
      intro f
      change ((∀ j, min (f j) B = min ((q.2 i).val j) B) ∧ ∑ j, f j = d i) ↔
        ((∀ j, min (f j) B = (q.1.val i j : ℕ)) ∧ ∑ j, f j = d i)
      simp only [(q.2 i).property.1]

theorem partition_card (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (d : Fin p → ℕ) :
    Nat.card {e : Var p N →₀ ℕ // Finsupp.weight (Hilbert.blockWeight p N) e = d ∧
      ∀ a ∈ s, ¬ a ≤ e} =
    ∑ b : GoodPattern p N s B, ∏ i : Fin p,
      Nat.card {f : Cell B (b.val i) // ∑ j, f.val j = d i} := by
  classical
  rw [Nat.card_congr (partitionEquiv p N s B hB d), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [DegreeCellProduct, Nat.card_pi]
  exact Finset.prod_congr rfl (fun i _ => Nat.card_congr (flatCellEquiv B (b.val i) (d i)))

abbrev Active (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :=
  {b : GoodPattern p N s B // ∀ i, 0 < Nat.card (Free B (b.val i))}

instance activeFintype (s : Finset (Var p N →₀ ℕ)) (B : ℕ) :
    Fintype (Active p N s B) := by classical exact Subtype.fintype _

theorem pattern_sum_bound (B : ℕ) (b : Pattern p N B) (i : Fin p) :
    (∑ j, (b i j : ℕ)) ≤ (N i + 1) * B := by
  calc
    _ ≤ ∑ _j : Fin (N i + 1), B := Finset.sum_le_sum (fun j _ => Nat.le_of_lt_succ (b i j).isLt)
    _ = _ := by simp

theorem eventual_partition_count (s : Finset (Var p N →₀ ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, ∀ v, a v ≤ B) (d : Fin p → ℕ)
    (hd : ∀ i, (N i + 1) * B < d i) :
    Nat.card {e : Var p N →₀ ℕ // Finsupp.weight (Hilbert.blockWeight p N) e = d ∧
      ∀ a ∈ s, ¬ a ≤ e} =
    ∑ b : Active p N s B, ∏ i : Fin p,
      (d i - (∑ j, (b.val.val i j : ℕ)) +
          (Nat.card (Free B (b.val.val i)) - 1)).choose
        (Nat.card (Free B (b.val.val i)) - 1) := by
  classical
  rw [partition_card p N s B hB d]
  calc
    _ = ∑ b : Active p N s B, ∏ i : Fin p,
        Nat.card {f : Cell B (b.val.val i) // ∑ j, f.val j = d i} := by
      apply Finset.sum_congr_set
        {b : GoodPattern p N s B | ∀ i, 0 < Nat.card (Free B (b.val i))}
      · intro b hb
        rfl
      · intro b hb
        simp only [Set.mem_setOf_eq, not_forall, Nat.not_lt, Nat.le_zero] at hb
        obtain ⟨i, hi⟩ := hb
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        exact degreeCell_card_zero B (b.val i) (d i)
          ((pattern_sum_bound p N B b.val i).trans_lt (hd i)) hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.prod_congr rfl
      intro i _
      exact degreeCell_card_pos B (b.val.val i) (d i)
        ((pattern_sum_bound p N B b.val.val i).trans (hd i).le) (b.property i)

end PhilipponMultiplicity.MonomialCells

end
end


section
-- Reused implementation: Solutions.PhilipponProductDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProductDegree

theorem top_mul {σ : Type*} (P Q : MvPolynomial σ ℚ) (a b : ℕ)
    (hP : P.totalDegree ≤ a) (hQ : Q.totalDegree ≤ b) :
    homogeneousComponent (a + b) (P * Q) =
      homogeneousComponent a P * homogeneousComponent b Q := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hd : d.degree = a + b
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    rintro ⟨e, f⟩ hef
    have hef' : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases he : coeff e P = 0
    · simp [he]
    by_cases hf : coeff f Q = 0
    · simp [hf]
    have he' : e.degree ≤ a := (le_totalDegree (mem_support_iff.mpr he)).trans hP
    have hf' : f.degree ≤ b := (le_totalDegree (mem_support_iff.mpr hf)).trans hQ
    have hsum : e.degree + f.degree = a + b := by
      rw [← map_add, hef', hd]
    have hea : e.degree = a := by omega
    have hfb : f.degree = b := by omega
    simp [hea, hfb]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨e, f⟩ hef
    have hef' : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases he : e.degree = a
    · by_cases hf : f.degree = b
      · exfalso
        apply hd
        rw [← hef', map_add, he, hf]
      · simp [hf]
    · simp [he]

theorem top_prod {σ ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℚ)
    (hP : ∀ i ∈ s, P i ≠ 0) :
    (∏ i ∈ s, P i).totalDegree = ∑ i ∈ s, (P i).totalDegree ∧
    homogeneousComponent (∏ i ∈ s, P i).totalDegree (∏ i ∈ s, P i) =
      ∏ i ∈ s, homogeneousComponent (P i).totalDegree (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hpi := hP i (Finset.mem_insert_self i s)
    have hps : ∀ j ∈ s, P j ≠ 0 := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    obtain ⟨hdeg, htop⟩ := ih hps
    have hprod : ∏ j ∈ s, P j ≠ 0 := Finset.prod_ne_zero_iff.mpr hps
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    rw [totalDegree_mul_of_isDomain hpi hprod]
    constructor
    · rw [hdeg]
    · rw [top_mul _ _ _ _ le_rfl le_rfl, htop]

theorem degree_fin_one (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem top_fin_one (P : MvPolynomial (Fin 1) ℚ) :
    homogeneousComponent P.totalDegree P =
      monomial (Finsupp.single 0 P.totalDegree) (coeff (Finsupp.single 0 P.totalDegree) P) := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_monomial]
  have hd : d.degree = P.totalDegree ↔ Finsupp.single 0 P.totalDegree = d := by
    rw [degree_fin_one]
    constructor
    · intro h
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h.symm
    · intro h
      rw [← h, Finsupp.single_eq_same]
  by_cases h : d.degree = P.totalDegree
  · rw [if_pos h, if_pos (hd.mp h), ← hd.mp h]
  · rw [if_neg h, if_neg (mt hd.mpr h)]

theorem degree_rename_single {ι : Type*} (i : ι) (P : MvPolynomial (Fin 1) ℚ) :
    (rename (fun _ => i) P).totalDegree = P.totalDegree := by
  have h := (weightedTotalDegree_rename_of_injective
      (w := (1 : ι → ℕ)) (P := P)
      (show Function.Injective (fun _ : Fin 1 => i) from fun _ _ _ => Subsingleton.elim _ _))
  change weightedTotalDegree 1 _ = weightedTotalDegree 1 _ at h
  simpa only [weightedTotalDegree_one] using h

theorem eval_top_fin_one (P : MvPolynomial (Fin 1) ℚ) (d : Fin 1 → ℚ) :
    eval d (homogeneousComponent P.totalDegree P) =
      coeff (Finsupp.single 0 P.totalDegree) P * d 0 ^ P.totalDegree := by
  conv_lhs => rw [top_fin_one P]
  rw [eval_monomial, Finsupp.prod_single_index]
  simp

/-- Philippon's factorial normalization for a product of polynomials in separate
variables. Zero factors are included, so no nonemptiness premise is needed. -/
theorem normalized_product {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin 1) ℚ) (d : ι → ℚ) :
    let Q := ∏ i, rename (fun _ : Fin 1 => i) (P i)
    eval d ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) =
      (Q.totalDegree.factorial : ℚ) / (∏ i, ((P i).totalDegree.factorial : ℚ)) *
        (∏ i, eval (fun _ => 1)
          (((P i).totalDegree.factorial : ℚ) •
            homogeneousComponent (P i).totalDegree (P i))) *
        ∏ i, d i ^ (P i).totalDegree := by
  classical
  dsimp only
  by_cases hP : ∀ i, P i ≠ 0
  · have hrename (i : ι) : rename (fun _ : Fin 1 => i) (P i) ≠ 0 := by
      exact fun h => hP i ((rename_injective _ (fun _ _ _ => Subsingleton.elim _ _)) h)
    have htop := (top_prod Finset.univ
      (fun i => rename (fun _ : Fin 1 => i) (P i)) (fun i _ => hrename i)).2
    rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, htop, map_prod]
    simp_rw [degree_rename_single, ← rename_homogeneousComponent, eval_rename,
      eval_top_fin_one, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_top_fin_one]
    simp only [Function.comp_apply, one_pow, mul_one, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hfact : (∏ i, ((P i).totalDegree.factorial : ℚ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact_mod_cast Nat.factorial_ne_zero (P i).totalDegree
    field_simp
  · push Not at hP
    obtain ⟨i, hi⟩ := hP
    have hprod : (∏ j, rename (fun _ : Fin 1 => j) (P j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi, map_zero]
    have hprod' : (∏ j, eval (fun _ => (1 : ℚ))
        (((P j).totalDegree.factorial : ℚ) •
          homogeneousComponent (P j).totalDegree (P j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hprod, hprod']
    simp

end PhilipponMultiplicity.ProductDegree


namespace PhilipponMultiplicity
open SectionThree

/-- The product Hilbert polynomial identity supplies exactly the geometric input
to Lemma 3.4. The remaining factorial and leading-term calculation is proved here. -/
theorem lemma_3_4_of_product_hilbertPolynomial
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (V : ∀ i : M.FactorIndex, ProjectiveSubvariety K (M.ambientDimension i))
    (hprod : Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension
        (M.vanishingIdeal (productCarrier M V)) =
      ∏ i, MvPolynomial.rename (fun _ : Fin 1 => i)
        (Hilbert.hilbertPolynomial K 1 (fun _ => M.ambientDimension i)
          ((projectiveSpace K (M.ambientDimension i)).vanishingIdeal
            (V i).carrierInSingleFactor)))
    (d : M.FactorIndex → ℕ) :
    locusDegreeValue M (productCarrier M V) d =
      ((locusDimension M (productCarrier M V)).factorial : ℚ) /
        (∏ i, ((V i).dimension.factorial : ℚ)) *
        (∏ i, (V i).degree) * ∏ i, (d i : ℚ) ^ (V i).dimension := by
  unfold locusDegreeValue locusDimension idealDegreeValue idealDimension
    ProjectiveSubvariety.dimension ProjectiveSubvariety.degree
    idealDegreeValue idealDimension Hilbert.degreeValue Hilbert.degreeForm
  rw [hprod]
  exact ProductDegree.normalized_product _ _

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponBinomialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.BinomialPolynomial

def oneVariable (q a : ℕ) : MvPolynomial (Fin 1) ℚ :=
  (uniqueAlgEquiv ℚ (Fin 1)).symm (Polynomial.preHilbertPoly ℚ q a)

theorem oneVariable_coeff (q a : ℕ) (b : Fin 1 →₀ ℕ) :
    coeff b (oneVariable q a) = (Polynomial.preHilbertPoly ℚ q a).coeff (b 0) :=
  coeff_uniqueAlgEquiv_symm ℚ _ _

theorem oneVariable_degree (q a : ℕ) : (oneVariable q a).totalDegree = q := by
  classical
  apply le_antisymm
  · change (oneVariable q a).support.sup (fun b : Fin 1 →₀ ℕ => b.sum (fun _ e => e)) ≤ q
    apply Finset.sup_le
    intro b hb
    have h := mem_support_iff.mp hb
    rw [oneVariable_coeff] at h
    have ht := Polynomial.le_natDegree_of_ne_zero h
    rw [Polynomial.natDegree_preHilbertPoly] at ht
    simpa [Finsupp.sum_fintype] using ht
  · have hcoeff : coeff (Finsupp.single 0 q) (oneVariable q a) ≠ 0 := by
      rw [oneVariable_coeff, Finsupp.single_eq_same, Polynomial.coeff_preHilbertPoly_self]
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero q)
    simpa using le_totalDegree (mem_support_iff.mpr hcoeff)

theorem oneVariable_top (q a : ℕ) :
    homogeneousComponent q (oneVariable q a) =
      monomial (Finsupp.single 0 q) (q.factorial : ℚ)⁻¹ := by
  have h := ProductDegree.top_fin_one (oneVariable q a)
  simpa only [oneVariable_degree, oneVariable_coeff, Finsupp.single_eq_same,
    Polynomial.coeff_preHilbertPoly_self] using h

def block {ι : Type*} (i : ι) (q a : ℕ) : MvPolynomial ι ℚ :=
  rename (fun _ : Fin 1 => i) (oneVariable q a)

theorem block_degree {ι : Type*} (i : ι) (q a : ℕ) : (block i q a).totalDegree = q := by
  rw [block, ProductDegree.degree_rename_single, oneVariable_degree]

theorem block_top {ι : Type*} (i : ι) (q a : ℕ) :
    homogeneousComponent q (block i q a) =
      monomial (Finsupp.single i q) (q.factorial : ℚ)⁻¹ := by
  rw [block, ← rename_homogeneousComponent, oneVariable_top, rename_monomial]
  simp

theorem block_ne_zero {ι : Type*} (i : ι) (q a : ℕ) : block i q a ≠ 0 := by
  intro h
  have hh := block_top i q a
  rw [h, map_zero] at hh
  have hn : (monomial (Finsupp.single i q) (q.factorial : ℚ)⁻¹ : MvPolynomial ι ℚ) ≠ 0 := by
    simp [Nat.factorial_ne_zero]
  exact hn hh.symm

theorem block_eval {ι : Type*} (i : ι) (q a : ℕ) (d : ι → ℕ) (ha : a ≤ d i) :
    eval (fun i => (d i : ℚ)) (block i q a) = ((d i - a + q).choose q : ℚ) := by
  rw [block, eval_rename]
  change MvPolynomial.eval₂ (RingHom.id ℚ) _
    ((uniqueAlgEquiv ℚ (Fin 1)).symm _) = _
  rw [eval₂_uniqueAlgEquiv_symm]
  exact Polynomial.preHilbertPoly_eq_choose_sub_add ℚ q ha

def product {ι : Type*} [Fintype ι] (q a : ι → ℕ) : MvPolynomial ι ℚ :=
  ∏ i, block i (q i) (a i)

def exponent {ι : Type*} [Fintype ι] (q : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm q

theorem prod_monomial {ι σ : Type*} (s : Finset ι) (e : ι → σ →₀ ℕ) (c : ι → ℚ) :
    (∏ i ∈ s, monomial (e i) (c i) : MvPolynomial σ ℚ) =
      monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, monomial_mul]

theorem product_degree {ι : Type*} [Fintype ι] (q a : ι → ℕ) :
    (product q a).totalDegree = ∑ i, q i := by
  have h := (ProductDegree.top_prod Finset.univ
    (fun i => block i (q i) (a i)) (fun i _ => block_ne_zero i _ _)).1
  simpa only [product, block_degree] using h

theorem product_top {ι : Type*} [Fintype ι] (q a : ι → ℕ) :
    homogeneousComponent (∑ i, q i) (product q a) =
      monomial (exponent q) (∏ i, (q i |>.factorial : ℚ)⁻¹) := by
  classical
  rw [← product_degree q a]
  have h := (ProductDegree.top_prod Finset.univ
    (fun i => block i (q i) (a i)) (fun i _ => block_ne_zero i _ _)).2
  simp only [block_degree, block_top] at h
  change homogeneousComponent (product q a).totalDegree (product q a) = _ at h
  rw [h, prod_monomial]
  have he : (∑ i, Finsupp.single i (q i)) = exponent q := by
    ext i
    simp [exponent, Finsupp.single_apply]
  rw [he]

theorem product_eval {ι : Type*} [Fintype ι] (q a d : ι → ℕ) (ha : ∀ i, a i ≤ d i) :
    eval (fun i => (d i : ℚ)) (product q a) =
      (∏ i, (d i - a i + q i).choose (q i) : ℕ) := by
  classical
  simp only [product, map_prod, Nat.cast_prod]
  exact Finset.prod_congr rfl (fun i _ => block_eval i _ _ _ (ha i))

/-- Positive leading monomials cannot cancel in a finite sum. -/
theorem sum_top_coefficients {ι J : Type*} [Fintype ι] [Fintype J]
    (q a : J → ι → ℕ) (N : ι → ℕ) (hq : ∀ j i, q j i ≤ N i) :
    let F := ∑ j, product (q j) (a j)
    (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧
    (∀ b : ι →₀ ℕ, (∃ i, N i < b i) →
      coeff b (homogeneousComponent F.totalDegree F) = 0) := by
  classical
  let F := ∑ j, product (q j) (a j)
  change (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧ _
  cases isEmpty_or_nonempty J with
  | inl h => simp [F]
  | inr h =>
    let n := Finset.univ.sup (fun j : J => ∑ i, q j i)
    have hqn (j : J) : (∑ i, q j i) ≤ n :=
      Finset.le_sup (f := fun j : J => ∑ i, q j i) (Finset.mem_univ j)
    have hpn (j : J) : (product (q j) (a j)).totalDegree ≤ n := by
      rw [product_degree]
      exact hqn j
    have hc (j : J) : 0 < ∏ i, ((q j i).factorial : ℚ)⁻¹ := by
      apply Finset.prod_pos
      intro i _
      exact inv_pos.mpr (by exact_mod_cast Nat.factorial_pos (q j i))
    have hpart (j : J) : homogeneousComponent n (product (q j) (a j)) =
        if (∑ i, q j i) = n then
          monomial (exponent (q j)) (∏ i, ((q j i).factorial : ℚ)⁻¹) else 0 := by
      split_ifs with he
      · rw [← he, product_top]
      · apply homogeneousComponent_eq_zero
        rw [product_degree]
        exact lt_of_le_of_ne (hqn j) he
    have hnn (j : J) (b : ι →₀ ℕ) :
        0 ≤ coeff b (homogeneousComponent n (product (q j) (a j))) := by
      rw [hpart]
      split_ifs
      · rw [coeff_monomial]
        split_ifs
        · exact (hc j).le
        · rfl
      · simp
    have hcoeff (b : ι →₀ ℕ) : coeff b (homogeneousComponent n F) =
        ∑ j, coeff b (homogeneousComponent n (product (q j) (a j))) := by
      simp only [F, map_sum, coeff_sum]
    have hFle : F.totalDegree ≤ n := totalDegree_finsetSum_le (fun j _ => hpn j)
    obtain ⟨j, hj, hjn⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun j : J => ∑ i, q j i)
    have hjn' : (∑ i, q j i) = n := hjn.symm
    have hp : 0 < coeff (exponent (q j)) (homogeneousComponent n F) := by
      rw [hcoeff]
      have hpos : 0 < coeff (exponent (q j))
          (homogeneousComponent n (product (q j) (a j))) := by
        rw [hpart, if_pos hjn', coeff_monomial, if_pos rfl]
        exact hc j
      exact hpos.trans_le (Finset.single_le_sum (fun k _ => hnn k _) hj)
    have hFge : n ≤ F.totalDegree := by
      by_contra! hlt
      rw [homogeneousComponent_eq_zero n F hlt, coeff_zero] at hp
      exact (lt_irrefl 0) hp
    have hFn : F.totalDegree = n := le_antisymm hFle hFge
    change (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧
      (∀ b : ι →₀ ℕ, (∃ i, N i < b i) →
        coeff b (homogeneousComponent F.totalDegree F) = 0)
    rw [hFn]
    constructor
    · intro b
      rw [hcoeff]
      exact Finset.sum_nonneg (fun j _ => hnn j b)
    · intro b hb
      obtain ⟨i, hi⟩ := hb
      rw [hcoeff]
      apply Finset.sum_eq_zero
      intro j _
      rw [hpart]
      split_ifs
      · rw [coeff_monomial, if_neg]
        intro he
        have hiq : q j i = b i := congrArg (fun e : ι →₀ ℕ => e i) he
        have hqi := hq j i
        omega
      · simp

end PhilipponMultiplicity.BinomialPolynomial

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertFoundations

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

/-- A constructive Hilbert polynomial with its actual leading-coefficient data.
The proof applies to every homogeneous ideal, including nonreduced ideals. -/
theorem multigraded_hilbert_foundations
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F ∧
      (∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) ∧
      (∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
        coeff b (homogeneousComponent F.totalDegree F) = 0) := by
  classical
  obtain ⟨s, hs⟩ := multigraded_hilbert_function_standard_monomials K M I hI
  obtain ⟨B, hB⟩ := MonomialCells.exists_bound M.factorCount M.ambientDimension s
  let J := MonomialCells.Active M.factorCount M.ambientDimension s B
  let q (b : J) (i : M.FactorIndex) := Nat.card (MonomialCells.Free B (b.val.val i)) - 1
  let a (b : J) (i : M.FactorIndex) := ∑ j, (b.val.val i j : ℕ)
  let F := ∑ b : J, BinomialPolynomial.product (q b) (a b)
  have hq (b : J) (i : M.FactorIndex) : q b i ≤ M.ambientDimension i := by
    have h := Nat.card_le_card_of_injective
      (fun x : MonomialCells.Free B (b.val.val i) => x.val) Subtype.val_injective
    rw [Nat.card_fin] at h
    dsimp [q]
    omega
  have ht := BinomialPolynomial.sum_top_coefficients q a M.ambientDimension hq
  refine ⟨F, ?_, ht⟩
  refine ⟨fun i => (M.ambientDimension i + 1) * B + 1, ?_⟩
  intro d hd
  have hd' (i : M.FactorIndex) : (M.ambientDimension i + 1) * B < d i := by
    exact Nat.lt_of_succ_le (hd i)
  have ha (b : J) (i : M.FactorIndex) : a b i ≤ d i :=
    (MonomialCells.pattern_sum_bound M.factorCount M.ambientDimension B b.val.val i).trans
      (hd' i).le
  change eval (fun i => (d i : ℚ)) (∑ b : J, BinomialPolynomial.product (q b) (a b)) = _
  rw [map_sum, hs d, MonomialCells.eventual_partition_count
    M.factorCount M.ambientDimension s B hB d hd', Nat.cast_sum]
  exact Finset.sum_congr rfl (fun b _ => BinomialPolynomial.product_eval (q b) (a b) d (ha b))

theorem multigraded_hilbert_polynomial_exists
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    ∃ F, Hilbert.IsHilbertPolynomial K M.factorCount M.ambientDimension I F := by
  obtain ⟨F, hF, _⟩ := multigraded_hilbert_foundations K M I hI
  exact ⟨F, hF⟩

theorem multigraded_hilbert_polynomial_top_coefficients
    (K : Type*) [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I) :
    (∀ b, 0 ≤ coeff b (homogeneousComponent
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
      (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I))) ∧
    (∀ b : M.FactorIndex →₀ ℕ, (∃ i, M.ambientDimension i < b i) →
      coeff b (homogeneousComponent
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I).totalDegree
        (Hilbert.hilbertPolynomial K M.factorCount M.ambientDimension I)) = 0) := by
  obtain ⟨F, hF, htop⟩ := multigraded_hilbert_foundations K M I hI
  rw [Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial K M.factorCount M.ambientDimension I hF]
  exact htop

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponFiltrationPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertPolynomial_top :
    hilbertPolynomial K M.factorCount M.ambientDimension (⊤ : Ideal M.CoordinateRing) = 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0, fun d hd => ?_⟩
  simp only [map_zero, hilbertFunction]
  letI : Subsingleton (quotientPiece K M.factorCount M.ambientDimension
      (⊤ : Ideal M.CoordinateRing) d) := inferInstance
  rw [Module.finrank_zero_of_subsingleton]
  rfl

theorem hilbertPolynomial_colon_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    hilbertPolynomial K M.factorCount M.ambientDimension I =
      hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) +
        aeval (fun i => X i - C (D i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P})) := by
  let J := I ⊔ Ideal.span {P}
  let Q := I.colon {P}
  obtain ⟨a, ha⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension J
    (multigraded_hilbert_polynomial_exists K M J (homogeneous_sup_span M I hI P D hP))
  obtain ⟨b, hb⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q (homogeneous_colon M I hI P D hP))
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨D + a + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have han : ∀ i, a i ≤ n i := by intro i; have := hn i; change D i + a i + b i ≤ n i at this; omega
  have hbsub : ∀ i, b i ≤ (n - D) i := by
    intro i; have := hn i; change D i + a i + b i ≤ n i at this; change b i ≤ n i - D i; omega
  have hnsub : D + (n - D) = n := by
    funext i; exact Nat.add_sub_of_le (hDn i)
  have heval (F : MvPolynomial M.FactorIndex ℚ) :
      eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
        eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    clear ha hb
    induction F using MvPolynomial.induction_on with
    | C c => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
      simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
      simp only [Pi.sub_apply, Nat.cast_sub (hDn i)]
  rw [map_add, heval, ha n han, hb (n - D) hbsub]
  have h := hilbertFunction_colon_add M I hI P D hP (n - D)
  rw [hnsub] at h
  exact_mod_cast h

/-- A finite prime filtration gives a sum of shifted prime Hilbert polynomials.
The chain is supplied explicitly, so the result also applies to every later
chosen filtration, not only to a particular existence witness. -/
theorem hilbertPolynomial_filtration_sum (n : ℕ)
    (J : Fin (n + 1) → Ideal M.CoordinateRing)
    (P : Fin n → M.CoordinateRing) (D : Fin n → M.FactorIndex → ℕ)
    (hhom : ∀ j, IsMultihomogeneousIdeal M (J j))
    (hstep : ∀ j, M.IsHomogeneous (P j) (D j) ∧
      J j.succ = J j.castSucc ⊔ Ideal.span {P j})
    (hlast : J (Fin.last n) = ⊤) :
    hilbertPolynomial K M.factorCount M.ambientDimension (J 0) =
      ∑ j, aeval (fun i => X i - C (D j i : ℚ))
        (hilbertPolynomial K M.factorCount M.ambientDimension
          ((J j.castSucc).colon {P j})) := by
  induction n with
  | zero =>
    have heq : J 0 = ⊤ := hlast
    rw [heq]
    simpa using hilbertPolynomial_top M
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have htail := ih (fun j => J j.succ) (fun j => P j.succ) (fun j => D j.succ)
      (fun j => hhom j.succ) (fun j => by simpa using hstep j.succ) hlast
    have hfirst := hilbertPolynomial_colon_add M (J 0) (hhom 0) (P 0) (D 0) (hstep 0).1
    have hzero : J (Fin.succ 0) = J 0 ⊔ Ideal.span {P 0} := (hstep 0).2
    rw [← hzero] at hfirst
    rw [htail] at hfirst
    simpa only [Fin.castSucc_zero, Fin.castSucc_succ, add_comm] using hfirst

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponRelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_antitone (I J : Ideal M.CoordinateRing) (hIJ : I ≤ J)
    (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension J d ≤
      hilbertFunction K M.factorCount M.ambientDimension I d := by
  let q := Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) hIJ
  let f : quotientPiece K M.factorCount M.ambientDimension I d →ₗ[K]
      quotientPiece K M.factorCount M.ambientDimension J d :=
    (q.toLinearMap.domRestrict _).codRestrict _ (by
      rintro ⟨x, P, hP, rfl⟩
      exact ⟨P, hP, rfl⟩)
  apply LinearMap.finrank_le_finrank_of_surjective (f := f)
  rintro ⟨x, P, hP, rfl⟩
  exact ⟨⟨Ideal.Quotient.mk I P, ⟨P, hP, rfl⟩⟩, rfl⟩

theorem hilbertPolynomial_zero_of_le (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hIJ : I ≤ J)
    (hz : hilbertPolynomial K M.factorCount M.ambientDimension I = 0) :
    hilbertPolynomial K M.factorCount M.ambientDimension J = 0 := by
  have hex := hilbertPolynomial_spec K M.factorCount M.ambientDimension I
    (multigraded_hilbert_polynomial_exists K M I hI)
  rw [hz] at hex
  obtain ⟨a, ha⟩ := hex
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨a, fun d hd => ?_⟩
  have hzero : hilbertFunction K M.factorCount M.ambientDimension I d = 0 := by
    have h := ha d hd
    simpa using h.symm
  have hJzero : hilbertFunction K M.factorCount M.ambientDimension J d = 0 :=
    Nat.eq_zero_of_le_zero (hzero ▸ hilbertFunction_antitone M I J hIJ d)
  rw [map_zero, hJzero, Nat.cast_zero]

theorem relevant_variables (Q : Ideal M.CoordinateRing)
    (hQ : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ v : ∀ i, Fin (M.ambientDimension i + 1), ∀ i, X ⟨i, v i⟩ ∉ Q := by
  classical
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1), X ⟨i, j⟩ ∉ Q := by
    by_contra! h
    apply hQ
    apply (iInf_le (blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [blockIdeal, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact h j
  exact Classical.axiomOfChoice hx

theorem variable_product_homogeneous (v : ∀ i, Fin (M.ambientDimension i + 1))
    (d : M.FactorIndex → ℕ) :
    M.IsHomogeneous (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) d := by
  classical
  apply (M.degreePiece_iff _ d).mp
  let w := blockWeight M.factorCount M.ambientDimension
  have hx (i : M.FactorIndex) : (X ⟨i, v i⟩ : M.CoordinateRing).IsWeightedHomogeneous w
      (w ⟨i, v i⟩) := isWeightedHomogeneous_X K w ⟨i, v i⟩
  have h := IsWeightedHomogeneous.prod (w := w) Finset.univ
    (fun i => (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i)
    (fun i => d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩)
    (fun i _ => (hx i).pow (d i))
  have heq : (∑ i, d i • blockWeight M.factorCount M.ambientDimension ⟨i, v i⟩) = d := by
    funext i
    simp [blockWeight, Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  rwa [heq] at h

theorem variable_product_notMem (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (v : ∀ i, Fin (M.ambientDimension i + 1)) (hv : ∀ i, X ⟨i, v i⟩ ∉ Q)
    (d : M.FactorIndex → ℕ) : (∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i) ∉ Q := by
  classical
  letI := hQ
  intro h
  obtain ⟨i, hi, hip⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hv i (hQ.mem_of_pow_mem _ hip)

/-- A relevant homogeneous prime has a nonzero actual Hilbert polynomial. -/
theorem relevant_prime_hilbertPolynomial_ne_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro hz
  have hex := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  rw [hz] at hex
  obtain ⟨d, hd⟩ := hex
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ d i
  have hP : P ∉ Q := variable_product_notMem M Q hQ v hv d
  let x : quotientPiece K M.factorCount M.ambientDimension Q d :=
    ⟨Ideal.Quotient.mk Q P, P, (M.degreePiece_iff P d).mpr (variable_product_homogeneous M v d), rfl⟩
  have hx : x ≠ 0 := by
    intro h
    exact hP (Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h))
  letI : Nontrivial (quotientPiece K M.factorCount M.ambientDimension Q d) :=
    ⟨⟨x, 0, hx⟩⟩
  have hpos := Module.finrank_pos (R := K)
    (M := quotientPiece K M.factorCount M.ambientDimension Q d)
  have heq := hd d (fun _ => le_rfl)
  change (MvPolynomial.eval _ (0 : MvPolynomial M.FactorIndex ℚ)) = _ at heq
  rw [map_zero] at heq
  have hzero : hilbertFunction K M.factorCount M.ambientDimension Q d = 0 := by exact_mod_cast heq.symm
  exact (Nat.ne_of_gt hpos) hzero

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertPieceGrowth

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- For a relevant homogeneous prime, multiplying by a selected nonzero
coordinate in each block makes the actual Hilbert function monotone. -/
theorem hilbertFunction_mono_relevant_prime (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    Monotone (hilbertFunction K M.factorCount M.ambientDimension Q) := by
  classical
  obtain ⟨v, hv⟩ := relevant_variables M Q hrel
  intro d e hde
  let P : M.CoordinateRing := ∏ i, (X ⟨i, v i⟩ : M.CoordinateRing) ^ (e - d) i
  have hP : M.IsHomogeneous P (e - d) := variable_product_homogeneous M v (e - d)
  have hPnot : P ∉ Q := variable_product_notMem M Q hQ v hv (e - d)
  have hcolon : Q.colon {P} = Q := by
    apply le_antisymm ?_ Ideal.le_colon
    intro f hf
    have hmul : f * P ∈ Q := by
      simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hf
    exact (hQ.mem_or_mem hmul).resolve_right hPnot
  have h := hilbertFunction_colon_add M Q hhom P (e - d) hP d
  rw [hcolon, tsub_add_cancel_of_le hde] at h
  omega

/-- One fixed shift bounds every graded piece by a value of the eventual
Hilbert polynomial, including degrees on coordinate boundaries. -/
theorem hilbertFunction_le_shifted_polynomial_relevant_prime
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ d₀ : M.FactorIndex → ℕ, ∀ d : M.FactorIndex → ℕ,
      (hilbertFunction K M.factorCount M.ambientDimension Q d : ℚ) ≤
        eval (fun i => ((d + d₀) i : ℚ))
          (hilbertPolynomial K M.factorCount M.ambientDimension Q) := by
  obtain ⟨d₀, hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  refine ⟨d₀, fun d => ?_⟩
  rw [hd₀ (d + d₀) (fun i => Nat.le_add_left _ _)]
  exact_mod_cast hilbertFunction_mono_relevant_prime M Q hQ hhom hrel
    (show d ≤ d + d₀ from fun i => Nat.le_add_right _ _)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertFiltration

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private def PhilipponHilbertFiltration_quotientProjection (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d : M.FactorIndex → ℕ) :
    (M.CoordinateRing ⧸ I) →ₗ[K] (M.CoordinateRing ⧸ I) :=
  (I.restrictScalars K).liftQ
    ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
      (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d)) (by
        intro P hP
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI P hP d))

private theorem PhilipponHilbertFiltration_quotientProjection_on_piece (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (d e : M.FactorIndex → ℕ)
    {x : M.CoordinateRing ⧸ I} (hx : x ∈ quotientPiece K M.factorCount M.ambientDimension I e) :
    PhilipponHilbertFiltration_quotientProjection M I hI d x = if d = e then x else 0 := by
  classical
  obtain ⟨P, hP, rfl⟩ := hx
  change Ideal.Quotient.mk I
    (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d P) = _
  rw [weightedHomogeneousComponent_of_mem hP]
  split_ifs <;> simp

/-- Distinct actual multidegree pieces of a homogeneous quotient are independent. -/
theorem quotientPiece_iSupIndep (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    iSupIndep (quotientPiece K M.factorCount M.ambientDimension I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hz d hd
  have h := congrArg (PhilipponHilbertFiltration_quotientProjection M I hI d) hz
  rw [map_sum, map_zero] at h
  have heq : (∑ e ∈ s, PhilipponHilbertFiltration_quotientProjection M I hI d (v e)) = v d := by
    rw [Finset.sum_eq_single d]
    · simpa using PhilipponHilbertFiltration_quotientProjection_on_piece M I hI d d (hv d hd)
    · intro e he hed
      rw [PhilipponHilbertFiltration_quotientProjection_on_piece M I hI d e (hv e he), if_neg (Ne.symm hed)]
    · exact fun hn => False.elim (hn hd)
  exact heq.symm.trans h

instance finite_piece_sum (I : Ideal M.CoordinateRing) (s : Finset (M.FactorIndex → ℕ)) :
    Module.Finite K (⨆ d ∈ s, quotientPiece K M.factorCount M.ambientDimension I d :
      Submodule K (M.CoordinateRing ⧸ I)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (⨆ d ∈ (∅ : Finset (M.FactorIndex → ℕ)),
        quotientPiece K M.factorCount M.ambientDimension I d :
        Submodule K (M.CoordinateRing ⧸ I)) = ⊥ := by simp
    rw [hz]
    infer_instance
  | @insert d s hd ih =>
    rw [Finset.iSup_insert]
    let := ih
    infer_instance

/-- The actual dimension of a finite sum of quotient pieces is their dimension sum. -/
theorem finrank_quotientPiece_sum (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (s : Finset (M.FactorIndex → ℕ)) :
    Module.finrank K (⨆ d ∈ s, quotientPiece K M.factorCount M.ambientDimension I d :
      Submodule K (M.CoordinateRing ⧸ I)) =
      ∑ d ∈ s, hilbertFunction K M.factorCount M.ambientDimension I d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert d s hd ih =>
    rw [Finset.iSup_insert, Finset.sum_insert hd]
    have hdis := (quotientPiece_iSupIndep M I hI).disjoint_biSup (y := (s : Set _)) hd
    have hzero : quotientPiece K M.factorCount M.ambientDimension I d ⊓
        (⨆ e ∈ s, quotientPiece K M.factorCount M.ambientDimension I e) = ⊥ := by
      simpa only [Finset.mem_coe] using hdis.eq_bot
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (quotientPiece K M.factorCount M.ambientDimension I d)
      (⨆ e ∈ s, quotientPiece K M.factorCount M.ambientDimension I e)
    rw [hzero, finrank_bot, add_zero, ih] at hdim
    exact hdim

theorem mem_multidegreesLe (n : ℕ) (d : M.FactorIndex → ℕ) :
    d ∈ multidegreesLe M n ↔ ∑ i, d i ≤ n := by
  classical
  simp only [multidegreesLe, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  intro i
  exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h

theorem sum_blockWeight (e : M.Variable →₀ ℕ) :
    (∑ i, (Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e) i) = e.degree := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => M.blockWeight_apply e i)

theorem restrictTotalDegree_eq_piece_sum (n : ℕ) :
    restrictTotalDegree M.Variable K n =
      ⨆ d ∈ multidegreesLe M n, degreePiece K M.factorCount M.ambientDimension d := by
  classical
  apply le_antisymm
  · intro P hP
    have hdeg := (mem_restrictTotalDegree M.Variable n P).mp hP
    have hsum : (∑ e ∈ P.support, monomial e (coeff e P)) ∈
        ⨆ d ∈ multidegreesLe M n, degreePiece K M.factorCount M.ambientDimension d := by
      apply Submodule.sum_mem
      intro e he
      let d := Finsupp.weight (blockWeight M.factorCount M.ambientDimension) e
      have hd : d ∈ multidegreesLe M n := (mem_multidegreesLe M n d).mpr (by
        rw [sum_blockWeight]
        exact (le_totalDegree he).trans hdeg)
      apply Submodule.mem_iSup_of_mem d
      apply Submodule.mem_iSup_of_mem hd
      exact isWeightedHomogeneous_monomial _ _ _ rfl
    simpa only [← P.as_sum] using hsum
  · refine iSup_le fun d => iSup_le fun hd => ?_
    intro P hP
    apply (mem_restrictTotalDegree M.Variable n P).mpr
    exact (M.homogeneous_total ((M.degreePiece_iff P d).mp hP)).totalDegree_le.trans
      ((mem_multidegreesLe M n d).mp hd)

theorem degreeFiltration_eq_piece_sum (I : Ideal M.CoordinateRing) (n : ℕ) :
    degreeFiltration M I n =
      ⨆ d ∈ multidegreesLe M n, quotientPiece K M.factorCount M.ambientDimension I d := by
  unfold degreeFiltration
  rw [restrictTotalDegree_eq_piece_sum]
  simp only [Submodule.map_iSup, quotientPiece]

instance degreeFiltration_finite (I : Ideal M.CoordinateRing) (n : ℕ) :
    Module.Finite K (degreeFiltration M I n) := by
  unfold degreeFiltration
  infer_instance

/-- The standard total-degree filtration counts the actual multigraded pieces. -/
theorem cumulativeHilbertFunction_eq_sum (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (n : ℕ) :
    cumulativeHilbertFunction M I n =
      ∑ d ∈ multidegreesLe M n, hilbertFunction K M.factorCount M.ambientDimension I d := by
  unfold cumulativeHilbertFunction
  rw [degreeFiltration_eq_piece_sum, finrank_quotientPiece_sum M I hI]

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertGrowthBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The diagonal Hilbert function bounds the dimension of the actual
total-degree filtration, with explicit constants and no eventual threshold. -/
theorem cumulativeHilbertFunction_diagonal_bounds
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) (n : ℕ) :
    cumulativeHilbertFunction M Q n ≤
        (n + 1) ^ M.factorCount *
          hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) ∧
      (n + 1) ^ M.factorCount *
          hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) ≤
        cumulativeHilbertFunction M Q (2 * M.factorCount * n) := by
  classical
  let H := hilbertFunction K M.factorCount M.ambientDimension Q
  have hmono : Monotone H := hilbertFunction_mono_relevant_prime M Q hQ hhom hrel
  have hic : (Finset.Iic (fun _ : M.FactorIndex => n)).card = (n + 1) ^ M.factorCount := by
    simp [Pi.card_Iic, Nat.card_Iic, MultiProjectiveSpace.FactorIndex]
  have hcc : (Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n)).card =
      (n + 1) ^ M.factorCount := by
    have hnat : 2 * n + 1 - n = n + 1 := by omega
    simp [Pi.card_Icc, Nat.card_Icc, hnat, MultiProjectiveSpace.FactorIndex]
  constructor
  · rw [cumulativeHilbertFunction_eq_sum M Q hhom]
    calc
      ∑ d ∈ multidegreesLe M n, H d ≤ ∑ d ∈ Finset.Iic (fun _ => n), H d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro _ _ _; exact Nat.zero_le _
      _ ≤ ∑ _d ∈ Finset.Iic (fun _ : M.FactorIndex => n), H (fun _ => n) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hmono (Finset.mem_Iic.mp hd)
      _ = (n + 1) ^ M.factorCount * H (fun _ => n) := by
        rw [Finset.sum_const, nsmul_eq_mul, hic]
        simp
  · rw [cumulativeHilbertFunction_eq_sum M Q hhom]
    have hsub : Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n) ⊆
        multidegreesLe M (2 * M.factorCount * n) := by
      intro d hd
      apply (mem_multidegreesLe M _ d).mpr
      have h := Finset.sum_le_sum (s := Finset.univ)
        (fun i _ => (Finset.mem_Icc.mp hd).2 i)
      have hs : (∑ _i : M.FactorIndex, 2 * n) = 2 * M.factorCount * n := by
        simp [MultiProjectiveSpace.FactorIndex]
        ring
      exact h.trans_eq hs
    calc
      (n + 1) ^ M.factorCount * H (fun _ => n) =
          ∑ _d ∈ Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n), H (fun _ => n) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcc]
        simp
      _ ≤ ∑ d ∈ Finset.Icc (fun _ : M.FactorIndex => n) (fun _ => 2 * n), H d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hmono (Finset.mem_Icc.mp hd).1
      _ ≤ ∑ d ∈ multidegreesLe M (2 * M.factorCount * n), H d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro _ _ _; exact Nat.zero_le _

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponDiagonalHilbert

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem diagonalPolynomial_eq_sum {ι : Type*} (F : MvPolynomial ι ℚ) :
    eval₂ Polynomial.C (fun _ => Polynomial.X) F =
      ∑ e ∈ F.support, Polynomial.monomial e.degree (coeff e F) := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [eval₂_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval₂_monomial]
  have hp : e.prod (fun _ k => (Polynomial.X : Polynomial ℚ) ^ k) =
      Polynomial.X ^ e.degree := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [hp, Polynomial.C_mul_X_pow_eq_monomial]

/-- Nonnegative top coefficients prevent cancellation on the diagonal. -/
theorem diagonalPolynomial_degree_and_leadingCoeff {ι : Type*}
    (F : MvPolynomial ι ℚ) (hF : F ≠ 0)
    (hpos : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F) :
    (eval₂ Polynomial.C (fun _ => Polynomial.X) F).natDegree = F.totalDegree ∧
      0 < (eval₂ Polynomial.C (fun _ => Polynomial.X) F).leadingCoeff := by
  classical
  let P := eval₂ Polynomial.C (fun _ => Polynomial.X) F
  have hle : P.natDegree ≤ F.totalDegree := by
    dsimp only [P]
    rw [diagonalPolynomial_eq_sum]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro e he
    exact (Polynomial.natDegree_monomial_le (coeff e F)).trans (le_totalDegree he)
  have hcoef : 0 < P.coeff F.totalDegree := by
    dsimp only [P]
    rw [diagonalPolynomial_eq_sum, Polynomial.finsetSum_coeff]
    obtain ⟨e, he, hdeg⟩ := Finset.exists_mem_eq_sup F.support
      (support_nonempty.mpr hF) Finsupp.degree
    change F.totalDegree = e.degree at hdeg
    have hdeg' : e.degree = F.totalDegree := hdeg.symm
    apply Finset.sum_pos'
    · intro b hb
      rw [Polynomial.coeff_monomial]
      split_ifs with h
      · exact hpos b h
      · exact le_rfl
    · refine ⟨e, he, ?_⟩
      rw [Polynomial.coeff_monomial, if_pos hdeg']
      exact lt_of_le_of_ne (hpos e hdeg') (Ne.symm (mem_support_iff.mp he))
  have hdeg : P.natDegree = F.totalDegree :=
    le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (ne_of_gt hcoef))
  refine ⟨hdeg, ?_⟩
  change 0 < P.leadingCoeff
  simpa only [Polynomial.leadingCoeff, hdeg] using hcoef

theorem diagonalPolynomial_eval {ι : Type*} (F : MvPolynomial ι ℚ) (x : ℚ) :
    (eval₂ Polynomial.C (fun _ => Polynomial.X) F).eval x = eval (fun _ => x) F := by
  classical
  rw [diagonalPolynomial_eq_sum, Polynomial.eval_finsetSum]
  conv_rhs => rw [F.as_sum]
  rw [eval_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [Polynomial.eval_monomial, eval_monomial, Finsupp.prod,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

/-- The diagonal of the actual Hilbert function eventually has precisely
the original total degree and a positive leading coefficient. -/
theorem exists_diagonal_hilbertPolynomial
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ P : Polynomial ℚ, P.natDegree = SectionThree.idealDimension M Q ∧
      0 < P.leadingCoeff ∧ ∃ N : ℕ, ∀ n ≥ N,
        P.eval (n : ℚ) =
          (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension Q
  have hF : F ≠ 0 := relevant_prime_hilbertPolynomial_ne_zero M Q hQ hhom hrel
  have htop : ∀ e, e.degree = F.totalDegree → 0 ≤ coeff e F := by
    intro e he
    have h := (multigraded_hilbert_polynomial_top_coefficients K M Q hhom).1 e
    rwa [coeff_homogeneousComponent, if_pos he] at h
  obtain ⟨hdeg, hpos⟩ := diagonalPolynomial_degree_and_leadingCoeff F hF htop
  refine ⟨eval₂ Polynomial.C (fun _ => Polynomial.X) F, hdeg, hpos, ?_⟩
  obtain ⟨d₀, hd₀⟩ := hilbertPolynomial_spec K M.factorCount M.ambientDimension Q
    (multigraded_hilbert_polynomial_exists K M Q hhom)
  refine ⟨Finset.univ.sup d₀, fun n hn => ?_⟩
  rw [diagonalPolynomial_eval]
  apply hd₀
  intro i
  exact (Finset.le_sup (Finset.mem_univ i)).trans hn

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertGrowthExponent

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

theorem polynomial_eventually_two_sided (P : Polynomial ℚ) (hpos : 0 < P.leadingCoeff) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℚ) ^ P.natDegree ≤ P.eval (n : ℚ) ∧
        P.eval (n : ℚ) ≤ C * (n : ℚ) ^ P.natDegree := by
  have hP : P ≠ 0 := by
    intro hz
    simpa [hz] using hpos
  have hdegree : P.degree = (Polynomial.X ^ P.natDegree : Polynomial ℚ).degree := by
    rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hP]
  have hlim := P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (Polynomial.X ^ P.natDegree) hdegree
  have hlim' : Tendsto (fun n : ℕ => P.eval (n : ℚ) / (n : ℚ) ^ P.natDegree)
      atTop (𝓝 P.leadingCoeff) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_natCast_atTop_atTop (R := ℚ))
  have hlo := (tendsto_order.mp hlim').1 (P.leadingCoeff / 2) (by linarith)
  have hhi := (tendsto_order.mp hlim').2 (2 * P.leadingCoeff) (by linarith)
  refine ⟨P.leadingCoeff / 2, 2 * P.leadingCoeff, by positivity, by positivity, ?_⟩
  filter_upwards [hlo, hhi, eventually_ge_atTop 1] with n hnlo hnhi hn
  have hnpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp := pow_pos hnpos P.natDegree
  exact ⟨(le_div_iff₀ hp).mp hnlo.le, (div_le_iff₀ hp).mp hnhi.le⟩

/-- The Hilbert-polynomial side of the prime dimension comparison:
the actual quotient filtration has matching polynomial growth bounds. -/
theorem cumulativeHilbertFunction_polynomial_bounds
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q) :
    ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
          (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤
          C * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) := by
  obtain ⟨P, hdeg, hpos, N₀, hP⟩ := exists_diagonal_hilbertPolynomial M Q hQ hhom hrel
  obtain ⟨c, C, hc, hC, hbounds⟩ := polynomial_eventually_two_sided P hpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbounds
  refine ⟨c, C, hc, hC, max N N₀, fun n hn => ?_⟩
  have hp := hN n ((le_max_left N N₀).trans hn)
  rw [hP n ((le_max_right N N₀).trans hn), hdeg] at hp
  obtain ⟨hupper, hlower⟩ := cumulativeHilbertFunction_diagonal_bounds M Q hQ hhom hrel n
  have hu : (cumulativeHilbertFunction M Q n : ℚ) ≤
      ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
        (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) := by
    exact_mod_cast hupper
  have hl : ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
        (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) ≤
      (cumulativeHilbertFunction M Q (2 * M.factorCount * n) : ℚ) := by
    exact_mod_cast hlower
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hn1 : (n : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ n
  have hpow (b : ℕ) : (n : ℚ) ^ b ≤ ((n + 1 : ℕ) : ℚ) ^ b :=
    pow_le_pow_left₀ hn0 hn1 b
  constructor
  · calc
      c * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) =
          (n : ℚ) ^ M.factorCount * (c * (n : ℚ) ^ SectionThree.idealDimension M Q) := by
        rw [pow_add]; ring
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (c * (n : ℚ) ^ SectionThree.idealDimension M Q) :=
        mul_le_mul_of_nonneg_right (hpow M.factorCount) (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (hilbertFunction K M.factorCount M.ambientDimension Q (fun _ => n) : ℚ) :=
        mul_le_mul_of_nonneg_left hp.1 (by positivity)
      _ ≤ _ := hl
  · calc
      (cumulativeHilbertFunction M Q n : ℚ) ≤ _ := hu
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (C * (n : ℚ) ^ SectionThree.idealDimension M Q) :=
        mul_le_mul_of_nonneg_left hp.2 (by positivity)
      _ ≤ ((n + 1 : ℕ) : ℚ) ^ M.factorCount *
          (C * ((n + 1 : ℕ) : ℚ) ^ SectionThree.idealDimension M Q) := by
        gcongr
      _ = _ := by rw [pow_add]; ring

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponGrowthExponentComparison

set_option autoImplicit false
set_option maxHeartbeats 500000
open Filter
noncomputable section

namespace PhilipponMultiplicity.Hilbert

/-- The elementary final comparison of polynomial growth exponents. -/
theorem exponent_le_of_eventual_power_bound {a b : ℕ} {c C : ℚ}
    (hc : 0 < c)
    (h : ∀ᶠ n : ℕ in atTop, c * (n : ℚ) ^ a ≤ C * (n : ℚ) ^ b) : a ≤ b := by
  by_contra hab
  have hba : b + 1 ≤ a := by omega
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C / c) (max (N : ℚ) 1))
  have hnN : N ≤ n := by
    exact_mod_cast le_of_lt ((le_max_left (N : ℚ) 1).trans (le_max_right _ _) |>.trans_lt hn)
  have hn1 : (1 : ℚ) < n :=
    ((le_max_right (N : ℚ) 1).trans (le_max_right _ _)).trans_lt hn
  have hnpos : (0 : ℚ) < n := lt_trans zero_lt_one hn1
  have hpow : (n : ℚ) ^ (b + 1) ≤ (n : ℚ) ^ a :=
    pow_le_pow_right₀ hn1.le hba
  have hprod : (c * n) * (n : ℚ) ^ b ≤ C * (n : ℚ) ^ b := by
    calc
      (c * n) * (n : ℚ) ^ b = c * (n : ℚ) ^ (b + 1) := by rw [pow_succ]; ring
      _ ≤ c * (n : ℚ) ^ a := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hN n hnN
  have hcn : c * n ≤ C := (mul_le_mul_iff_left₀ (pow_pos hnpos b)).mp hprod
  have hlarge : C < c * n := by
    have := (le_max_left (C / c) (max (N : ℚ) 1)).trans_lt hn
    have := (div_lt_iff₀ hc).mp this
    simpa [mul_comm] using this
  exact (not_lt_of_ge hcn) hlarge

/-- Linear changes of the filtration index do not change its growth exponent. -/
theorem exponent_le_of_scaled_filtration_bounds
    (f : ℕ → ℕ) {a b L : ℕ} {c C : ℚ} (hL : 0 < L) (hc : 0 < c) (hC : 0 ≤ C)
    (hlo : ∀ᶠ n : ℕ in atTop, c * (n : ℚ) ^ a ≤ (f (L * n) : ℚ))
    (hhi : ∀ᶠ n : ℕ in atTop, (f n : ℚ) ≤ C * ((n + 1 : ℕ) : ℚ) ^ b) : a ≤ b := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hlo
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hhi
  apply exponent_le_of_eventual_power_bound hc (C := C * ((L + 1 : ℕ) : ℚ) ^ b)
  apply eventually_atTop.mpr
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans ((le_max_left _ _).trans hn)
  have hn₂ : N₂ ≤ L * n :=
    ((le_max_right N₁ N₂).trans ((le_max_left _ _).trans hn)).trans
      (Nat.le_mul_of_pos_left n hL)
  have hnpos : 1 ≤ n := (le_max_right _ _).trans hn
  have hscale : ((L * n + 1 : ℕ) : ℚ) ≤ ((L + 1 : ℕ) : ℚ) * n := by
    exact_mod_cast (show L * n + 1 ≤ (L + 1) * n by nlinarith)
  calc
    c * (n : ℚ) ^ a ≤ (f (L * n) : ℚ) := hN₁ n hn₁
    _ ≤ C * ((L * n + 1 : ℕ) : ℚ) ^ b := hN₂ (L * n) hn₂
    _ ≤ C * (((L + 1 : ℕ) : ℚ) * n) ^ b :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale b) hC
    _ = (C * ((L + 1 : ℕ) : ℚ) ^ b) * (n : ℚ) ^ b := by rw [mul_pow]; ring

theorem degreeFiltration_mono {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) : Monotone (degreeFiltration M I) := by
  intro m n hmn
  apply Submodule.map_mono
  intro P hP
  apply (MvPolynomial.mem_restrictTotalDegree M.Variable n P).mpr
  exact ((MvPolynomial.mem_restrictTotalDegree M.Variable m P).mp hP).trans hmn

theorem cumulativeHilbertFunction_mono {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) : Monotone (cumulativeHilbertFunction M I) := by
  intro m n hmn
  exact Submodule.finrank_mono (degreeFiltration_mono M I hmn)

/-- A checked reduction with the remaining normalization-based growth theorem
as an explicit hypothesis. This does not assume a Hilbert-dimension formula. -/
theorem relevant_prime_krull_dimension_of_normalization_growth
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (Q : Ideal M.CoordinateRing) (hQ : Q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M Q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension Q)
    (hNoether : ∃ r L : ℕ, 0 < L ∧
      ringKrullDim (M.CoordinateRing ⧸ Q) = ((r : ℕ) : WithBot ℕ∞) ∧
      ∃ c C : ℚ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
        c * (n : ℚ) ^ r ≤ (cumulativeHilbertFunction M Q (L * n) : ℚ) ∧
        (cumulativeHilbertFunction M Q n : ℚ) ≤ C * ((n + 1 : ℕ) : ℚ) ^ r) :
    ringKrullDim (M.CoordinateRing ⧸ Q) =
      ((SectionThree.idealDimension M Q + M.factorCount : ℕ) : WithBot ℕ∞) := by
  obtain ⟨r, L, hL, hr, c₁, C₁, hc₁, hC₁, N₁, h₁⟩ := hNoether
  obtain ⟨c₂, C₂, hc₂, hC₂, N₂, h₂⟩ :=
    cumulativeHilbertFunction_polynomial_bounds M Q hQ hhom hrel
  have hu₁ : ∀ᶠ n : ℕ in atTop, (cumulativeHilbertFunction M Q n : ℚ) ≤
      C₁ * ((n + 1 : ℕ) : ℚ) ^ r :=
    eventually_atTop.mpr ⟨N₁, fun n hn => (h₁ n hn).2⟩
  have hu₂ : ∀ᶠ n : ℕ in atTop, (cumulativeHilbertFunction M Q n : ℚ) ≤
      C₂ * ((n + 1 : ℕ) : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) :=
    eventually_atTop.mpr ⟨N₂, fun n hn => (h₂ n hn).2⟩
  have hlo₁ : ∀ᶠ n : ℕ in atTop, c₁ * (n : ℚ) ^ r ≤
      (cumulativeHilbertFunction M Q (L * n) : ℚ) :=
    eventually_atTop.mpr ⟨N₁, fun n hn => (h₁ n hn).1⟩
  have hlo₂ : ∀ᶠ n : ℕ in atTop,
      c₂ * (n : ℚ) ^ (SectionThree.idealDimension M Q + M.factorCount) ≤
        (cumulativeHilbertFunction M Q ((2 * M.factorCount + 1) * n) : ℚ) := by
    apply eventually_atTop.mpr
    refine ⟨N₂, fun n hn => (h₂ n hn).1.trans ?_⟩
    exact_mod_cast cumulativeHilbertFunction_mono M Q
      (show 2 * M.factorCount * n ≤ (2 * M.factorCount + 1) * n by nlinarith)
  have ha := exponent_le_of_scaled_filtration_bounds (cumulativeHilbertFunction M Q)
    (by omega : 0 < 2 * M.factorCount + 1) hc₂ hC₁.le hlo₂ hu₁
  have hb := exponent_le_of_scaled_filtration_bounds (cumulativeHilbertFunction M Q)
    hL hc₁ hC₂.le hlo₁ hu₂
  rw [hr, le_antisymm hb ha]

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponPrimeHilbertKrull

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert

/-- The prime Hilbert–Krull comparison from actual quotient growth and
finite Noether normalization. -/
theorem relevant_prime_krull_dimension_formula
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q) :
    ringKrullDim (M.CoordinateRing ⧸ q) =
      ((SectionThree.idealDimension M q + M.factorCount : ℕ) : WithBot ℕ∞) := by
  letI : q.IsPrime := hq
  apply relevant_prime_krull_dimension_of_normalization_growth M q hq hhom hrel
  obtain ⟨r, L, hL, hdim, c, C, hc, hC, hb⟩ :=
    PolynomialGrowth.normalization_filtration_bounds (Ideal.Quotient.mkₐ K q)
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk q))
  refine ⟨r, L, hL, hdim, c, C, hc, hC, 0, fun n _ => ?_⟩
  exact hb n

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponFiniteDifference

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.FiniteDifference
variable {ι : Type*} [Fintype ι]

def shift (D : ι → ℚ) : MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ :=
  aeval (fun i => X i - C (D i))

def deriv (D : ι → ℚ) : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
  ∑ i, D i • (pderiv i).toLinearMap

theorem deriv_apply (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    deriv D F = ∑ i, D i • pderiv i F := by
  simp only [deriv, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

theorem deriv_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (i : ι) :
    deriv D (F * X i) = deriv D F * X i + D i • F := by
  classical
  simp only [deriv_apply, pderiv_mul, pderiv_X, MvPolynomial.smul_eq_C_mul,
    mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  simp [Pi.single_apply, mul_ite, mul_assoc]

private theorem PhilipponFiniteDifference_component_mul_X (F : MvPolynomial ι ℚ) (i : ι) (n : ℕ) :
    homogeneousComponent (n + 1) (F * X i) = homogeneousComponent n F * X i := by
  classical
  letI := weightedGradedAlgebra ℚ (1 : ι → ℕ)
  have h := DirectSum.coe_decompose_mul_add_of_right_mem
    (weightedHomogeneousSubmodule ℚ (1 : ι → ℕ))
    (a := F) (i := n) (isHomogeneous_X ℚ i)
  change ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) (F * X i)) (n + 1) : MvPolynomial ι ℚ) =
    ((MvPolynomial.decompose' ℚ (1 : ι → ℕ) F) n : MvPolynomial ι ℚ) * X i at h
  simpa only [MvPolynomial.decompose'_apply, homogeneousComponent] using h

private theorem PhilipponFiniteDifference_degree_le_pred_of_top_zero (F : MvPolynomial ι ℚ) (n : ℕ)
    (hdegree : F.totalDegree ≤ n) (hzero : homogeneousComponent n F = 0) :
    F.totalDegree ≤ n - 1 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hdn : d.degree ≤ n := (le_totalDegree hd).trans hdegree
  have hne : d.degree ≠ n := by
    intro heq
    have hh := congrArg (coeff d) hzero
    simp only [coeff_homogeneousComponent, heq, if_pos rfl, coeff_zero] at hh
    exact (mem_support_iff.mp hd) hh
  change d.degree ≤ n - 1
  omega

private def PhilipponFiniteDifference_Expansion (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ) : Prop :=
  (shift D F).totalDegree ≤ n ∧ homogeneousComponent n (shift D F) = F ∧
    (∀ k, n = k + 1 → homogeneousComponent k (shift D F) = -deriv D F)

private theorem PhilipponFiniteDifference_expansion_C (D : ι → ℚ) (c : ℚ) : PhilipponFiniteDifference_Expansion D (C c) 0 := by
  simp [PhilipponFiniteDifference_Expansion, shift]

private theorem PhilipponFiniteDifference_expansion_mul_X (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hF : F.IsHomogeneous n) (h : PhilipponFiniteDifference_Expansion D F n) (i : ι) :
    PhilipponFiniteDifference_Expansion D (F * X i) (n + 1) := by
  classical
  rcases h with ⟨hdeg, htop, hnext⟩
  have hs : shift D (F * X i) = shift D F * X i - D i • shift D F := by
    simp only [shift, map_mul, aeval_X, mul_sub, MvPolynomial.smul_eq_C_mul]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hs]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_right hdeg 1)
    · exact (totalDegree_smul_le _ _).trans (hdeg.trans (Nat.le_succ n))
  · rw [hs, map_sub, map_smul, PhilipponFiniteDifference_component_mul_X, htop,
      homogeneousComponent_eq_zero _ _ (by omega : (shift D F).totalDegree < n + 1)]
    simp
  · intro k hk
    have hkn : k = n := by omega
    subst k
    rw [hs, map_sub, map_smul, htop, deriv_mul_X]
    cases n with
    | zero =>
      have hconst : F = C (coeff 0 F) := by
        exact (homogeneousComponent_eq_self hF).symm.trans
          (MvPolynomial.homogeneousComponent_zero F)
      have hd : deriv D F = 0 := by
        nth_rw 1 [hconst]
        simp [deriv]
      have hz : coeff (0 : ι →₀ ℕ) (shift D F * X i) = 0 := by
        simpa using (MvPolynomial.coeff_mul_X' (0 : ι →₀ ℕ) i (shift D F))
      simp [hd, homogeneousComponent_zero, hz]
    | succ n =>
      rw [PhilipponFiniteDifference_component_mul_X, hnext n rfl]
      simp only [neg_mul, neg_add_rev, sub_eq_add_neg]
      ac_rfl

private theorem PhilipponFiniteDifference_expansion_monomial (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    PhilipponFiniteDifference_Expansion D (monomial a c) a.degree := by
  classical
  induction a using Finsupp.induction with
  | zero => simpa using PhilipponFiniteDifference_expansion_C D c
  | @single_add i k a hia hk ih =>
    have haux : ∀ k, PhilipponFiniteDifference_Expansion D (monomial (Finsupp.single i k + a) c)
        ((Finsupp.single i k + a).degree) := by
      intro k
      induction k with
      | zero => simpa using ih
      | succ k ihk =>
        have heq : monomial (Finsupp.single i (k + 1) + a) c =
            monomial (Finsupp.single i k + a) c * X i := by
          simp only [monomial_single_add, pow_succ]
          ring
        rw [heq]
        have hh := PhilipponFiniteDifference_expansion_mul_X D (monomial (Finsupp.single i k + a) c)
          (Finsupp.single i k + a).degree (isHomogeneous_monomial c rfl) ihk i
        simpa only [map_add, Finsupp.degree_single, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
    exact haux k

private theorem PhilipponFiniteDifference_monomial_difference (D : ι → ℚ) (a : ι →₀ ℕ) (c : ℚ) :
    (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree - 1 ∧
    (a.degree = 0 → monomial a c - shift D (monomial a c) = 0) ∧
    (0 < a.degree → homogeneousComponent (a.degree - 1)
      (monomial a c - shift D (monomial a c)) = deriv D (monomial a c)) := by
  obtain ⟨hdeg, htop, hnext⟩ := PhilipponFiniteDifference_expansion_monomial D a c
  have hhom := isHomogeneous_monomial (σ := ι) c (show a.degree = a.degree from rfl)
  have hbd : (monomial a c - shift D (monomial a c)).totalDegree ≤ a.degree :=
    (totalDegree_sub _ _).trans (max_le hhom.totalDegree_le hdeg)
  refine ⟨PhilipponFiniteDifference_degree_le_pred_of_top_zero _ _ hbd ?_, ?_, ?_⟩
  · rw [map_sub, homogeneousComponent_eq_self hhom, htop, sub_self]
  · intro ha
    have hconst : monomial a c = C (coeff 0 (monomial a c)) :=
      (homogeneousComponent_eq_self (ha ▸ hhom)).symm.trans
        (MvPolynomial.homogeneousComponent_zero _)
    conv_lhs => rw [hconst]
    simp [shift]
  · intro ha
    rw [map_sub, homogeneousComponent_of_mem hhom,
      if_neg (by omega), hnext (a.degree - 1) (by omega)]
    simp

/-- Translation subtracts the top degree, and its next homogeneous part is
the directional derivative of the old top part. -/
theorem top_difference (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (ha : 0 < a) (hF : F.totalDegree ≤ a) :
    (F - shift D F).totalDegree ≤ a - 1 ∧
    homogeneousComponent (a - 1) (F - shift D F) =
      deriv D (homogeneousComponent a F) := by
  classical
  let δ : MvPolynomial ι ℚ →ₗ[ℚ] MvPolynomial ι ℚ :=
    LinearMap.id - (shift D).toLinearMap
  have hδ : δ F = F - shift D F := rfl
  have hsum : F - shift D F = ∑ d ∈ F.support, δ (monomial d (coeff d F)) := by
    rw [← hδ, ← map_sum]
    congr 1
    exact F.as_sum
  have hterm (d : ι →₀ ℕ) (hd : d ∈ F.support) :
      (δ (monomial d (coeff d F))).totalDegree ≤ a - 1 ∧
      homogeneousComponent (a - 1) (δ (monomial d (coeff d F))) =
        deriv D (homogeneousComponent a (monomial d (coeff d F))) := by
    obtain ⟨hdeg, hz, ht⟩ := PhilipponFiniteDifference_monomial_difference D d (coeff d F)
    have hda : d.degree ≤ a := (le_totalDegree hd).trans hF
    refine ⟨hdeg.trans (Nat.sub_le_sub_right hda 1), ?_⟩
    change homogeneousComponent (a - 1) (monomial d (coeff d F) - shift D (monomial d (coeff d F))) = _
    by_cases heq : d.degree = a
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_pos heq.symm, ← heq]
      exact ht (heq ▸ ha)
    · rw [homogeneousComponent_of_mem (isHomogeneous_monomial (coeff d F) rfl),
        if_neg (Ne.symm heq), map_zero]
      by_cases hd0 : d.degree = 0
      · rw [hz hd0, map_zero]
      · exact homogeneousComponent_eq_zero _ _ (by omega)
  constructor
  · rw [hsum]
    exact (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun d hd => (hterm d hd).1))
  · rw [hsum, map_sum]
    conv_rhs => rw [F.as_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun d hd => (hterm d hd).2)

theorem coeff_deriv (D : ι → ℚ) (F : MvPolynomial ι ℚ) (b : ι →₀ ℕ) :
    coeff b (deriv D F) =
      ∑ i, D i * (coeff (b + Finsupp.single i 1) F * (b i + 1 : ℚ)) := by
  classical
  rw [deriv_apply]
  change coeff b (∑ i, D i • pderiv i F) = _
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_pderiv]

theorem deriv_ne_zero (D : ι → ℚ) (hD : ∀ i, 0 < D i)
    (F : MvPolynomial ι ℚ) (a : ℕ) (ha : 0 < a)
    (hF : F.IsHomogeneous a) (hne : F ≠ 0)
    (hcoeff : ∀ b, 0 ≤ coeff b F) : deriv D F ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := exists_coeff_ne_zero hne
  have hba : b.degree = a := by
    by_contra h
    exact hb (hF.coeff_eq_zero h)
  have hsum : 0 < ∑ i, b i := by
    simpa only [← Finsupp.degree_eq_sum, hba] using ha
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hsum
  let c := b - Finsupp.single i 1
  have hc : c + Finsupp.single i 1 = b := by
    apply tsub_add_cancel_of_le
    exact Finsupp.single_le_iff.mpr (by omega)
  have hpos : 0 < coeff c (deriv D F) := by
    rw [coeff_deriv]
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hD j).le (mul_nonneg (hcoeff _) (by positivity))
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [hc]
      exact mul_pos (hD i) (mul_pos (lt_of_le_of_ne (hcoeff b) (Ne.symm hb)) (by positivity))
  intro hz
  rw [hz, coeff_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- Positive equation degrees prevent cancellation of the new leading part. -/
theorem difference_degree (D : ι → ℚ) (hD : ∀ i, 0 < D i)
    (F : MvPolynomial ι ℚ) (ha : 0 < F.totalDegree)
    (hcoeff : ∀ b, 0 ≤ coeff b (homogeneousComponent F.totalDegree F)) :
    (F - shift D F).totalDegree = F.totalDegree - 1 ∧
    homogeneousComponent (F - shift D F).totalDegree (F - shift D F) =
      deriv D (homogeneousComponent F.totalDegree F) := by
  obtain ⟨hdeg, htop⟩ := top_difference D F F.totalDegree ha le_rfl
  have hne : homogeneousComponent F.totalDegree F ≠ 0 := by
    intro hz
    have hh := PhilipponFiniteDifference_degree_le_pred_of_top_zero F F.totalDegree le_rfl hz
    omega
  have hdne := deriv_ne_zero D hD _ F.totalDegree ha
    (homogeneousComponent_isHomogeneous _ _) hne hcoeff
  have hge : F.totalDegree - 1 ≤ (F - shift D F).totalDegree := by
    by_contra h
    have hz := homogeneousComponent_eq_zero (F.totalDegree - 1) (F - shift D F)
      (lt_of_not_ge h)
    exact hdne (htop.symm.trans hz)
  have heq := le_antisymm hdeg hge
  exact ⟨heq, heq ▸ htop⟩

theorem eval_deriv_monomial (D d : ι → ℚ) (hd : ∀ i, d i ≠ 0)
    (b : ι →₀ ℕ) (c : ℚ) :
    eval d (deriv D (monomial b c)) =
      c * (∑ i, (b i : ℚ) * D i / d i) * ∏ i, d i ^ b i := by
  classical
  have hev (i : ι) : eval d (pderiv i (monomial b c)) =
      (b i : ℚ) * eval d (monomial b c) / d i := by
    apply (eq_div_iff (hd i)).mpr
    have hh := congrArg (eval d) (X_mul_pderiv_monomial (i := i) (m := b) (r := c))
    simpa only [map_mul, eval_X, map_nsmul, nsmul_eq_mul, map_natCast, mul_comm] using hh
  rw [deriv_apply]
  change eval d (∑ i, D i • pderiv i (monomial b c)) = _
  simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, hev, eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_deriv_self (D : ι → ℚ) (F : MvPolynomial ι ℚ) (a : ℕ)
    (hF : F.IsHomogeneous a) : eval D (deriv D F) = (a : ℚ) * eval D F := by
  classical
  have hh := congrArg (eval D) hF.sum_X_mul_pderiv
  rw [deriv_apply]
  change eval D (∑ i, D i • pderiv i F) = _
  simpa only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, eval_C, eval_X, map_nsmul,
    nsmul_eq_mul, map_natCast] using hh

end PhilipponMultiplicity.FiniteDifference

end
end


section
-- Reused implementation: Solutions.PhilipponHilbertDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem shift_top (D : ι → ℚ) (F : MvPolynomial ι ℚ) :
    homogeneousComponent F.totalDegree (FiniteDifference.shift D F) =
      homogeneousComponent F.totalDegree F ∧
    (FiniteDifference.shift D F).totalDegree = F.totalDegree := by
  classical
  by_cases hz : F.totalDegree = 0
  · have hc := totalDegree_eq_zero_iff_eq_C.mp hz
    rw [hc]
    simp [FiniteDifference.shift]
  · have hp : 0 < F.totalDegree := Nat.pos_of_ne_zero hz
    have hdiff := (FiniteDifference.top_difference D F F.totalDegree hp le_rfl).1
    have hzero : homogeneousComponent F.totalDegree (F - FiniteDifference.shift D F) = 0 :=
      homogeneousComponent_eq_zero _ _ (by omega)
    rw [map_sub, sub_eq_zero] at hzero
    refine ⟨hzero.symm, le_antisymm ?_ ?_⟩
    · have heq : FiniteDifference.shift D F = F - (F - FiniteDifference.shift D F) := by abel
      nth_rw 1 [heq]
      exact (totalDegree_sub _ _).trans (max_le le_rfl (by omega))
    · by_contra hlt
      have hc := homogeneousComponent_eq_zero F.totalDegree (FiniteDifference.shift D F)
        (lt_of_not_ge hlt)
      rw [← hzero] at hc
      have ht : homogeneousComponent F.totalDegree F ≠ 0 := by
        have hne : F ≠ 0 := by intro h; apply hz; rw [h, totalDegree_zero]
        obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup F.support
          (support_nonempty.mpr hne) Finsupp.degree
        change F.totalDegree = e.degree at hed
        intro h
        have hx := congrArg (coeff e) h
        rw [coeff_homogeneousComponent, if_pos hed.symm, coeff_zero] at hx
        exact (mem_support_iff.mp he) hx
      exact ht hc

theorem component_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e (homogeneousComponent F.totalDegree F))
    (n : ℕ) (hn : F.totalDegree ≤ n) (e : ι →₀ ℕ) :
    0 ≤ coeff e (homogeneousComponent n F) := by
  by_cases heq : n = F.totalDegree
  · simpa only [heq] using hF e
  · rw [homogeneousComponent_eq_zero n F (by omega), coeff_zero]

theorem totalDegree_le_add_of_top_nonneg (F G : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e (homogeneousComponent F.totalDegree F))
    (hG : ∀ e, 0 ≤ coeff e (homogeneousComponent G.totalDegree G)) :
    F.totalDegree ≤ (F + G).totalDegree := by
  classical
  have aux (A B : MvPolynomial ι ℚ)
      (hA : ∀ e, 0 ≤ coeff e (homogeneousComponent A.totalDegree A))
      (hB : ∀ e, 0 ≤ coeff e (homogeneousComponent B.totalDegree B))
      (hle : B.totalDegree ≤ A.totalDegree) : A.totalDegree ≤ (A + B).totalDegree := by
    by_cases hz : A = 0
    · simp [hz]
    obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup A.support (support_nonempty.mpr hz) Finsupp.degree
    change A.totalDegree = e.degree at hed
    have hc : 0 < coeff e (homogeneousComponent A.totalDegree A) := by
      apply lt_of_le_of_ne (hA e)
      rw [coeff_homogeneousComponent, if_pos hed.symm]
      exact Ne.symm (mem_support_iff.mp he)
    have hpos : 0 < coeff e (homogeneousComponent A.totalDegree (A + B)) := by
      rw [map_add, coeff_add]
      exact add_pos_of_pos_of_nonneg hc (component_nonneg B hB _ hle e)
    by_contra hlt
    rw [homogeneousComponent_eq_zero _ _ (lt_of_not_ge hlt), coeff_zero] at hpos
    exact (lt_irrefl 0) hpos
  rcases le_total G.totalDegree F.totalDegree with hle | hle
  · exact aux F G hF hG hle
  · exact hle.trans (by simpa only [add_comm] using aux G F hG hF hle)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem idealDimension_sup_span_le (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    idealDimension M (I ⊔ Ideal.span {P}) ≤ idealDimension M I := by
  unfold idealDimension
  rw [hilbertPolynomial_colon_add M I hI P D hP]
  apply ComponentDegree.totalDegree_le_add_of_top_nonneg
  · exact (multigraded_hilbert_polynomial_top_coefficients K M _
      (homogeneous_sup_span M I hI P D hP)).1
  · have hs := ComponentDegree.shift_top (fun i => (D i : ℚ))
      (hilbertPolynomial K M.factorCount M.ambientDimension (I.colon {P}))
    change ∀ e, 0 ≤ coeff e (homogeneousComponent
      (FiniteDifference.shift _ _).totalDegree (FiniteDifference.shift _ _))
    rw [hs.2, hs.1]
    exact (multigraded_hilbert_polynomial_top_coefficients K M _
      (homogeneous_colon M I hI P D hP)).1

theorem homogeneous_component_outside (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hnot : ¬ J ≤ I) :
    ∃ P D, M.IsHomogeneous P D ∧ P ∈ J ∧ P ∉ I := by
  classical
  obtain ⟨f, hfJ, hfI⟩ := Set.not_subset.mp hnot
  let w := blockWeight M.factorCount M.ambientDimension
  have hsome : ∃ d, weightedHomogeneousComponent w d f ∉ I := by
    by_contra! h
    apply hfI
    rw [← sum_weightedHomogeneousComponent w f]
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact I.sum_mem (fun d _ => h d)
  obtain ⟨d, hd⟩ := hsome
  exact ⟨_, d, (M.degreePiece_iff _ d).mp (weightedHomogeneousComponent_mem _ _ _),
    hJ f hfJ d, hd⟩

/-- Hilbert dimension is antitone under inclusion of actual homogeneous ideals. -/
theorem idealDimension_antitone (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J) (hle : I ≤ J) :
    idealDimension M J ≤ idealDimension M I := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases heq : I = J
    · simp [heq]
    · have hnot : ¬ J ≤ I := fun h => heq (le_antisymm hle h)
      obtain ⟨P, D, hP, hPJ, hPI⟩ := homogeneous_component_outside M I J hI hJ hnot
      have hlt : I < I ⊔ Ideal.span {P} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hPI
        rw [h]
        exact (le_sup_right : Ideal.span {P} ≤ I ⊔ Ideal.span {P})
          (Ideal.subset_span (Set.mem_singleton P))
      have hsub : I ⊔ Ideal.span {P} ≤ J := by
        apply sup_le hle
        rwa [Ideal.span_singleton_le_iff_mem]
      exact (ih _ hlt (homogeneous_sup_span M I hI P D hP) hsub).trans
        (idealDimension_sup_span_le M I hI P D hP)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponComponentFormula
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section
attribute [local instance] Classical.propDecidable

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem shift_component_of_le (D : ι → ℚ) (F : MvPolynomial ι ℚ) (n : ℕ)
    (hn : F.totalDegree ≤ n) :
    homogeneousComponent n (FiniteDifference.shift D F) = homogeneousComponent n F := by
  have hs := shift_top D F
  by_cases heq : n = F.totalDegree
  · rw [heq]; exact hs.1
  · rw [homogeneousComponent_eq_zero n F (by omega),
      homogeneousComponent_eq_zero n (FiniteDifference.shift D F) (by omega)]

end PhilipponMultiplicity.ComponentDegree

end
end


section
-- Reused implementation: Solutions.PhilipponDegreeMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem eval_nonneg_of_coeff_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e F) (d : ι → ℕ) : 0 ≤ eval (fun i => (d i : ℚ)) F := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hF e)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.Hilbert
open SectionThree ComponentDegree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem degreeValue_sup_span_le (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hdim : idealDimension M (I ⊔ Ideal.span {P}) = idealDimension M I)
    (d : M.FactorIndex → ℕ) :
    idealDegreeValue M (I ⊔ Ideal.span {P}) d ≤ idealDegreeValue M I d := by
  let Q := I.colon {P}
  let F := hilbertPolynomial K M.factorCount M.ambientDimension Q
  have hQhom := homogeneous_colon M I hI P D hP
  have hQdim := idealDimension_antitone M I Q hI hQhom Ideal.le_colon
  have hcoeff := component_nonneg F
    (multigraded_hilbert_polynomial_top_coefficients K M Q hQhom).1
    (idealDimension M I) hQdim
  have hnonneg := eval_nonneg_of_coeff_nonneg _ hcoeff d
  have hpoly := hilbertPolynomial_colon_add M I hI P D hP
  have hcomp := congrArg (homogeneousComponent (idealDimension M I)) hpoly
  rw [map_add] at hcomp
  have hshift := shift_component_of_le (fun i => (D i : ℚ)) F (idealDimension M I) hQdim
  simp only [FiniteDifference.shift] at hshift
  rw [hshift] at hcomp
  change eval _ (degreeForm K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P})) ≤
    eval _ (degreeForm K M.factorCount M.ambientDimension I)
  unfold degreeForm
  change eval _ (((idealDimension M (I ⊔ Ideal.span {P})).factorial : ℚ) •
      homogeneousComponent (idealDimension M (I ⊔ Ideal.span {P}))
        (hilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}))) ≤
    eval _ (((idealDimension M I).factorial : ℚ) •
      homogeneousComponent (idealDimension M I) (hilbertPolynomial K M.factorCount M.ambientDimension I))
  rw [hdim, hcomp, smul_add, map_add]
  have hscaled : 0 ≤ eval (fun i => (d i : ℚ))
      (((idealDimension M I).factorial : ℚ) • homogeneousComponent (idealDimension M I) F) := by
    rw [smul_eq_C_mul, map_mul, eval_C]
    exact mul_nonneg (Nat.cast_nonneg _) hnonneg
  exact le_add_of_nonneg_right hscaled

/-- Inclusion cannot increase the normalized Hilbert degree when the two
actual Hilbert dimensions agree. This is the comparison used after Lemma 3.2. -/
theorem degreeValue_antitone_of_dimension_eq (I J : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hJ : IsMultihomogeneousIdeal M J)
    (hle : I ≤ J) (hdim : idealDimension M I = idealDimension M J)
    (d : M.FactorIndex → ℕ) : idealDegreeValue M J d ≤ idealDegreeValue M I d := by
  induction I using IsNoetherian.induction with
  | hgt I ih =>
    by_cases heq : I = J
    · simp [heq]
    · obtain ⟨P, D, hP, hPJ, hPI⟩ := homogeneous_component_outside M I J hI hJ
        (fun h => heq (le_antisymm hle h))
      have hlt : I < I ⊔ Ideal.span {P} := by
        refine lt_of_le_of_ne le_sup_left ?_
        intro h
        apply hPI
        rw [h]
        exact (le_sup_right : Ideal.span {P} ≤ I ⊔ Ideal.span {P})
          (Ideal.subset_span (Set.mem_singleton P))
      have hsub : I ⊔ Ideal.span {P} ≤ J := by
        apply sup_le hle
        rwa [Ideal.span_singleton_le_iff_mem]
      have hmid := homogeneous_sup_span M I hI P D hP
      have hd₁ := idealDimension_antitone M I (I ⊔ Ideal.span {P}) hI hmid le_sup_left
      have hd₂ := idealDimension_antitone M (I ⊔ Ideal.span {P}) J hmid hJ hsub
      have hmd : idealDimension M (I ⊔ Ideal.span {P}) = idealDimension M I := by omega
      exact (ih _ hlt hmid hsub (hmd.trans hdim)).trans
        (degreeValue_sup_span_le M I hI P D hP hmd d)

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponIrrelevantHilbert

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_mem_blockIdeal (i : M.FactorIndex) (d : M.FactorIndex → ℕ)
    (hd : 0 < d i) (P : M.CoordinateRing) (hP : M.IsHomogeneous P d) :
    P ∈ blockIdeal K M.factorCount M.ambientDimension i := by
  classical
  have hset : Set.range (fun j : Fin (M.ambientDimension i + 1) =>
        (X ⟨i, j⟩ : M.CoordinateRing)) =
      X '' {x : M.Variable | x.1 = i} := by
    ext f
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨⟨i, j⟩, rfl, rfl⟩
    · rintro ⟨⟨k, j⟩, hk, rfl⟩
      change k = i at hk
      subst k
      exact ⟨j, rfl⟩
  unfold blockIdeal
  rw [hset, mem_ideal_span_X_image]
  intro e he
  have hsum : ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ = d i := hP e he i
  have hsome : ∃ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ ≠ 0 := by
    by_contra! h
    have hz : ∑ j : Fin (M.ambientDimension i + 1), e ⟨i, j⟩ = 0 := by simp [h]
    omega
  obtain ⟨j, hj⟩ := hsome
  exact ⟨⟨i, j⟩, rfl, hj⟩

theorem hilbertPolynomial_zero_of_blockIdeal_le (I : Ideal M.CoordinateRing)
    (i : M.FactorIndex) (hI : blockIdeal K M.factorCount M.ambientDimension i ≤ I) :
    hilbertPolynomial K M.factorCount M.ambientDimension I = 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨fun _ => 1, fun d hd => ?_⟩
  have hz : quotientPiece K M.factorCount M.ambientDimension I d = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨P, hP, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hI (homogeneous_mem_blockIdeal M i d (hd i) P ((M.degreePiece_iff P d).mp hP))
  rw [map_zero, hilbertFunction, hz, finrank_bot, Nat.cast_zero]

/-- An irrelevant prime has zero multiprojective Hilbert polynomial, including
the zero-dimensional boundary case in the natural total-degree convention. -/
theorem irrelevant_prime_hilbertPolynomial_zero (Q : Ideal M.CoordinateRing)
    (hQ : Q.IsPrime) (hirr : ¬ IsRelevant K M.factorCount M.ambientDimension Q) :
    hilbertPolynomial K M.factorCount M.ambientDimension Q = 0 := by
  classical
  have hle : irrelevantIdeal K M.factorCount M.ambientDimension ≤ Q := not_not.mp hirr
  have hfin : Finset.univ.inf (blockIdeal K M.factorCount M.ambientDimension) ≤ Q := by
    simpa only [irrelevantIdeal, Finset.inf_eq_iInf, Finset.mem_univ, iInf_true] using hle
  obtain ⟨i, hi, hblock⟩ := hQ.inf_le'.mp hfin
  exact hilbertPolynomial_zero_of_blockIdeal_le M Q i hblock

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponMinimalPrimeHomogeneous

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Every actual minimal prime of a multihomogeneous ideal is multihomogeneous. -/
theorem minimalPrime_homogeneous (I Q : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (hQ : Q ∈ I.minimalPrimes) :
    IsMultihomogeneousIdeal M Q := by
  classical
  let w : M.Variable → Lex (M.FactorIndex → ℕ) :=
    fun x => toLex (blockWeight M.factorCount M.ambientDimension x)
  letI : DecidableEq (Lex (M.FactorIndex → ℕ)) := LinearOrder.toDecidableEq
  letI := weightedGradedAlgebra K w
  have hproj (f : M.CoordinateRing) (d : Lex (M.FactorIndex → ℕ)) :
      weightedHomogeneousComponent w d f =
        weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (ofLex d) f := by
    ext e
    simp only [coeff_weightedHomogeneousComponent]
    rfl
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    rw [MvPolynomial.decompose'_apply, hproj]
    exact hI f hf (ofLex d)
  let C := Q.homogeneousCore (weightedHomogeneousSubmodule K w)
  have hCprime : C.toIdeal.IsPrime := hQ.1.1.homogeneousCore
  have hCQ : C.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hIC : I ≤ C.toIdeal := by
    rw [← hIg.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hQ.1.2
  have heq : C.toIdeal = Q := le_antisymm hCQ (hQ.2 ⟨hCprime, hIC⟩ hCQ)
  intro f hf d
  rw [← heq] at hf ⊢
  have h := weightedHomogeneousComponent_mem_of_mem K w C.isHomogeneous hf (toLex d)
  rwa [hproj] at h

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHypersurfaceHilbert

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
namespace Hilbert

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

private theorem PhilipponHypersurfaceHilbert_component_mul_homogeneous
    {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (Q : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)
      (P * Q) =
    P * weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d Q := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hP' : P ∈ weightedHomogeneousSubmodule K w D :=
    (M.degreePiece_iff P D).mpr hP
  have hh := DirectSum.coe_decompose_mul_add_of_left_mem
    (weightedHomogeneousSubmodule K w) (b := Q) (j := d) hP'
  change ((MvPolynomial.decompose' K w (P * Q)) (D + d) : M.CoordinateRing) =
    P * ((MvPolynomial.decompose' K w Q) d : M.CoordinateRing) at hh
  simpa only [MvPolynomial.decompose'_apply] using hh

instance quotientPiece_finite (I : Ideal M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    Module.Finite K (quotientPiece K M.factorCount M.ambientDimension I d) := by
  unfold quotientPiece
  infer_instance

/-- The actual short exact sequence for multiplication by a regular
multihomogeneous equation, in each multidegree. -/
theorem hilbertFunction_hypersurface_add
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) (d : M.FactorIndex → ℕ) :
    hilbertFunction K M.factorCount M.ambientDimension
        (I ⊔ Ideal.span {P}) (D + d) +
      hilbertFunction K M.factorCount M.ambientDimension I d =
    hilbertFunction K M.factorCount M.ambientDimension I (D + d) := by
  classical
  let J := I ⊔ Ideal.span {P}
  let W := fun n => quotientPiece K M.factorCount M.ambientDimension I n
  let V := quotientPiece K M.factorCount M.ambientDimension J (D + d)
  let f : W d →ₗ[K] W (D + d) :=
    ((LinearMap.mulLeft K (Ideal.Quotient.mk I P)).domRestrict (W d)).codRestrict
      (W (D + d)) (by
        rintro ⟨x, Q, hQ, rfl⟩
        refine ⟨P * Q, ?_, ?_⟩
        · exact ((M.degreePiece_iff P D).mpr hP :
            P.IsWeightedHomogeneous (blockWeight M.factorCount M.ambientDimension) D).mul hQ
        · exact map_mul (Ideal.Quotient.mk I) P Q)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hregular.left (congrArg Subtype.val hxy)
  let q : (M.CoordinateRing ⧸ I) →ₐ[K] (M.CoordinateRing ⧸ J) :=
    Ideal.quotientMapₐ J (AlgHom.id K M.CoordinateRing) (by
      intro x hx
      exact (le_sup_left : I ≤ J) hx)
  let g : W (D + d) →ₗ[K] V :=
    (q.toLinearMap.domRestrict (W (D + d))).codRestrict V (by
      rintro ⟨x, Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩)
  have hsurj : Function.Surjective g := by
    rintro ⟨x, Q, hQ, rfl⟩
    exact ⟨⟨Ideal.Quotient.mk I Q, ⟨Q, hQ, rfl⟩⟩, rfl⟩
  have hker : LinearMap.ker g = LinearMap.range f := by
    ext x
    constructor
    · intro hx
      obtain ⟨Q, hQ, hQx⟩ := x.property
      have hQJ : Q ∈ J := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hx' := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
        change q x.val = 0 at hx'
        rw [← hQx] at hx'
        exact hx'
      obtain ⟨a, b, hb, heq⟩ :=
        Ideal.mem_span_singleton_sup.mp (show Q ∈ Ideal.span {P} ⊔ I by
          simpa only [sup_comm] using hQJ)
      let a' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) d a
      let b' := weightedHomogeneousComponent
        (blockWeight M.factorCount M.ambientDimension) (D + d) b
      have hb' : b' ∈ I := hI b hb (D + d)
      have hproj : P * a' + b' = Q := by
        have hh := congrArg
          (weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) (D + d)) heq
        rw [map_add, mul_comm a P, PhilipponHypersurfaceHilbert_component_mul_homogeneous M hP a d,
          IsWeightedHomogeneous.weightedHomogeneousComponent_same hQ] at hh
        exact hh
      refine ⟨⟨Ideal.Quotient.mk I a', ⟨a', ?_, rfl⟩⟩, ?_⟩
      · exact weightedHomogeneousComponent_mem _ _ _
      · apply Subtype.ext
        change Ideal.Quotient.mk I P * Ideal.Quotient.mk I a' = x.val
        change Ideal.Quotient.mk I Q = x.val at hQx
        rw [← hQx, ← hproj, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb', add_zero,
          map_mul]
    · rintro ⟨y, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change q (Ideal.Quotient.mk I P * y.val) = 0
      rw [map_mul]
      have hP0 : q (Ideal.Quotient.mk I P) = 0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        exact (le_sup_right : Ideal.span {P} ≤ J) (Ideal.subset_span (Set.mem_singleton P))
      rw [hP0, zero_mul]
  have hdim := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
    LinearMap.finrank_range_of_inj hinj] at hdim
  exact hdim

/-- The finite-difference Hilbert polynomial follows from the exact sequence;
the premise is an actual eventual Hilbert polynomial, not an assigned degree. -/
theorem IsHilbertPolynomial.hypersurface
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (F : MvPolynomial M.FactorIndex ℚ)
    (hF : IsHilbertPolynomial K M.factorCount M.ambientDimension I F) :
    IsHilbertPolynomial K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P})
      (F - aeval (fun i => X i - C (D i : ℚ)) F) := by
  obtain ⟨b, hb⟩ := hF
  refine ⟨D + b, fun n hn => ?_⟩
  have hDn : ∀ i, D i ≤ n i := fun i => (Nat.le_add_right _ _).trans (hn i)
  have hbn : ∀ i, b i ≤ n i := fun i => (Nat.le_add_left _ _).trans (hn i)
  have hbsub : ∀ i, b i ≤ n i - D i := by
    intro i
    have := hn i
    change D i + b i ≤ n i at this
    omega
  have hnsub : D + (n - D) = n := by
    funext i
    exact Nat.add_sub_of_le (hDn i)
  have heval : eval (fun i => (n i : ℚ)) (aeval (fun i => X i - C (D i : ℚ)) F) =
      eval (fun i => (((n - D) i : ℕ) : ℚ)) F := by
    have hc : (fun i => ((n i : ℚ) - D i)) = (fun i => (((n - D) i : ℕ) : ℚ)) := by
      funext i
      simp [Nat.cast_sub (hDn i)]
    clear hb
    induction F using MvPolynomial.induction_on with
    | C a => simp
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F i hF =>
        simp only [map_mul, hF, aeval_X, map_sub, eval_X, eval_C]
        rw [congrFun hc i]
  rw [map_sub, heval, hb n hbn, hb (n - D) hbsub]
  have hdim := hilbertFunction_hypersurface_add M I hI P D hP hregular (n - D)
  rw [hnsub] at hdim
  exact_mod_cast (show
    (hilbertFunction K M.factorCount M.ambientDimension I n : ℚ) -
      hilbertFunction K M.factorCount M.ambientDimension I (n - D) =
      hilbertFunction K M.factorCount M.ambientDimension (I ⊔ Ideal.span {P}) n by
    have hcast := congrArg (fun x : ℕ => (x : ℚ)) hdim
    push_cast at hcast
    linarith)

end Hilbert
end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponRegularCutDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem idealDimension_le_of_minimalPrimes (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (b : ℕ)
    (hb : ∀ q ∈ I.minimalPrimes, IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q ≤ b) : idealDimension M I ≤ b := by
  classical
  obtain ⟨n, A, P, D, hfirst, hlast, hhom, hstep⟩ := homogeneous_prime_filtration M I hI
  have hmono : Monotone A := Fin.monotone_iff_le_succ.mpr fun j => by
    rw [(hstep j).2.2.1]; exact le_sup_left
  unfold idealDimension
  rw [← hfirst, hilbertPolynomial_filtration_sum M n A P D hhom
    (fun j => ⟨(hstep j).1, (hstep j).2.2.1⟩) hlast]
  apply totalDegree_finsetSum_le
  intro j _
  let Q := (A j.castSucc).colon {P j}
  have hQ := (hstep j).2.2.2
  have hQhom := homogeneous_colon M _ (hhom j.castSucc) _ _ (hstep j).1
  change (FiniteDifference.shift (fun i => (D j i : ℚ))
      (hilbertPolynomial K M.factorCount M.ambientDimension Q)).totalDegree ≤ b
  by_cases hr : IsRelevant K M.factorCount M.ambientDimension Q
  · have hIQ : I ≤ Q := by
      rw [← hfirst]
      exact (hmono (Fin.zero_le _)).trans Ideal.le_colon
    letI : Q.IsPrime := hQ
    obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hIQ
    have hprel : IsRelevant K M.factorCount M.ambientDimension p := fun h => hr (h.trans hpQ)
    rw [(ComponentDegree.shift_top _ _).2]
    exact (idealDimension_antitone M p Q (minimalPrime_homogeneous M I p hI hp)
      hQhom hpQ).trans (hb p hp hprel)
  · rw [irrelevant_prime_hilbertPolynomial_zero M Q hQ hr, map_zero, totalDegree_zero]
    exact Nat.zero_le b

/-- The numerical hypersurface identity at the equation's own degree does
not require positive degree entries once the actual dimension drop is known. -/
theorem regular_cut_degreeValue_of_dimension (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (hregular : IsRegular (Ideal.Quotient.mk I P))
    (hdim : idealDimension M (I ⊔ Ideal.span {P}) + 1 = idealDimension M I) :
    idealDegreeValue M (I ⊔ Ideal.span {P}) D = idealDegreeValue M I D := by
  classical
  let F := hilbertPolynomial K M.factorCount M.ambientDimension I
  let a := F.totalDegree
  let Q := F - FiniteDifference.shift (fun i => (D i : ℚ)) F
  have ha : 0 < a := by change 0 < idealDimension M I; omega
  have hpoly : hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P}) = Q :=
    hilbertPolynomial_eq_of_isHilbertPolynomial _ _ _ _
      (IsHilbertPolynomial.hypersurface M I hI P D hP hregular F
        (hilbertPolynomial_spec _ _ _ _ (multigraded_hilbert_polynomial_exists K M I hI)))
  have hdegree : Q.totalDegree = a - 1 := by
    change (hilbertPolynomial K M.factorCount M.ambientDimension
      (I ⊔ Ideal.span {P})).totalDegree + 1 = a at hdim
    rw [hpoly] at hdim
    omega
  have htop := (FiniteDifference.top_difference (fun i => (D i : ℚ)) F a ha le_rfl).2
  unfold idealDegreeValue degreeValue degreeForm
  rw [hpoly]
  change eval _ ((Q.totalDegree.factorial : ℚ) • homogeneousComponent Q.totalDegree Q) =
    eval _ ((a.factorial : ℚ) • homogeneousComponent a F)
  rw [hdegree, htop, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
    FiniteDifference.eval_deriv_self _ _ _ (homogeneousComponent_isHomogeneous _ _),
    MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
  have haeq : a = (a - 1) + 1 := by omega
  have hfac : ((a - 1).factorial : ℚ) * (a : ℚ) = (a.factorial : ℚ) := by
    have hh := Nat.factorial_succ (a - 1)
    rw [← haeq] at hh
    exact_mod_cast (Nat.mul_comm _ _).trans hh.symm
  rw [← mul_assoc, hfac]

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponAffineAltitudeKernelAudit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW
namespace S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

set_option autoImplicit false

universe u v

namespace P2mDimFormula

open Ideal Polynomial

private lemma PhilipponAffineAltitudeKernelAudit_exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨q, hq⟩ := Algebra.IsIntegral.comap_surjective R S x
    exact ⟨RelSeries.singleton _ q, rfl, hq⟩
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      have h1 : PrimeSpectrum.comap (algebraMap R S) L.last ≤ x := hlast ▸ le_of_lt hx
      exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr h1
    obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal L.last.asIdeal hle
    have hlx : l.last < x := hx
    have hQlt : L.last < (⟨Q, hQprime⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
      intro h
      refine absurd ?_ (ne_of_lt hlx)
      calc l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
        _ = PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ := by rw [h]
        _ = x := PrimeSpectrum.ext hQcomap
    refine ⟨L.snoc ⟨Q, hQprime⟩ hQlt, by simp [hlen], ?_⟩
    simp only [RelSeries.last_snoc]
    exact PrimeSpectrum.ext hQcomap

theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S := by
  refine le_antisymm ?_ ?_
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    refine iSup_le fun l => ?_
    obtain ⟨L, hlen, -⟩ := PhilipponAffineAltitudeKernelAudit_exists_ltSeries_comap_eq_last hinj l
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  · change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
    refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)

theorem height_le_height_under_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] :
    P.height ≤ (P.under R).height := by
  haveI : (P.under R).IsPrime := inferInstance
  rw [show P.height = Order.height (⟨P, ‹_›⟩ : PrimeSpectrum S) from
      PrimeSpectrum.height_eq_orderHeight ⟨P, _⟩,
    show (P.under R).height = Order.height (⟨P.under R, ‹_›⟩ : PrimeSpectrum R) from
      PrimeSpectrum.height_eq_orderHeight ⟨P.under R, _⟩]
  have hf : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
    intro q1 q2 hlt
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
    obtain ⟨y, hy2, hy1⟩ := SetLike.exists_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hlt)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le) ⟨hy2, hy1⟩
      (Algebra.IsIntegral.isIntegral y)
  exact Order.height_le_height_apply_of_strictMono _ hf ⟨P, ‹_›⟩

theorem height_eq_height_under_of_hasGoingDown {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  refine le_antisymm (height_le_height_under_of_isIntegral P) ?_
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  exact le_self_add

theorem ringKrullDim_mvPolynomial_fin (k : Type u) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem height_eq_of_isMaximal_mvPolynomial (k : Type u) [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
    intro M hM
    have hle : (M.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 0) k) :=
      Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [ringKrullDim_mvPolynomial_fin] at hle
    have : M.height ≤ 0 := by exact_mod_cast hle
    simpa using this
  | succ n ih =>
    intro M hM
    haveI := hM
    let e : MvPolynomial (Fin (n + 1)) k ≃+* (MvPolynomial (Fin n) k)[X] :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let M' : Ideal (MvPolynomial (Fin n) k)[X] := M.map e
    haveI hM' : M'.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let p : Ideal (MvPolynomial (Fin n) k) := M'.under (MvPolynomial (Fin n) k)
    haveI : M'.LiesOver p := ⟨rfl⟩
    have hp : p.IsMaximal := by
      have : p = M'.comap (C : MvPolynomial (Fin n) k →+* (MvPolynomial (Fin n) k)[X]) := by
        simp only [p, Ideal.under_def, Polynomial.algebraMap_eq]
      rw [this]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
    have h1 : M'.height = p.height + 1 := Polynomial.height_eq_height_add_one p M'
    have h2 : p.height = n := ih p hp
    have h3 : M'.height = M.height := RingEquiv.height_map e M
    rw [← h3, h1, h2]
    norm_cast

theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hdim : ringKrullDim A = s := by
    rw [← ringKrullDim_mvPolynomial_fin k s]
    exact (ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) hinj).symm
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top hm.ne_top) ?_
  let m' : Ideal (MvPolynomial (Fin s) k) := m.under (MvPolynomial (Fin s) k)
  have h1 : m'.height = s := height_eq_of_isMaximal_mvPolynomial k s m' inferInstance
  have h2 : m.height = m'.height + _ := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m' m
  have h3 : (s : ℕ∞) ≤ m.height := by
    rw [h2, h1]; exact le_self_add
  rw [hdim]
  exact_mod_cast h3

theorem ringKrullDim_quotient_radical {A : Type v} [CommRing A] (I : Ideal A) :
    ringKrullDim (A ⧸ I.radical) = ringKrullDim (A ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

theorem ringKrullDim_quotient_radical_span_add_one (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal]
    {f : A} (hf : f ≠ 0) (hfm : f ∈ m) :
    ringKrullDim (A ⧸ (Ideal.span {f}).radical) + 1 = ringKrullDim A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [ringKrullDim_quotient_radical]
  exact Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf) (height_eq_ringKrullDim_of_isMaximal k m) hfm

theorem exists_ringKrullDim_eq_natCast (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨RingHom.Finite.to_isIntegral hfin⟩
  refine ⟨s, ?_⟩
  rw [← ringKrullDim_mvPolynomial_fin k s]
  exact (ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) hinj).symm

theorem height_head_add_length_le {α : Type*} [Preorder α] (p : LTSeries α) :
    Order.height p.head + p.length ≤ Order.height p.last := by
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.height p.head →
      ((n + p.length : ℕ) : ℕ∞) ≤ Order.height p.last := by
    intro n hn
    obtain ⟨q, hlast, hlen⟩ := Order.exists_series_of_le_height p.head hn
    have h := Order.length_le_height_last (p := q.smash p hlast)
    rw [RelSeries.last_smash, RelSeries.smash_length, hlen] at h
    exact h
  cases hh : Order.height p.head with
  | top =>
    have : Order.height p.last = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro m
      have := key m (by rw [hh]; exact le_top)
      exact le_trans (by exact_mod_cast Nat.le_add_right m p.length) this
    rw [this]; exact le_top
  | coe m =>
    have := key m (by rw [hh])
    exact_mod_cast this

theorem height_map_mk_add_height_le {A : Type v} [CommRing A] (P₁ P : Ideal A) [P₁.IsPrime]
    [P.IsPrime] (h : P₁ ≤ P) [hP : (P.map (Ideal.Quotient.mk P₁)).IsPrime] :
    (P.map (Ideal.Quotient.mk P₁)).height + P₁.height ≤ P.height := by
  rw [show (P.map (Ideal.Quotient.mk P₁)).height =
      Order.height (⟨P.map (Ideal.Quotient.mk P₁), hP⟩ : PrimeSpectrum (A ⧸ P₁)) from
      PrimeSpectrum.height_eq_orderHeight ⟨_, hP⟩,
    show P₁.height = Order.height (⟨P₁, ‹_›⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨P₁, _⟩,
    show P.height = Order.height (⟨P, ‹_›⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨P, _⟩]
  set xb : PrimeSpectrum (A ⧸ P₁) := ⟨P.map (Ideal.Quotient.mk P₁), hP⟩ with hxb
  set f := PrimeSpectrum.comap (Ideal.Quotient.mk P₁) with hfdef
  have hf : StrictMono f := RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  have hfx : f xb = ⟨P, ‹_›⟩ := by
    apply PrimeSpectrum.ext
    change (P.map (Ideal.Quotient.mk P₁)).comap (Ideal.Quotient.mk P₁) = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr h
  have hhead : ∀ y : PrimeSpectrum (A ⧸ P₁), (⟨P₁, ‹_›⟩ : PrimeSpectrum A) ≤ f y := by
    intro y
    change P₁ ≤ y.asIdeal.comap (Ideal.Quotient.mk P₁)
    intro a ha
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact zero_mem _
  have key : ∀ n : ℕ, (n : ℕ∞) ≤ Order.height xb →
      (n : ℕ∞) + Order.height (⟨P₁, ‹_›⟩ : PrimeSpectrum A) ≤
        Order.height (⟨P, ‹_›⟩ : PrimeSpectrum A) := by
    intro n hn
    obtain ⟨q, hlast, hlen⟩ := Order.exists_series_of_le_height xb hn
    let q' : LTSeries (PrimeSpectrum A) := q.map f hf
    have h1 := height_head_add_length_le q'
    rw [LTSeries.last_map, hlast, hfx, LTSeries.head_map] at h1
    have h2 : Order.height (⟨P₁, ‹_›⟩ : PrimeSpectrum A) ≤ Order.height (f q.head) :=
      Order.height_mono (hhead _)
    have hlen' : q'.length = n := by simp [q', hlen]
    rw [hlen'] at h1
    calc (n : ℕ∞) + Order.height (⟨P₁, ‹_›⟩ : PrimeSpectrum A)
        ≤ n + Order.height (f q.head) := add_le_add le_rfl h2
      _ = Order.height (f q.head) + n := add_comm _ _
      _ ≤ _ := h1
  cases hh : Order.height xb with
  | top =>
    have : Order.height (⟨P, ‹_›⟩ : PrimeSpectrum A) = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro m
      exact le_trans le_self_add (key m (by rw [hh]; exact le_top))
    rw [this]; exact le_top
  | coe m => exact key m (by rw [hh])

theorem ringKrullDim_quotient_eq_coheight {A : Type v} [CommRing A] (P : Ideal A) [P.IsPrime] :
    ringKrullDim (A ⧸ P) = Order.coheight (⟨P, ‹_›⟩ : PrimeSpectrum A) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  apply Order.krullDim_eq_of_orderIso
  refine OrderIso.setCongr _ _ ?_
  ext q
  simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal,
    SetLike.coe_subset_coe]

theorem height_add_ringKrullDim_quotient_le {A : Type v} [CommRing A] (P : Ideal A) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) ≤ ringKrullDim A := by
  haveI : Nonempty (PrimeSpectrum A) := ⟨⟨P, ‹_›⟩⟩
  rw [ringKrullDim_quotient_eq_coheight,
    show P.height = Order.height (⟨P, ‹_›⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨P, _⟩,
    ← WithBot.coe_add, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a : PrimeSpectrum A =>
    Order.height a + Order.coheight a) ⟨P, ‹_›⟩)

theorem ringKrullDim_quotient_add_one_of_height_eq_one (k : Type u) {A : Type v} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have hint : g.toRingHom.IsIntegral := RingHom.Finite.to_isIntegral hfin
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  set B := MvPolynomial (Fin s) k with hB

  let p : Ideal B := P.comap (algebraMap B A)
  have hp : p.height = 1 := by
    rw [← hP]; exact (height_eq_height_under_of_hasGoingDown (R := B) P).symm
  have hp0 : p ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.height_bot] at hp
    exact zero_ne_one hp
  obtain ⟨f, hfp, hfprime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : p.IsPrime) hp0
  have hf0 : f ≠ 0 := hfprime.ne_zero
  haveI hfP : (Ideal.span {f} : Ideal B).IsPrime :=
    (Ideal.span_singleton_prime hf0).mpr hfprime
  have hspan : Ideal.span {f} = p := by
    refine Ideal.eq_of_le_of_height_le (Ideal.span {f})
      ((Ideal.span_singleton_le_iff_mem _).mpr hfp) ?_
    rw [hp]
    have h01 : (⊥ : Ideal B) < Ideal.span {f} := by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hf0
    have := Ideal.height_add_one_le_of_lt_of_isPrime h01
    rw [Ideal.height_bot, zero_add] at this
    exact this

  obtain ⟨M, hMmax, hpM⟩ := Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top inferInstance)
  haveI := hMmax
  have hdimB : ringKrullDim (B ⧸ p) + 1 = ringKrullDim B := by
    have h1 := ringKrullDim_quotient_radical_span_add_one k M hf0 (hpM hfp)
    rwa [Ideal.IsPrime.radical hfP, hspan] at h1

  have hdimA : ringKrullDim A = ringKrullDim B :=
    (ringKrullDim_eq_of_isIntegral_of_injective (R := B) (S := A) hinj).symm
  have hdimQ : ringKrullDim (A ⧸ P) = ringKrullDim (B ⧸ p) := by
    haveI : Algebra.IsIntegral (B ⧸ p) (A ⧸ P) := Algebra.IsIntegral.quotient
    exact (ringKrullDim_eq_of_isIntegral_of_injective (R := B ⧸ p) (S := A ⧸ P)
      Ideal.algebraMap_quotient_injective).symm
  rw [hdimA, hdimQ, hdimB]

theorem main (k : Type u) [Field k] : ∀ (n : ℕ) {A : Type v} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A], ringKrullDim A = n → ∀ (P : Ideal A) [P.IsPrime],
      (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) = ringKrullDim A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ _ hA P _
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine le_antisymm (height_add_ringKrullDim_quotient_le P) ?_
  by_cases hP0 : P = ⊥
  · subst hP0
    rw [Ideal.height_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    simp

  obtain ⟨f, hfP, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨P₁, hP₁min, hP₁P⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem P).mpr hfP)
  haveI hP₁ : P₁.IsPrime := hP₁min.1.1
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    have hfP₁ : f ∈ P₁ := hP₁min.1.2 (Ideal.mem_span_singleton_self f)
    rw [h] at hfP₁
    exact hf0 ((Submodule.mem_bot A).mp hfP₁)
  have hht1 : P₁.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hP₁min) ?_
    have h01 : (⊥ : Ideal A) < P₁ := bot_lt_iff_ne_bot.mpr hP₁ne
    have := Ideal.height_add_one_le_of_lt_of_isPrime h01
    rwa [Ideal.height_bot, zero_add] at this
  have hdrop := ringKrullDim_quotient_add_one_of_height_eq_one k P₁ hht1

  haveI : Nontrivial (A ⧸ P₁) := Ideal.Quotient.nontrivial_iff.mpr hP₁.ne_top
  haveI : Nontrivial (A ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨m, hm⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P₁)
  obtain ⟨e, he⟩ := exists_ringKrullDim_eq_natCast k (A ⧸ P)
  have hmn : m + 1 = n := by
    rw [hm, hA] at hdrop
    exact_mod_cast hdrop

  haveI hPb : (P.map (Ideal.Quotient.mk P₁)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hIH := ih m (by omega) hm (P.map (Ideal.Quotient.mk P₁))
  have hqq : ringKrullDim ((A ⧸ P₁) ⧸ P.map (Ideal.Quotient.mk P₁)) = ringKrullDim (A ⧸ P) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hP₁P)
  rw [hqq, hm, he] at hIH
  have hhtq := height_map_mk_add_height_le P₁ P hP₁P
  rw [hht1] at hhtq
  have h1 : (P.map (Ideal.Quotient.mk P₁)).height + (e : ℕ∞) = m := by exact_mod_cast hIH
  have key : ((n : ℕ) : ℕ∞) ≤ P.height + e := by
    calc ((n : ℕ) : ℕ∞) = m + 1 := by exact_mod_cast hmn.symm
      _ = (P.map (Ideal.Quotient.mk P₁)).height + e + 1 := by rw [h1]
      _ = ((P.map (Ideal.Quotient.mk P₁)).height + 1) + e := add_right_comm _ _ _
      _ ≤ P.height + e := add_le_add hhtq le_rfl
  rw [hA, he]
  exact_mod_cast key

end P2mDimFormula

theorem PhilipponAffineAltitudeKernelAudit_reused_solution
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) = ringKrullDim A := by
  haveI : Nontrivial A := inferInstance
  obtain ⟨n, hn⟩ := P2mDimFormula.exists_ringKrullDim_eq_natCast k A
  exact P2mDimFormula.main k n hn P

end S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
end P2MW
export P2MW.S_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType (PhilipponAffineAltitudeKernelAudit_reused_solution)


theorem altitudeKernelCheck
(K A : Type*) [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (q : Ideal A) (hq : q.IsPrime) :
    ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A  := by
  letI : q.IsPrime := hq
  rw [add_comm]
  exact PhilipponAffineAltitudeKernelAudit_reused_solution K q

end


section
-- Reused implementation: Solutions.PhilipponResolvedCutGeometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The existing hypersurface proof with its two now-proved inputs resolved locally. -/
theorem relevant_hypersurface_component_dimension (p : Ideal M.CoordinateRing)
    (hp : p.IsPrime) (hpH : IsMultihomogeneousIdeal M p)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hPp : P ∉ p)
    (q : Ideal M.CoordinateRing) (hq : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes)
    (hqr : IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q + 1 = idealDimension M p := by
  let : p.IsPrime := hp
  let : q.IsPrime := hq.isPrime
  have hpq : p ≤ q := le_sup_left.trans hq.le
  have hpr : IsRelevant K M.factorCount M.ambientDimension p := fun h => hqr (h.trans hpq)
  have hqh := minimalPrime_homogeneous M _ q (homogeneous_sup_span M p hpH P D hP) hq
  have hmap : (q.map (Ideal.Quotient.mk p)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hpq)
  have hheight := Ideal.height_map_quotient_eq_one_of_minimalPrimes p q hp P hPp hq
  have hd := altitudeKernelCheck K
    (M.CoordinateRing ⧸ p) (q.map (Ideal.Quotient.mk p)) hmap
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq), hheight] at hd
  rw [relevant_prime_krull_dimension_formula M p hp hpH hpr,
    relevant_prime_krull_dimension_formula M q hq.isPrime hqh hqr] at hd
  have hn : idealDimension M q + M.factorCount + 1 =
      idealDimension M p + M.factorCount := by exact_mod_cast hd
  omega

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem notMem_minimalPrime_of_quotient_regular (I p : Ideal M.CoordinateRing)
    (hp : p ∈ I.minimalPrimes) (P : M.CoordinateRing)
    (hregular : IsRegular (Ideal.Quotient.mk I P)) : P ∉ p := by
  rw [Ideal.minimalPrimes_eq_comap] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  intro hP
  change Ideal.Quotient.mk I P ∈ q at hP
  exact (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hP hq)
    hregular.mem_nonZeroDivisors

/-- The geometric dimension statement extends from primes to homogeneous
ideals whose relevant minimal components all have the ideal's dimension. -/
theorem equidimensional_regular_cut_component_dimension (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ p ∈ I.minimalPrimes,
      IsRelevant K M.factorCount M.ambientDimension p →
      idealDimension M p = idealDimension M I)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) (hregular : IsRegular (Ideal.Quotient.mk I P))
    (q : Ideal M.CoordinateRing) (hq : q ∈ (I ⊔ Ideal.span {P}).minimalPrimes)
    (hqr : IsRelevant K M.factorCount M.ambientDimension q) :
    idealDimension M q + 1 = idealDimension M I := by
  let : q.IsPrime := hq.isPrime
  have hIq : I ≤ q := le_sup_left.trans hq.le
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hIq
  have hpr : IsRelevant K M.factorCount M.ambientDimension p := fun h => hqr (h.trans hpq)
  have hq' : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes := by
    refine ⟨⟨hq.isPrime, sup_le hpq (le_sup_right.trans hq.le)⟩, ?_⟩
    intro r hr hrq
    exact hq.2 ⟨hr.1, sup_le (hp.le.trans (le_sup_left.trans hr.2))
      (le_sup_right.trans hr.2)⟩ hrq
  have hd := relevant_hypersurface_component_dimension M p hp.isPrime
    (minimalPrime_homogeneous M I p hI hp) P D hP
    (notMem_minimalPrime_of_quotient_regular M I p hp P hregular) q hq' hqr
  rwa [hdim p hp hpr] at hd

end PhilipponMultiplicity.Hilbert

end
end


section
-- Reused implementation: Solutions.PhilipponHomogeneousPrimary

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimarySupport

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primary_bot_of_injective (f : R →+* S) (hf : Function.Injective f)
    (h : (⊥ : Ideal S).IsPrimary) : (⊥ : Ideal R).IsPrimary := by
  have heq : (⊥ : Ideal S).comap f = ⊥ := by
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact map_eq_zero_iff f hf
  rw [← heq]
  exact h.comap f

theorem primary_bot_quotient (Q : Ideal R) (hQ : Q.IsPrimary) :
    (⊥ : Ideal (R ⧸ Q)).IsPrimary := by
  haveI : Nontrivial (R ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hab : a * b ∈ Q := by
    simpa only [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] using hxy
  rcases (Ideal.isPrimary_iff.mp hQ).2 hab with ha | hb
  · left
    simpa only [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] using ha
  · right
    obtain ⟨n, hn⟩ := hb
    exact ⟨n, by simpa only [Ideal.mem_bot, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] using hn⟩

/-- McCoy's theorem makes zero-primaryness stable under adjoining one variable. -/
theorem primary_bot_polynomial (hR : (⊥ : Ideal R).IsPrimary) :
    (⊥ : Ideal (Polynomial R)).IsPrimary := by
  haveI : Nontrivial R := nontrivial_of_ne (x := (0 : R)) (y := 1) (by
    intro h
    exact (Ideal.ne_top_iff_one _).mp hR.ne_top h.symm)
  refine Ideal.isPrimary_iff.mpr ⟨bot_ne_top, ?_⟩
  intro P Q hPQ
  by_cases hP : P = 0
  · exact Or.inl hP
  right
  have hQ : Q ∉ nonZeroDivisors (Polynomial R) := by
    intro hQ
    exact hP (hQ.2 P hPQ)
  obtain ⟨a, ha, h⟩ := Polynomial.notMem_nonZeroDivisors_iff.mp hQ
  have hnil : IsNilpotent Q := by
    apply Polynomial.isNilpotent_iff.mpr
    intro i
    have hzero : a * Q.coeff i = 0 := by
      simpa only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_zero] using
        congrArg (fun f : Polynomial R => f.coeff i) h
    have hm := ((Ideal.isPrimary_iff.mp hR).2 hzero).resolve_left ha
    exact hm
  exact hnil

/-- Polynomial extension in finitely many variables preserves a primary zero ideal. -/
theorem primary_bot_mvPolynomial {σ : Type*} [Finite σ]
    (hR : (⊥ : Ideal R).IsPrimary) : (⊥ : Ideal (MvPolynomial σ R)).IsPrimary := by
  classical
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ
  · intro α β _ e ih
    exact primary_bot_of_injective (MvPolynomial.renameEquiv R e.symm).toRingHom
      (MvPolynomial.renameEquiv R e.symm).injective ih
  · exact primary_bot_of_injective (MvPolynomial.isEmptyRingEquiv R PEmpty).toRingHom
      (MvPolynomial.isEmptyRingEquiv R PEmpty).injective hR
  · intro α _ ih
    exact primary_bot_of_injective (MvPolynomial.optionEquivLeft R α).toRingHom
      (MvPolynomial.optionEquivLeft R α).injective (primary_bot_polynomial ih)

open MvPolynomial
open Finsupp (weight weight_apply)
variable {σ τ : Type*} {K : Type*} [CommRing K]

/-- The coefficient of the auxiliary monomial of degree `d` is the actual
weighted homogeneous component of degree `d`. -/
def degreeTag (w : σ → (τ →₀ ℕ)) :
    MvPolynomial σ K →+* MvPolynomial τ (MvPolynomial σ K) :=
  eval₂Hom (C.comp C) (fun x => monomial (w x) (X x))

theorem degreeTag_monomial (w : σ → (τ →₀ ℕ)) (e : σ →₀ ℕ) (c : K) :
    degreeTag w (monomial e c) = monomial (weight w e) (monomial e c) := by
  classical
  simp only [degreeTag, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    monomial_pow, weight_apply, Finsupp.sum, Finsupp.prod]
  rw [← monomial_sum_prod]
  rw [monomial_eq (s := e) (a := c), C_mul_monomial]
  rfl

theorem degreeTag_coeff (w : σ → (τ →₀ ℕ)) (f : MvPolynomial σ K) (d : τ →₀ ℕ) :
    coeff d (degreeTag w f) = weightedHomogeneousComponent w d f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, coeff_add, hf, hg]
  | monomial e c =>
    rw [degreeTag_monomial, coeff_monomial]
    ext a
    simp only [coeff_weightedHomogeneousComponent, coeff_monomial]
    split_ifs <;> simp_all <;> aesop

/-- Homogeneous core expressed as the kernel of a map into a polynomial ring
with coefficients in the quotient by `Q`. -/
def weightedCore (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) :=
  RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp (degreeTag w))

theorem mem_weightedCore (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) :
    f ∈ weightedCore w Q ↔ ∀ d, weightedHomogeneousComponent w d f ∈ Q := by
  simp only [weightedCore, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.ext_iff, coeff_map, coeff_zero, degreeTag_coeff,
    Ideal.Quotient.eq_zero_iff_mem]

theorem weightedCore_primary [Finite τ] (w : σ → (τ →₀ ℕ))
    (Q : Ideal (MvPolynomial σ K)) (hQ : Q.IsPrimary) :
    (weightedCore w Q).IsPrimary :=
  (primary_bot_mvPolynomial (σ := τ) (primary_bot_quotient Q hQ)).comap
    ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp (degreeTag w))

theorem weightedCore_le (w : σ → (τ →₀ ℕ)) (Q : Ideal (MvPolynomial σ K)) :
    weightedCore w Q ≤ Q := by
  classical
  intro f hf
  have h := (mem_weightedCore w Q f).mp hf
  rw [← sum_weightedHomogeneousComponent w f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp (w := w) f)]
  exact Q.sum_mem fun d _ => h d

/-- A homogeneous decomposition can be made irredundant and have distinct
radicals without losing any property closed under finite intersections. -/
theorem minimal_primary_with_property (P : Ideal R → Prop)
    (hP : ∀ s : Finset (Ideal R), (∀ J ∈ s, P J) → P (s.inf id))
    {I : Ideal R} {s : Finset (Ideal R)} (hs : s.inf id = I)
    (hsprimary : ∀ J ∈ s, J.IsPrimary) (hsP : ∀ J ∈ s, P J) :
    ∃ t : Finset (Ideal R), Submodule.IsMinimalPrimaryDecomposition I t ∧ ∀ J ∈ t, P J := by
  classical
  let t : Finset (Ideal R) :=
    (s.image fun J => s.filter fun Q => Q.radical = J.radical).image fun u => u.inf id
  have ht : t.inf id = I := by
    ext x
    simp only [t, Finset.inf_image, Submodule.mem_finsetInf, Finset.mem_filter,
      Function.comp_def, id_eq]
    rw [← hs]
    simp only [Submodule.mem_finsetInf, id_eq]
    constructor
    · intro h Q hQ
      exact h Q hQ Q ⟨hQ, rfl⟩
    · intro h J hJ Q hQ
      exact h Q hQ.1
  have htprimary : ∀ J ∈ t, J.IsPrimary := by
    intro J hJ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    apply Ideal.isPrimary_finsetInf (i := Q) (by simp [hQ])
    · intro T hT
      exact hsprimary T (Finset.mem_filter.mp hT).1
    · simp
  have htP : ∀ J ∈ t, P J := by
    intro J hJ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    exact hP _ fun T hT => hsP T (Finset.mem_filter.mp hT).1
  have htdistinct : (t : Set (Ideal R)).Pairwise
      (fun A B => (A.colon Set.univ).radical ≠ (B.colon Set.univ).radical) := by
    intro A hA B hB hne heq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hv
    have hrQ : ((s.filter fun U => U.radical = Q.radical).inf id).radical = Q.radical := by
      exact Ideal.radical_finset_inf (i := Q) (by simp [hQ]) (by simp)
    have hrT : ((s.filter fun U => U.radical = T.radical).inf id).radical = T.radical := by
      exact Ideal.radical_finset_inf (i := T) (by simp [hT]) (by simp)
    simp only [Submodule.colon_univ, hrQ, hrT] at heq
    exact hne (by simp only [heq])
  obtain ⟨u, hut, hu, humin⟩ := Submodule.decomposition_erase_inf ht
  exact ⟨u, ⟨hu, fun _ h => htprimary _ (hut h), htdistinct.mono hut, humin⟩,
    fun J hJ => htP J (hut hJ)⟩

end PhilipponMultiplicity.PrimarySupport


namespace PhilipponMultiplicity.PrimarySupport
open MvPolynomial
open Finsupp (weight weight_apply)
open Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

def blockCore (Q : Ideal M.CoordinateRing) : Ideal M.CoordinateRing :=
  weightedCore (fun x => (Finsupp.equivFunOnFinite).symm
    (blockWeight M.factorCount M.ambientDimension x)) Q

theorem blockCore_projection (f : M.CoordinateRing) (d : M.FactorIndex → ℕ) :
    weightedHomogeneousComponent
      (fun x => (Finsupp.equivFunOnFinite).symm
        (blockWeight M.factorCount M.ambientDimension x))
      ((Finsupp.equivFunOnFinite).symm d) f =
    weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d f := by
  classical
  have hw (e : M.Variable →₀ ℕ) :
      weight (fun x => (Finsupp.equivFunOnFinite).symm
          (blockWeight M.factorCount M.ambientDimension x)) e =
        (Finsupp.equivFunOnFinite).symm
          (weight (blockWeight M.factorCount M.ambientDimension) e) := by
    ext i
    simp [weight_apply, Finsupp.sum, Finset.sum_apply]
  ext e
  simp only [coeff_weightedHomogeneousComponent, hw, Equiv.apply_eq_iff_eq]

theorem mem_blockCore (Q : Ideal M.CoordinateRing) (f : M.CoordinateRing) :
    f ∈ blockCore M Q ↔ ∀ d : M.FactorIndex → ℕ,
      weightedHomogeneousComponent (blockWeight M.factorCount M.ambientDimension) d f ∈ Q := by
  rw [blockCore, mem_weightedCore]
  constructor
  · intro h d
    simpa only [blockCore_projection M] using h ((Finsupp.equivFunOnFinite).symm d)
  · intro h d
    obtain ⟨d, rfl⟩ := (Finsupp.equivFunOnFinite).symm.surjective d
    simpa only [blockCore_projection M] using h d

theorem blockCore_homogeneous (Q : Ideal M.CoordinateRing) :
    IsMultihomogeneousIdeal M (blockCore M Q) := by
  classical
  intro f hf d
  apply (mem_blockCore M Q _).mpr
  intro e
  rw [weightedHomogeneousComponent_of_mem (weightedHomogeneousComponent_mem _ f d)]
  split_ifs
  · exact (mem_blockCore M Q f).mp hf d
  · exact Q.zero_mem

theorem homogeneous_finsetInf (s : Finset (Ideal M.CoordinateRing))
    (hs : ∀ J ∈ s, IsMultihomogeneousIdeal M J) :
    IsMultihomogeneousIdeal M (s.inf id) := by
  intro f hf d
  simp only [Submodule.mem_finsetInf, id_eq] at hf ⊢
  exact fun J hJ => hs J hJ f (hf J hJ) d

theorem exists_minimal_homogeneous_primary (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) :
    ∃ t : Finset (Ideal M.CoordinateRing),
      Submodule.IsMinimalPrimaryDecomposition I t ∧
      ∀ J ∈ t, IsMultihomogeneousIdeal M J := by
  classical
  obtain ⟨s, hs, hsprimary⟩ := Submodule.isLasker M.CoordinateRing M.CoordinateRing I
  let t := s.image (blockCore M)
  have ht : t.inf id = I := by
    apply le_antisymm
    · rw [← hs]
      apply Finset.le_inf_iff.mpr
      intro J hJ
      exact (Finset.inf_le (Finset.mem_image.mpr ⟨J, hJ, rfl⟩)).trans
        (weightedCore_le _ J)
    · apply Finset.le_inf_iff.mpr
      intro J hJ
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
      intro f hf
      apply (mem_blockCore M Q f).mpr
      intro d
      have hIQ : I ≤ Q := hs.symm.le.trans (Finset.inf_le hQ)
      exact hIQ (hI f hf d)
  apply minimal_primary_with_property (IsMultihomogeneousIdeal M) (homogeneous_finsetInf M) ht
  · intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
    exact weightedCore_primary _ Q (hsprimary hQ)
  · intro J hJ
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hJ
    exact blockCore_homogeneous M Q

end PhilipponMultiplicity.PrimarySupport


namespace PhilipponMultiplicity.SectionThreeSupport
open PrimarySupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A finite minimal decomposition by actual multihomogeneous primary ideals,
over any field and including the whole-ring case with an empty family. -/
theorem exists_primaryDecomposition (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) : Nonempty (PrimaryDecomposition M I) := by
  classical
  obtain ⟨s, hs, hshom⟩ := exists_minimal_homogeneous_primary M I hI
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hiInf : (⨅ i : Fin (Fintype.card s), (e i).1) = s.inf id := by
    ext f
    simp only [Submodule.mem_iInf, Submodule.mem_finsetInf, id_eq]
    constructor
    · intro h J hJ
      obtain ⟨i, hi⟩ := e.surjective ⟨J, hJ⟩
      have := h i
      simpa only [hi] using this
    · intro h i
      exact h _ (e i).2
  refine ⟨{
    count := Fintype.card s
    component := fun i => (e i).1
    primary := fun i => hs.primary (e i).2
    homogeneous := fun i => hshom _ (e i).2
    intersection_eq := hs.inf_eq.symm.trans hiInf.symm
    irredundant := ?_
    radicals_injective := ?_ }⟩
  · intro i heq
    apply hs.minimal (e i).2
    calc
      (s.erase (e i).1).inf id ≤ ⨅ j : {j : Fin (Fintype.card s) // j ≠ i},
          (e j.1).1 := by
        apply le_iInf
        intro j
        apply Finset.inf_le
        refine Finset.mem_erase.mpr ⟨?_, (e j.1).2⟩
        exact fun h => j.2 (e.injective (Subtype.ext h))
      _ = I := heq
      _ ≤ (e i).1 := hs.inf_eq.symm.le.trans (Finset.inf_le (e i).2)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply hs.injOn I s (e i).2 (e j).2
    simpa only [Submodule.colon_univ] using hij

end PhilipponMultiplicity.SectionThreeSupport

end
end


section
-- Reused implementation: Solutions.PhilipponDimensionSlice
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection

theorem finite_iInf_le_prime {R ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Ideal R) (q : Ideal R) (hq : q.IsPrime) :
    (⨅ i, A i) ≤ q ↔ ∃ i, A i ≤ q := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
    (hq.inf_le' (s := Finset.univ) (f := A))

end PhilipponMultiplicity.ComponentSelection

end
end


section
-- Reused implementation: Solutions.PhilipponPrimaryComponentDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimaryComponentSupport

private theorem PhilipponPrimaryComponentDegree_localization_map_iInf {R ι : Type*} [CommRing R] [Finite ι]
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    (Q : ι → Ideal R) :
    (⨅ i, Q i).map (algebraMap R A) = ⨅ i, (Q i).map (algebraMap R A) := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Function.comp_def, IsLocalization.mapFrameHom_apply]
    using map_finset_inf (IsLocalization.mapFrameHom S A) Finset.univ Q

open SectionThree SectionThreeSupport ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The canonical contraction from a minimal-prime localization equals the
corresponding member of any minimal primary decomposition. -/
theorem primaryComponent_eq_decomposition (I : Ideal M.CoordinateRing)
    (D : PrimaryDecomposition M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    ∃ i : Fin D.count, (D.component i).radical = q.asIdeal ∧
      Hilbert.primaryComponent K M.factorCount M.ambientDimension I q = D.component i := by
  classical
  obtain ⟨i, hi⟩ := (finite_iInf_le_prime D.component q.asIdeal q.isPrime).mp
    (D.intersection_eq.symm.le.trans hq.1.2)
  have hrad (j : Fin D.count) (hj : D.component j ≤ q.asIdeal) :
      (D.component j).radical = q.asIdeal := by
    have hle := q.isPrime.radical_le_iff.mpr hj
    have hI : I ≤ (D.component j).radical :=
      (D.intersection_eq.le.trans (iInf_le D.component j)).trans Ideal.le_radical
    exact le_antisymm hle (hq.2 ⟨Ideal.isPrime_radical (D.primary j), hI⟩ hle)
  have hri := hrad i hi
  let A := Localization.AtPrime q.asIdeal
  let f := algebraMap M.CoordinateRing A
  have hmap : I.map f = (D.component i).map f := by
    apply (congrArg (Ideal.map f) D.intersection_eq).trans
    rw [PhilipponPrimaryComponentDegree_localization_map_iInf q.asIdeal.primeCompl A]
    apply le_antisymm (iInf_le _ i)
    refine le_iInf fun j => ?_
    by_cases heq : j = i
    · subst j; exact le_rfl
    · have hnot : ¬ D.component j ≤ q.asIdeal := by
        intro hj
        exact heq (D.radicals_injective ((hrad j hj).trans hri.symm))
      rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hnot]
      exact le_top
  refine ⟨i, hri, ?_⟩
  change (I.map f).comap f = D.component i
  rw [hmap]
  exact IsLocalization.under_map_of_isPrimary_disjoint q.asIdeal.primeCompl A (D.primary i)
    (Set.disjoint_left.mpr fun x hx hxI => hx (hi hxI))

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Isolated primary components of a multihomogeneous ideal are themselves
multihomogeneous, for the canonical localized-component definition. -/
theorem primaryComponent_homogeneous (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes) :
    IsMultihomogeneousIdeal M (primaryComponent K M.factorCount M.ambientDimension I q) := by
  obtain ⟨D⟩ := exists_primaryDecomposition M I hI
  obtain ⟨i, _, heq⟩ := PrimaryComponentSupport.primaryComponent_eq_decomposition M I D q hq
  rw [heq]
  exact D.homogeneous i


end PhilipponMultiplicity.Hilbert
end
end


section
-- Reused implementation: Solutions.PhilipponSelectedPrimary
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.PrimaryCut
open SectionThree SectionThreeSupport ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

abbrev MinComponent (J : Ideal M.CoordinateRing) :=
  Hilbert.MinimalComponent K M.factorCount M.ambientDimension J

abbrev primary (J : Ideal M.CoordinateRing) (p : PrimeSpectrum M.CoordinateRing) :=
  Hilbert.primaryComponent K M.factorCount M.ambientDimension J p

/-- A literal intersection of selected canonical isolated primary components. -/
def selectedIntersection (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop) :
    Ideal M.CoordinateRing := ⨅ p : {p : MinComponent M J // s p}, primary M J p.1.1

theorem le_selectedIntersection (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop) :
    J ≤ selectedIntersection M J s :=
  le_iInf fun _ => Ideal.le_comap_map

theorem selectedIntersection_le (J : Ideal M.CoordinateRing) (s : MinComponent M J → Prop)
    (p : MinComponent M J) (hp : s p) : selectedIntersection M J s ≤ primary M J p.1 :=
  iInf_le (fun q : {q : MinComponent M J // s q} => primary M J q.1.1) ⟨p,hp⟩

theorem primary_le_prime (J : Ideal M.CoordinateRing) (p : MinComponent M J) :
    primary M J p.1 ≤ p.1.asIdeal :=
  Ideal.le_radical.trans (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2).le

theorem selectedIntersection_le_prime_iff (J : Ideal M.CoordinateRing)
    (s : MinComponent M J → Prop) (q : Ideal M.CoordinateRing) (hq : q.IsPrime) :
    selectedIntersection M J s ≤ q ↔ ∃ p : MinComponent M J, s p ∧ p.1.asIdeal ≤ q := by
  rw [selectedIntersection, finite_iInf_le_prime _ q hq]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.1, p.2, ?_⟩
    rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1.1 p.1.2]
    exact hq.radical_le_iff.mpr hp
  · rintro ⟨p, hp, hpq⟩
    exact ⟨⟨p,hp⟩, (primary_le_prime M J p).trans hpq⟩

theorem selectedIntersection_minimalPrimes (J : Ideal M.CoordinateRing)
    (s : MinComponent M J → Prop) (q : Ideal M.CoordinateRing) :
    q ∈ (selectedIntersection M J s).minimalPrimes ↔
      ∃ p : MinComponent M J, s p ∧ p.1.asIdeal = q := by
  constructor
  · intro hq
    obtain ⟨p, hp, hpq⟩ := (selectedIntersection_le_prime_iff M J s q hq.1.1).mp hq.1.2
    have hNp := (selectedIntersection_le M J s p hp).trans (primary_le_prime M J p)
    exact ⟨p,hp,le_antisymm hpq (hq.2 ⟨p.1.isPrime,hNp⟩ hpq)⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p.1.isPrime, (selectedIntersection_le M J s p hp).trans (primary_le_prime M J p)⟩, ?_⟩
    intro q hq hqp
    exact p.2.2 ⟨hq.1,(le_selectedIntersection M J s).trans hq.2⟩ hqp

theorem selectedIntersection_homogeneous (J : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (s : MinComponent M J → Prop) :
    IsMultihomogeneousIdeal M (selectedIntersection M J s) := by
  intro f hf d
  simp only [selectedIntersection, Submodule.mem_iInf] at hf ⊢
  intro p
  exact Hilbert.primaryComponent_homogeneous M J hJ p.1.1 p.1.2 f
    (hf p) d


end PhilipponMultiplicity.PrimaryCut
end
end


section
-- Reused implementation: Solutions.PhilipponProjectiveHilbertExistence

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [MonomialCells.weight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d

theorem projective_hilbert_polynomial_exists
    (K : Type*) [Field K] (N : ℕ) (V : ProjectiveSubvariety K N) :
    ∃ P, Hilbert.IsHilbertPolynomial K 1 (fun _ => N)
      ((projectiveSpace K N).vanishingIdeal V.carrierInSingleFactor) P := by
  exact multigraded_hilbert_polynomial_exists K (projectiveSpace K N) _
    (vanishingIdeal_multihomogeneous K (projectiveSpace K N) V.carrierInSingleFactor)

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponGroupPrimeComponents
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.relevant_of_zeroLocus_nonempty {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (hne : (M.zeroLocus I).Nonempty) :
    Hilbert.IsRelevant K M.factorCount M.ambientDimension I := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hj (i : M.FactorIndex) : ∃ j, (x i).rep j ≠ 0 := by
    simpa only [ne_eq,funext_iff,Pi.zero_apply,not_forall] using
      (Projectivization.rep_nonzero (x i))
  choose j hj using hj
  let F : M.CoordinateRing := ∏ i, X ⟨i,j i⟩
  have hF : F ∈ Hilbert.irrelevantIdeal K M.factorCount M.ambientDimension := by
    apply Ideal.mem_iInf.mpr
    intro i
    apply Ideal.prod_mem _ (Finset.mem_univ i)
    exact Ideal.subset_span ⟨j i,rfl⟩
  intro hle
  have hz := hx F (hle hF)
  have hneF : M.eval F x ≠ 0 := by
    change MvPolynomial.eval (M.coordinate x) (∏ i, X ⟨i,j i⟩) ≠ 0
    simp only [map_prod,eval_X,MultiProjectiveSpace.coordinate]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hj i)
  exact hneF hz

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

theorem exists_minimalPrime_at_group_zero (I : Ideal G.CoordinateRing)
    (x : G.Point) (hx : x ∈ idealZeroLocusOnGroup G I) :
    ∃ q ∈ I.minimalPrimes, x ∈ idealZeroLocusOnGroup G q := by
  let e := MvPolynomial.eval (G.ambient.coordinate (G.embedding x))
  letI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨q,hq,hqe⟩ := Ideal.exists_minimalPrimes_le
    (show I ≤ RingHom.ker e from hx)
  exact ⟨q,hq,hqe⟩


end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponFiniteBasicCover

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

/-- A nonvanishing cover by finite-variable polynomials has a finite subcover,
even on an arbitrary subset of affine coordinate tuples. -/
theorem finite_polynomial_nonzero_cover {K σ X ι : Type*} [Field K] [Finite σ]
    (P : ι → MvPolynomial σ K) (v : X → σ → K)
    (hcover : ∀ x, ∃ i, MvPolynomial.eval (v x) (P i) ≠ 0) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, MvPolynomial.eval (v x) (P i) ≠ 0 := by
  classical
  obtain ⟨s,hs,hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial σ K) (Set.range P)).mp
      (IsNoetherian.noetherian (Ideal.span (Set.range P)))
  choose ind hind using (fun q : s => hs q.property)
  let t : Finset ι := Finset.univ.image ind
  refine ⟨t,?_⟩
  intro x
  by_contra hx
  push Not at hx
  have hle : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval (v x)) := by
    change Ideal.span (Set.range P) = Ideal.span (s : Set (MvPolynomial σ K)) at hspan
    rw [hspan]
    apply Ideal.span_le.mpr
    intro q hq
    change MvPolynomial.eval (v x) q = 0
    have hi : P (ind ⟨q,hq⟩) = q := hind ⟨q,hq⟩
    rw [← hi]
    exact hx (ind ⟨q,hq⟩) (Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩)
  obtain ⟨i,hi⟩ := hcover x
  exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Every open cover of an arbitrary multiprojective locus admits a finite
subcover. This supplies the finite family needed for uniform chart degrees. -/
theorem finite_open_subcover {X ι : Type*} (e : X → M.Point)
    (U : ι → Set M.Point) (hU : ∀ i, @IsOpen _ M.zariskiTopology (U i))
    (hcover : ∀ x, ∃ i, e x ∈ U i) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, e x ∈ U i := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  choose ind hind using hcover
  have hbasic (x : X) : ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
      M.eval P (e x) ≠ 0 ∧ {p : M.Point | M.eval P p ≠ 0} ⊆ U (ind x) := by
    obtain ⟨V,⟨P,D,hP,rfl⟩,hx,hV⟩ :=
      M.isTopologicalBasis_basic.exists_subset_of_mem_open (hind x) (hU (ind x))
    exact ⟨P,D,hP,hx,hV⟩
  choose P D hP hx hPU using hbasic
  obtain ⟨s,hs⟩ := finite_polynomial_nonzero_cover P (fun x => M.coordinate (e x))
    (fun x => ⟨x,hx x⟩)
  refine ⟨s.image ind,?_⟩
  intro x
  obtain ⟨y,hy,hyx⟩ := hs x
  exact ⟨ind y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hPU y hyx⟩

end MultiProjectiveSpace
end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponProjectiveTranslations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K] {n : ℕ}

def projectiveLeftSlice (a : Projectivization K (Fin (n + 1) → K))
    (p : (projectiveSpace K n).Point) : (projectiveSquare K n).Point :=
  fun b => if b.val = 0 then p (0 : Fin 1) else a

def projectiveLeftSlicePolynomial (a : Projectivization K (Fin (n + 1) → K))
    (v : (projectiveSquare K n).Variable) : (projectiveSpace K n).CoordinateRing :=
  if v.1.val = 0 then X ⟨(0 : Fin 1), v.2⟩ else C (a.rep v.2)

theorem projectiveLeftSlicePolynomial_homogeneous
    (a : Projectivization K (Fin (n + 1) → K)) (v : (projectiveSquare K n).Variable) :
    (projectiveSpace K n).IsHomogeneous (projectiveLeftSlicePolynomial a v)
      (fun _ => if v.1.val = 0 then 1 else 0) := by
  classical
  by_cases hv : v.1.val = 0
  · simp only [projectiveLeftSlicePolynomial, if_pos hv]
    convert (projectiveSpace K n).isHomogeneous_X ⟨(0 : Fin 1), v.2⟩ using 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    simp [hi]
  · simpa only [projectiveLeftSlicePolynomial, if_neg hv] using!
      (projectiveSpace K n).isHomogeneous_C (a.rep v.2)

theorem projectiveLeftSlice_eval (a : Projectivization K (Fin (n + 1) → K))
    (P : (projectiveSquare K n).CoordinateRing) (p : (projectiveSpace K n).Point) :
    (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p =
      (projectiveSquare K n).eval P (projectiveLeftSlice a p) := by
  dsimp only [MultiProjectiveSpace.eval]
  rw [← eval_assoc]
  apply congrArg (fun v => MvPolynomial.eval v P)
  funext v
  by_cases hv : v.1.val = 0 <;>
    simp [projectiveLeftSlicePolynomial, projectiveLeftSlice,
      MultiProjectiveSpace.coordinate, hv]

theorem projectiveLeftSlice_continuous (a : Projectivization K (Fin (n + 1) → K)) :
    @Continuous _ _ (projectiveSpace K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology (projectiveLeftSlice a) := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have heq : projectiveLeftSlice a ⁻¹' {p | (projectiveSquare K n).eval P p ≠ 0} =
      {p | (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0} := by
    ext p
    change (projectiveSquare K n).eval P (projectiveLeftSlice a p) ≠ 0 ↔
      (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0
    rw [projectiveLeftSlice_eval]
  rw [heq]
  apply (projectiveSpace K n).isOpen_basic
  exact hP.eval₂_blocks _ _ _ (fun b _ => if b.val = 0 then 1 else 0)
    (projectiveLeftSlicePolynomial_homogeneous a)

/-- Fixing one projective argument of a regular map gives a regular map. -/
theorem MultiProjectiveSpace.IsRegularAlong.of_left_slice
    {X : Type u} (N : MultiProjectiveSpace K)
    (a : Projectivization K (Fin (n + 1) → K))
    {e : X → (projectiveSpace K n).Point} {f : X → N.Point}
    (hf : (projectiveSquare K n).IsRegularAlong N (projectiveLeftSlice a ∘ e) f) :
    (projectiveSpace K n).IsRegularAlong N e f := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  let := (projectiveSquare K n).zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hlift⟩ := hf x b
  refine ⟨projectiveLeftSlice a ⁻¹' U, hU.preimage (projectiveLeftSlice_continuous a),
    hxU, (fun i => ∑ c, D c * (if c.val = 0 then 1 else 0)),
    (fun j => eval₂ C (projectiveLeftSlicePolynomial a) (P j)), ?_, ?_⟩
  · intro j
    exact (hP j).eval₂_blocks _ _ _ (fun c _ => if c.val = 0 then 1 else 0)
      (projectiveLeftSlicePolynomial_homogeneous a)
  · intro y hy
    obtain ⟨hn, heq⟩ := hlift y hy
    simpa only [projectiveLeftSlice_eval, Function.comp_apply] using ⟨hn, heq⟩

/-- The regular group law supplies regular translations. -/
theorem EmbeddedCommutativeGroup.translation_regular
    (G : EmbeddedCommutativeGroup K) (a : G.Point) :
    (projectiveSpace K G.ambientDimension).IsRegularAlong
      (projectiveSpace K G.ambientDimension)
      (fun x : G.Point => fun _ => x.val)
      (fun x => fun _ => (x + a).val) := by
  apply MultiProjectiveSpace.IsRegularAlong.of_left_slice _ a.val
  exact G.addition_regular.comp_domain (fun x : G.Point => (x, a))

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponRegularMapComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩

/-- Composition of regular maps, including maps given along arbitrary embedded domains. -/
theorem IsRegularAlong.comp {X : Type u} {M N Q : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} {g : X → Q.Point}
    (hf : M.IsRegularAlong N e f) (hg : N.IsRegularAlong Q f g) :
    M.IsRegularAlong Q e g := by
  classical
  let := M.zariskiTopology
  let := N.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hPlift⟩ := hg x b
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp (hU.preimage hf.continuous)
  choose W hW hxW E R hR hRlift using hf x
  let pull (j : Fin (Q.ambientDimension b + 1)) :=
    eval₂ C (fun t : N.Variable => R t.1 t.2) (P j)
  refine ⟨V ∩ ⋂ a, W a, hV.inter (isOpen_iInter_of_finite hW),
    ⟨?_, mem_iInter.mpr hxW⟩, (fun i => ∑ a, D a * E a i), pull, ?_, ?_⟩
  · have hx : x ∈ f ⁻¹' U := hxU
    rwa [← hVeq] at hx
  · intro j
    exact (hP j).eval₂_blocks M N _ E (fun t => hR t.1 t.2)
  · intro y hy
    have hyU : f y ∈ U := by
      change y ∈ f ⁻¹' U
      rw [← hVeq]
      exact hy.1
    obtain ⟨hn, heq⟩ := hPlift y hyU
    have hlift (a : N.FactorIndex) := hRlift a y (mem_iInter.mp hy.2 a)
    obtain ⟨hn', heq'⟩ := N.homogeneous_tuple_lift (f y)
      (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) hlift P D hP hn
    have heval (j) : M.eval (pull j) (e y) =
        MvPolynomial.eval (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) (P j) := by
      dsimp only [eval, pull]
      rw [← eval_assoc]
      rfl
    simpa only [heval] using ⟨hn', heq'.trans heq⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section
-- Reused implementation: Solutions.PhilipponProductRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem MultiProjectiveSpace.projection_regular (M : MultiProjectiveSpace K)
    (i : M.FactorIndex) :
    M.IsRegularAlong (projectiveSpace K (M.ambientDimension i)) id (fun p _ => p i) := by
  let := M.zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun a => if a = i then 1 else 0),
    (fun j => X ⟨i, j⟩), (fun j => M.isHomogeneous_X ⟨i, j⟩), ?_⟩
  intro y _
  simp only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate, id_eq]
  exact ⟨Projectivization.rep_nonzero (y i), Projectivization.mk_rep (y i)⟩

theorem EmbeddedGroupProduct.embedding_injective (G : EmbeddedGroupProduct K) :
    Function.Injective G.embedding := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem EmbeddedGroupProduct.embedding_locallyClosed (G : EmbeddedGroupProduct K) :
    @IsLocallyClosed _ G.ambient.zariskiTopology (range G.embedding) := by
  classical
  let := G.ambient.zariskiTopology
  have hloc (i : G.FactorIndex) : IsLocallyClosed {p : G.ambient.Point | p i ∈ (G.factor i).carrier} := by
    let := (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
    let := TopologicalSpace.induced
      (fun (x : Projectivization K (Fin ((G.factor i).ambientDimension + 1) → K)) (_ : Fin 1) => x)
      (projectiveSpace K (G.factor i).ambientDimension).zariskiTopology
    apply (G.factor i).locallyClosed.preimage
    apply continuous_induced_rng.mpr
    have h := (G.ambient.projection_regular i).continuous
    rw [induced_id] at h
    exact h
  choose U Z hU hZ hUZ using hloc
  refine ⟨⋂ i, U i, ⋂ i, Z i, isOpen_iInter_of_finite hU, isClosed_iInter hZ, ?_⟩
  have heq : range G.embedding = ⋂ i, {p : G.ambient.Point | p i ∈ (G.factor i).carrier} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_iInter.mpr (fun i => (x i).property)
    · intro hp
      exact ⟨(fun i => ⟨p i, mem_iInter.mp hp i⟩), rfl⟩
  rw [heq]
  simp only [hUZ, iInter_inter_distrib]

theorem EmbeddedGroupProduct.translation_regular (G : EmbeddedGroupProduct K) (a : G.Point) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (x + a)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have ht := ((G.factor b).translation_regular (a b)).comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp ht) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

theorem EmbeddedGroupProduct.negation_regular (G : EmbeddedGroupProduct K) :
    G.ambient.IsRegularAlong G.ambient G.embedding (fun x => G.embedding (-x)) := by
  intro x b
  have hp := (G.ambient.projection_regular b).comp_domain G.embedding
  have hn := (G.factor b).negation_regular.comp_domain (fun y : G.Point => y b)
  obtain ⟨U, hU, hx, D, P, hP, hl⟩ := (hp.comp hn) x (0 : Fin 1)
  exact ⟨U, hU, hx, D, P, hP, hl⟩

end PhilipponMultiplicity
end
end


section
-- Reused implementation: Solutions.PhilipponTranslationGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity
variable {K : Type*} [Field K] (G : EmbeddedGroupProduct K)

theorem EmbeddedGroupProduct.continuous_translation (g : G.Point) :
    @Continuous _ _ G.zariskiTopology G.zariskiTopology (fun x : G.Point => g+x) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  have hh : Continuous (fun x : G.Point => x+g) :=
    continuous_induced_rng.mpr (G.translation_regular g).continuous
  simpa only [add_comm] using hh

/-- Translation is a homeomorphism for the specified polynomial Zariski
topology. No topological-group instance is assumed. -/
def EmbeddedGroupProduct.translationHomeomorph (g : G.Point) :
    @Homeomorph G.Point G.Point G.zariskiTopology G.zariskiTopology := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact {
    toEquiv :=
      { toFun := fun x => g+x
        invFun := fun x => -g+x
        left_inv := fun x => by simp only [← add_assoc,neg_add_cancel,zero_add]
        right_inv := fun x => by simp only [← add_assoc,add_neg_cancel,zero_add] }
    continuous_toFun := G.continuous_translation g
    continuous_invFun := G.continuous_translation (-g) }

theorem isLocallyClosed_translate (g : G.Point) (V : Set G.Point)
    (hV : @IsLocallyClosed _ G.zariskiTopology V) :
    @IsLocallyClosed _ G.zariskiTopology (translate g V) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  have heq : translate g V = (fun x : G.Point => -g+x) ⁻¹' V := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,← add_assoc,neg_add_cancel,zero_add] using hy
    · intro hx
      exact ⟨-g+x,hx,by simp only [← add_assoc,add_neg_cancel,zero_add]⟩
  rw [heq]
  exact hV.preimage (G.continuous_translation (-g))

/-- Translation preserves the actual topological Krull dimension of every
subspace. Identifying it with the mission's Hilbert dimension is a separate
algebraic-geometric step in Lemma 4.5. -/
theorem topologicalKrullDim_translate (g : G.Point) (V : Set G.Point) :
    @topologicalKrullDim V (@TopologicalSpace.induced V G.Point Subtype.val G.zariskiTopology) =
      @topologicalKrullDim (translate g V)
        (@TopologicalSpace.induced (translate g V) G.Point Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  let e := (G.translationHomeomorph g).image V
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

theorem PolynomialTranslationChart.pullback_homogeneous {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    G.ambient.IsHomogeneous (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P)
      (fun i => chart.degree i * D i) := by
  classical
  have hh := hP.eval₂_blocks G.ambient G.ambient chart.coordinates
    (fun j i => if i=j then chart.degree i else 0) chart.homogeneous
  simpa [mul_ite,mul_comm] using hh

theorem PolynomialTranslationChart.pullback_eval_zero_iff {g : G.Point}
    (chart : PolynomialTranslationChart G g) (P : G.CoordinateRing)
    (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (x : G.Point) (hx : x ∈ chart.domain) :
    G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) = 0 ↔
      G.ambient.eval P (G.embedding (g+x)) = 0 := by
  have heval : G.ambient.eval (MvPolynomial.eval₂ MvPolynomial.C chart.coordinates P) (G.embedding x) =
      MvPolynomial.eval (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x)) P := by
    dsimp only [MultiProjectiveSpace.eval]
    rw [← MvPolynomial.eval_assoc]
    rfl
  rw [heval]
  exact G.ambient.eval_eq_zero_iff_of_lift (G.embedding (g+x))
    (fun v => G.ambient.eval (chart.coordinates v) (G.embedding x))
    (chart.represents x hx) P D hP

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponTranslationSeparation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem noetherian_induced {X : Type*} (e : X → M.Point) :
    @NoetherianSpace X (TopologicalSpace.induced e M.zariskiTopology) := by
  letI : TopologicalSpace M.Point := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  apply noetherianSpace_iff_isCompact.mpr
  intro S
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hcover
  choose W hW heq using fun i => isOpen_induced_iff.mp (hU i)
  obtain ⟨t,ht⟩ := M.finite_open_subcover (fun x : S => e x.val) W hW (by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover x.property)
    exact ⟨i,by change x.val ∈ e ⁻¹' W i; rwa [heq i]⟩)
  refine ⟨t,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := ht ⟨x,hx⟩
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,by rw [← heq i]; exact hxi⟩⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section
-- Reused implementation: Solutions.PhilipponConnectedGroupIrreducible

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

/-- A connected Noetherian space on which homeomorphisms act transitively
is irreducible. This uses only individual homeomorphisms, not a topological
group structure on the Zariski topology. -/
theorem irreducible_of_transitive_homeomorphisms {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [ConnectedSpace X]
    (htrans : ∀ x y : X, ∃ e : X ≃ₜ X, e x = y) : IrreducibleSpace X := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨U,hU,⟨p,hp⟩,hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨e,he⟩ := htrans p y
    have hopen : IsOpen (e '' U) := e.isOpenMap _ hU
    have hclosed : IsClosed (e '' C) := e.isClosedMap _
      (isClosed_of_mem_irreducibleComponents C hC)
    have hydense : C ⊆ closure (C ∩ e '' U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hopen
        ⟨y,hy,p,hp,he⟩
    have hCeC : C ⊆ e '' C := hydense.trans (closure_minimal
      (fun z hz => Set.image_mono hUC hz.2) hclosed)
    have heCC : e '' C ⊆ C := hC.2 (hC.1.image e e.continuous.continuousOn) hCeC
    exact Filter.mem_of_superset (hopen.mem_nhds ⟨p,hp,he⟩)
      ((Set.image_mono hUC).trans heCC)
  have hfull : C = univ := (show IsClopen C from
    ⟨isClosed_of_mem_irreducibleComponents C hC,hCopen⟩).eq_univ hC.1.nonempty
  exact { isPreirreducible_univ := by simpa only [hfull] using hC.1.2
          toNonempty := inferInstance }

variable {K : Type*} [Field K] {G : EmbeddedGroupProduct K}

def AlgebraicSubgroup.translationHomeomorph (H : AlgebraicSubgroup G)
    (a : H.toAddSubgroup) :
    @Homeomorph H.carrier H.carrier
      (TopologicalSpace.induced Subtype.val G.zariskiTopology)
      (TopologicalSpace.induced Subtype.val G.zariskiTopology) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (G.translationHomeomorph a.val).subtype (by
    intro x
    change x ∈ H.toAddSubgroup ↔ a.val+x ∈ H.toAddSubgroup
    exact ⟨fun hx => H.toAddSubgroup.add_mem a.property hx,fun hx => by
      have h := H.toAddSubgroup.add_mem (H.toAddSubgroup.neg_mem a.property) hx
      simpa only [← add_assoc,neg_add_cancel,zero_add] using h⟩)

/-- The actual connected algebraic subgroup is irreducible for the specified
polynomial Zariski topology, as used before Philippon's Lemma 4.6. -/
theorem AlgebraicSubgroup.isIrreducible_of_isConnected (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) : @IsIrreducible _ G.zariskiTopology H.carrier := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : NoetherianSpace G.Point := G.ambient.noetherian_induced G.embedding
  letI : ConnectedSpace H.carrier := isConnected_iff_connectedSpace.mp hH
  apply isIrreducible_iff_irreducibleSpace.mpr
  apply irreducible_of_transitive_homeomorphisms
  intro x y
  let a : H.toAddSubgroup := ⟨y.val-x.val,H.toAddSubgroup.sub_mem y.property x.property⟩
  refine ⟨H.translationHomeomorph a,?_⟩
  apply Subtype.ext
  change y.val-x.val+x.val = y.val
  exact sub_add_cancel _ _

theorem AlgebraicSubgroup.isIrreducible_translate (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    @IsIrreducible _ G.zariskiTopology (translate g H.carrier) := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  exact (H.isIrreducible_of_isConnected hH).image _ (G.continuous_translation g).continuousOn

/-- Irreducibility implies ordinary primality of the actual homogeneous
vanishing ideal, by the proved multigraded homogeneous-product criterion. -/
theorem MultiProjectiveSpace.vanishingIdeal_isPrime_of_isIrreducible
    (M : MultiProjectiveSpace K) (S : Set M.Point)
    (hS : @IsIrreducible _ M.zariskiTopology S) : (M.vanishingIdeal S).IsPrime := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  apply Hilbert.prime_of_homogeneous_products M _ (vanishingIdeal_multihomogeneous K M S)
  · intro htop
    obtain ⟨x,hx⟩ := hS.nonempty
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal
      (show (1 : M.CoordinateRing) ∈ M.vanishingIdeal S by rw [htop]; trivial) hx
    exact one_ne_zero (by simpa only [MultiProjectiveSpace.eval,map_one] using hz)
  · rintro P Q ⟨D,hP⟩ ⟨E,hQ⟩ hPQ
    by_contra! hn
    have hnzero (R : M.CoordinateRing) (d : M.FactorIndex → ℕ)
        (hR : M.IsHomogeneous R d) (hRI : R ∉ M.vanishingIdeal S) :
        (S ∩ {x | M.eval R x ≠ 0}).Nonempty := by
      by_contra hz
      apply hRI
      exact Ideal.subset_span ⟨⟨d,hR⟩,fun x hx => by
        by_contra hxR
        exact hz ⟨x,hx,hxR⟩⟩
    obtain ⟨x,hx,hxP,hxQ⟩ := hS.2 _ _ (M.isOpen_basic P D hP)
      (M.isOpen_basic Q E hQ) (hnzero P D hP hn.1) (hnzero Q E hQ hn.2)
    have hz := M.eval_eq_zero_of_mem_vanishingIdeal hPQ hx
    exact (mul_ne_zero hxP hxQ) (by simpa only [MultiProjectiveSpace.eval,map_mul] using hz)

/-- The coset prime used in the opening paragraph of Section 4.2 is the
mission's actual vanishing ideal. -/
theorem AlgebraicSubgroup.translated_vanishingIdeal_isPrime (H : AlgebraicSubgroup G)
    (hH : H.IsConnected) (g : G.Point) :
    (G.vanishingIdeal (translate g H.carrier)).IsPrime := by
  letI : TopologicalSpace G.Point := G.zariskiTopology
  letI : TopologicalSpace G.ambient.Point := G.ambient.zariskiTopology
  exact G.ambient.vanishingIdeal_isPrime_of_isIrreducible _
    ((H.isIrreducible_translate hH g).image G.embedding
      (show Continuous G.embedding from continuous_induced_dom).continuousOn)

end PhilipponMultiplicity

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzGlobalization
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MWGlobalization

variable {K : Type*} [NontriviallyNormedField K] (G : EmbeddedGroupProduct K)

def equationIdeal (Q : Finset G.CoordinateRing) : Ideal G.CoordinateRing :=
  G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)

theorem equationIdeal_homogeneous (Q : Finset G.CoordinateRing)
    (hQ : ∀ P ∈ Q, ∃ D, G.ambient.IsHomogeneous P D) :
    IsMultihomogeneousIdeal G.ambient (equationIdeal G Q) := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    simpa [equationIdeal,EmbeddedGroupProduct.vanishingIdeal] using vanishingIdeal_multihomogeneous K G.ambient
      (G.embedding '' Set.univ)
  | @insert P Q hPQ ih =>
    obtain ⟨D,hD⟩ := hQ P (Finset.mem_insert_self P Q)
    have hh := Hilbert.homogeneous_sup_span G.ambient (equationIdeal G Q)
      (ih (fun F hF => hQ F (Finset.mem_insert_of_mem hF))) P D hD
    simpa only [equationIdeal,Finset.coe_insert,Ideal.span_insert,
      sup_assoc,sup_left_comm,sup_comm] using hh

theorem zero_equationIdeal (Q : Finset G.CoordinateRing) :
    idealZeroLocusOnGroup G (equationIdeal G Q) =
      {x | ∀ P ∈ Q, G.ambient.eval P (G.embedding x) = 0} := by
  ext x
  constructor
  · intro hx P hP
    exact hx P ((show Ideal.span (Q : Set G.CoordinateRing) ≤ equationIdeal G Q from
      le_sup_right) (Ideal.subset_span hP))
  · intro hx
    have hle : equationIdeal G Q ≤
        RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
      apply sup_le
      · intro P hP
        exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal hP ⟨x,Set.mem_univ x,rfl⟩
      · exact Ideal.span_le.mpr hx
    exact hle


end PhilipponMultiplicity.MWGlobalization
end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzCutInduction

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MWCutInduction
open SectionThree PrimaryCut

section Algebra
variable {K : Type*} [Field K]

/-- An intersection of isolated primary components has no additional
zero-divisors supported away from its selected minimal primes. -/
theorem selected_regular (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing)
    (s : MinComponent M I → Prop) (Q : M.CoordinateRing)
    (hQ : ∀ p ∈ (selectedIntersection M I s).minimalPrimes, Q ∉ p) :
    IsRegular (Ideal.Quotient.mk (selectedIntersection M I s) Q) := by
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hQf : Q * f ∈ selectedIntersection M I s := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul]
    exact hz
  simp only [selectedIntersection, Submodule.mem_iInf] at hQf ⊢
  intro p
  have hp := Hilbert.primaryComponent_isPrimary K M.factorCount M.ambientDimension
    I p.1.1 p.1.2
  have hn : Q ∉ (primary M I p.1.1).radical := by
    rw [Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension I p.1.1 p.1.2]
    exact hQ _ ((selectedIntersection_minimalPrimes M I s _).mpr ⟨p.1,p.2,rfl⟩)
  exact ((Ideal.isPrimary_iff.mp hp).2 (mul_comm Q f ▸ hQf p)).resolve_right hn

theorem degree_fin_one (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem eval_top_fin_one (F : MvPolynomial (Fin 1) ℚ) (d : Fin 1 → ℚ) :
    eval d (homogeneousComponent F.totalDegree F) =
      coeff (Finsupp.single 0 F.totalDegree) F * d 0 ^ F.totalDegree := by
  have ht : homogeneousComponent F.totalDegree F =
      monomial (Finsupp.single 0 F.totalDegree) (coeff (Finsupp.single 0 F.totalDegree) F) := by
    classical
    ext v
    rw [coeff_homogeneousComponent, coeff_monomial]
    have hv : v.degree = F.totalDegree ↔ Finsupp.single 0 F.totalDegree = v := by
      rw [degree_fin_one]
      constructor
      · intro h
        apply Finsupp.ext
        intro i
        fin_cases i
        simpa using h.symm
      · intro h
        rw [← h, Finsupp.single_eq_same]
    by_cases h : v.degree = F.totalDegree
    · rw [if_pos h, if_pos (hv.mp h), ← hv.mp h]
    · rw [if_neg h, if_neg (mt hv.mpr h)]
  rw [ht, eval_monomial, Finsupp.prod_single_index]
  simp

/-- On one projective factor, evaluating the degree form at d multiplies
the ordinary degree by d to the actual Hilbert dimension. -/
theorem degree_scale (N : ℕ) (I : Ideal (projectiveSpace K N).CoordinateRing) (d : ℕ) :
    idealDegreeValue (projectiveSpace K N) I (fun _ => d) =
      idealDegreeValue (projectiveSpace K N) I (fun _ => 1) *
        (d : ℚ) ^ idealDimension (projectiveSpace K N) I := by
  let F := Hilbert.hilbertPolynomial K 1 (fun _ => N) I
  change eval (fun _ : Fin 1 => (d : ℚ)) ((F.totalDegree.factorial : ℚ) •
      homogeneousComponent F.totalDegree F) =
    eval (fun _ : Fin 1 => (1 : ℚ)) ((F.totalDegree.factorial : ℚ) •
      homogeneousComponent F.totalDegree F) * (d : ℚ) ^ F.totalDegree
  simp only [smul_eq_C_mul, map_mul, eval_C, eval_top_fin_one,
    one_pow, mul_one]
  ring

end Algebra
variable {K : Type*} [NontriviallyNormedField K]

/-- Retaining all components that meet Gamma commutes with adding one
equation at the level of those minimal primes. -/
theorem retained_minimal_after_cut (G : EmbeddedGroupProduct K)
    (Γ : Submodule ℤ G.Point) (I J : Ideal G.CoordinateRing) (hIJ : I ≤ J)
    (hretain : ∀ p ∈ I.minimalPrimes,
      (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p) → p ∈ J.minimalPrimes)
    (Q : G.CoordinateRing) (q : Ideal G.CoordinateRing)
    (hq : q ∈ (I ⊔ Ideal.span {Q}).minimalPrimes)
    (hmeet : ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) :
    q ∈ (J ⊔ Ideal.span {Q}).minimalPrimes := by
  letI := hq.isPrime
  obtain ⟨p,hp,hpq⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hq.le)
  have hpmeet : ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p := by
    obtain ⟨x,hx,hxq⟩ := hmeet
    exact ⟨x,hx,fun f hf => hxq f (hpq hf)⟩
  have hJq := (hretain p hp hpmeet).le.trans hpq
  refine ⟨⟨hq.isPrime,sup_le hJq (le_sup_right.trans hq.le)⟩,?_⟩
  intro r hr hrq
  exact hq.2 ⟨hr.1,(sup_le_sup_right hIJ _).trans hr.2⟩ hrq

/-- A nonempty regular hypersurface cut has pure relevant dimension one
less. Retaining its isolated primary components meeting Gamma preserves
this dimension, costs at most d times the degree, and restores the
regularity-by-prime-avoidance invariant for the next cut. -/
theorem retained_cut (E : EmbeddedCommutativeGroup K)
    (Γ : Submodule ℤ (singleGroupProduct E).Point)
    (I : Ideal (singleGroupProduct E).CoordinateRing)
    (hI : IsMultihomogeneousIdeal (singleGroupProduct E).ambient I)
    (hequi : ∀ p ∈ I.minimalPrimes,
      idealDimension (singleGroupProduct E).ambient p =
        idealDimension (singleGroupProduct E).ambient I)
    (Q : (singleGroupProduct E).CoordinateRing) (d : ℕ) (hd : 0 < d)
    (hQ : (singleGroupProduct E).ambient.IsHomogeneous Q (fun _ => d))
    (hregular : IsRegular (Ideal.Quotient.mk I Q))
    (hzero : (0 : (singleGroupProduct E).Point) ∈
      idealZeroLocusOnGroup (singleGroupProduct E) (I ⊔ Ideal.span {Q})) :
    ∃ J : Ideal (singleGroupProduct E).CoordinateRing,
      IsMultihomogeneousIdeal (singleGroupProduct E).ambient J ∧
      I ⊔ Ideal.span {Q} ≤ J ∧
      (∀ p ∈ J.minimalPrimes,
        idealDimension (singleGroupProduct E).ambient p =
          idealDimension (singleGroupProduct E).ambient J) ∧
      idealDimension (singleGroupProduct E).ambient J + 1 =
        idealDimension (singleGroupProduct E).ambient I ∧
      idealDegreeValue (singleGroupProduct E).ambient J (fun _ => 1) ≤
        (d : ℚ) * idealDegreeValue (singleGroupProduct E).ambient I (fun _ => 1) ∧
      (∀ p, p ∈ J.minimalPrimes ↔
        p ∈ (I ⊔ Ideal.span {Q}).minimalPrimes ∧
          ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup (singleGroupProduct E) p) ∧
      (∀ f, (∀ p ∈ J.minimalPrimes, f ∉ p) → IsRegular (Ideal.Quotient.mk J f)) := by
  classical
  let G := singleGroupProduct E
  let M := G.ambient
  let A := I ⊔ Ideal.span {Q}
  let s : MinComponent M A → Prop := fun p => ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p.1.asIdeal
  let J := selectedIntersection M A s
  have hA := Hilbert.homogeneous_sup_span M I hI Q (fun _ => d) hQ
  have hJ := selectedIntersection_homogeneous M A hA s
  have hAJ : A ≤ J := le_selectedIntersection M A s
  have hmin (p : Ideal M.CoordinateRing) : p ∈ J.minimalPrimes ↔
      p ∈ A.minimalPrimes ∧ ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p := by
    rw [selectedIntersection_minimalPrimes]
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨q.2,hq⟩
    · rintro ⟨hp,hmeet⟩
      exact ⟨⟨⟨p,hp.isPrime⟩,hp⟩,hmeet,rfl⟩
  have hcut (p) (hp : p ∈ A.minimalPrimes)
      (hpr : Hilbert.IsRelevant K M.factorCount M.ambientDimension p) :
      idealDimension M p + 1 = idealDimension M I :=
    Hilbert.equidimensional_regular_cut_component_dimension M I hI
      (fun p hp _ => hequi p hp) Q (fun _ => d) hQ hregular p hp hpr
  obtain ⟨p,hp,hp0⟩ := exists_minimalPrime_at_group_zero G A 0 hzero
  have hpr := M.relevant_of_zeroLocus_nonempty p ⟨G.embedding 0,hp0⟩
  have hpJ : p ∈ J.minimalPrimes := (hmin p).mpr ⟨hp,0,Γ.zero_mem,hp0⟩
  have hdimA : idealDimension M A + 1 = idealDimension M I := by
    have hupper := Hilbert.idealDimension_le_of_minimalPrimes M A hA
      (idealDimension M I - 1) (by
        intro q hq hqr
        have := hcut q hq hqr
        omega)
    have hlower := Hilbert.idealDimension_antitone M A p hA
      (Hilbert.minimalPrime_homogeneous M A p hA hp) hp.le
    have := hcut p hp hpr
    omega
  have hdimJ : idealDimension M J = idealDimension M A := by
    apply le_antisymm (Hilbert.idealDimension_antitone M A J hA hJ hAJ)
    have hlower := Hilbert.idealDimension_antitone M J p hJ
      (Hilbert.minimalPrime_homogeneous M A p hA hp) hpJ.le
    have := hcut p hp hpr
    omega
  have hdegA : idealDegreeValue M A (fun _ => 1) =
      (d : ℚ) * idealDegreeValue M I (fun _ => 1) := by
    have hv := Hilbert.regular_cut_degreeValue_of_dimension M I hI Q (fun _ => d)
      hQ hregular hdimA
    change idealDegreeValue M A (fun _ => d) = idealDegreeValue M I (fun _ => d) at hv
    have hscale (L : Ideal M.CoordinateRing) : idealDegreeValue M L (fun _ => d) =
        idealDegreeValue M L (fun _ => 1) * (d : ℚ) ^ idealDimension M L :=
      degree_scale E.ambientDimension L d
    rw [hscale A, hscale I, ← hdimA, pow_succ] at hv
    have hdq : (d : ℚ) ^ idealDimension M A ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
    apply (mul_right_cancel₀ hdq)
    calc
      _ = idealDegreeValue M I (fun _ => 1) *
          ((d : ℚ) ^ idealDimension M A * d) := hv
      _ = _ := by ring
  refine ⟨J,hJ,hAJ,?_,?_,?_,hmin,selected_regular M A s⟩
  · intro q hq
    change idealDimension M q = idealDimension M J
    obtain ⟨hqA,x,hx,hxq⟩ := (hmin q).mp hq
    have := hcut q hqA (M.relevant_of_zeroLocus_nonempty q ⟨G.embedding x,hxq⟩)
    omega
  · change idealDimension M J + 1 = idealDimension M I
    omega
  · exact (Hilbert.degreeValue_antitone_of_dimension_eq M A J hA hJ hAJ hdimJ.symm _).trans_eq hdegA

end PhilipponMultiplicity.MWCutInduction

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzTerminal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MWCutInduction
open SectionThree MWGlobalization
variable {K : Type*} [NontriviallyNormedField K]

theorem single_group_dimension (E : EmbeddedCommutativeGroup K) :
    idealDimension (singleGroupProduct E).ambient
      ((singleGroupProduct E).vanishingIdeal Set.univ) = (singleGroupProduct E).dimension := by
  have himage : (singleGroupProduct E).embedding '' Set.univ =
      (fun x => fun _ : Fin 1 => x) '' E.carrier := by
    ext x
    constructor
    · rintro ⟨y,_,rfl⟩
      refine ⟨(y (0 : Fin 1)).val,(y (0 : Fin 1)).property,?_⟩
      funext i
      fin_cases i
      rfl
    · rintro ⟨y,hy,rfl⟩
      exact ⟨fun _ => ⟨y,hy⟩,Set.mem_univ _,rfl⟩
  simp only [idealDimension, EmbeddedGroupProduct.vanishingIdeal, himage]
  simp [EmbeddedGroupProduct.dimension,singleGroupProduct,EmbeddedCommutativeGroup.dimension,
    EmbeddedGroupProduct.ambient,projectiveSpace]

theorem connected_group_prime (G : EmbeddedGroupProduct K)
    (hconnected : @_root_.IsConnected _ G.zariskiTopology Set.univ) :
    (G.vanishingIdeal Set.univ).IsPrime := by
  letI := G.zariskiTopology
  letI := G.ambient.zariskiTopology
  let H : AlgebraicSubgroup G := ⟨⊤,isClosed_univ⟩
  exact G.ambient.vanishingIdeal_isPrime_of_isIrreducible _
    ((H.isIrreducible_of_isConnected hconnected).image G.embedding
      (show Continuous G.embedding from continuous_induced_dom).continuousOn)

theorem zero_mem_grid (G : EmbeddedGroupProduct K) {m : ℕ}
    (γ : Fin m → G.Point) {S : ℝ} (hS : 0 ≤ S) : 0 ∈ samplingGrid γ S :=
  ⟨fun _ => 0,fun _ => by simpa using hS,by simp⟩

theorem grid_mono (G : EmbeddedGroupProduct K) {m : ℕ}
    (γ : Fin m → G.Point) {S T : ℝ} (hST : S ≤ T) :
    samplingGrid γ S ⊆ samplingGrid γ T := by
  rintro x ⟨v,hv,rfl⟩
  exact ⟨v,fun i => (hv i).trans hST,rfl⟩

theorem pad_initial_equation (G : EmbeddedGroupProduct K)
    (hprime : (G.vanishingIdeal Set.univ).IsPrime)
    (D : ℕ) (P : G.CoordinateRing)
    (hP : G.ambient.IsHomogeneousAtMost P (fun _ => D))
    (hnonzero : ∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) :
    ∃ Q : G.CoordinateRing, Q ∈ Ideal.span ({P} : Set G.CoordinateRing) ∧
      G.ambient.IsHomogeneous Q (fun _ => D) ∧ Q ∉ G.vanishingIdeal Set.univ := by
  classical
  have hPnot : P ∉ G.vanishingIdeal Set.univ := by
    intro h
    obtain ⟨x,hx⟩ := hnonzero
    exact hx (G.ambient.eval_eq_zero_of_mem_vanishingIdeal h ⟨x,Set.mem_univ _,rfl⟩)
  have hrel := G.ambient.relevant_of_zeroLocus_nonempty (G.vanishingIdeal Set.univ)
    ⟨G.embedding 0,fun f hf => G.ambient.eval_eq_zero_of_mem_vanishingIdeal hf
      ⟨0,Set.mem_univ _,rfl⟩⟩
  obtain ⟨d,hd,hPhom⟩ := hP
  obtain ⟨v,hv⟩ := Hilbert.relevant_variables G.ambient _ hrel
  let B : G.CoordinateRing := ∏ i, (X ⟨i,v i⟩ : G.CoordinateRing) ^ (D-d i)
  have hB := Hilbert.variable_product_homogeneous G.ambient v (fun i => D-d i)
  have hBnot := Hilbert.variable_product_notMem G.ambient _ hprime v hv (fun i => D-d i)
  have hdeg : d + (fun i => D-d i) = (fun _ => D) := by
    funext i
    simp only [Pi.add_apply]
    exact Nat.add_sub_of_le (hd i)
  refine ⟨P*B,(Ideal.span {P}).mul_mem_right B (Ideal.subset_span (Set.mem_singleton P)),?_,?_⟩
  · rw [← hdeg]
    exact (G.ambient.degreePiece_iff _ _).mp
      (((G.ambient.degreePiece_iff P d).mpr hPhom).mul
        ((G.ambient.degreePiece_iff B _).mpr hB))
  · exact fun h => (hprime.mem_or_mem h).elim hPnot hBnot

/-- The induction keeps the original equations separate from the
intersection of primary components retained along the sampling subgroup. -/
def Stage (E : EmbeddedCommutativeGroup K)
    (Γ : Submodule ℤ (singleGroupProduct E).Point) {m : ℕ}
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (a D : ℕ) (X : ℝ) (r : ℕ) : Prop :=
  let G := singleGroupProduct E
  ∃ F : Finset G.CoordinateRing,
    (∀ Q ∈ F, ∃ d : G.FactorIndex → ℕ,
      G.ambient.IsHomogeneous Q d ∧ ∀ i, d i ≤ a ^ (r-1) * D) ∧
    (∀ Q ∈ F, ∀ x ∈ samplingGrid γ (((G.dimension-r+1 : ℕ) : ℝ)*R),
      G.ambient.eval Q (G.embedding x) = 0) ∧
    ∃ J : Ideal G.CoordinateRing, IsMultihomogeneousIdeal G.ambient J ∧
      equationIdeal G F ≤ J ∧
      (∀ p ∈ J.minimalPrimes, idealDimension G.ambient p = idealDimension G.ambient J) ∧
      idealDimension G.ambient J = G.dimension-r ∧
      ((idealDegreeValue G.ambient J (fun _ => 1) : ℚ) : ℝ) ≤ X^r ∧
      (∀ p ∈ J.minimalPrimes, ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p) ∧
      (∀ p ∈ (equationIdeal G F).minimalPrimes,
        (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G p) → p ∈ J.minimalPrimes) ∧
      (∀ f, (∀ p ∈ J.minimalPrimes, f ∉ p) → IsRegular (Ideal.Quotient.mk J f))

theorem initial_stage (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (Γ : Submodule ℤ (singleGroupProduct E).Point) {m : ℕ}
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 0 ≤ R)
    (a D : ℕ) (hD : 0 < D) (X : ℝ)
    (hdegree : (D : ℝ) *
      (idealDegreeValue (singleGroupProduct E).ambient
        ((singleGroupProduct E).vanishingIdeal Set.univ) (fun _ => 1) : ℝ) ≤ X)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D))
    (hvanish : ∀ x ∈ samplingGrid γ (((singleGroupProduct E).dimension : ℝ)*R),
      (singleGroupProduct E).ambient.eval P ((singleGroupProduct E).embedding x) = 0)
    (hnonzero : ∃ x, (singleGroupProduct E).ambient.eval P ((singleGroupProduct E).embedding x) ≠ 0) :
    Stage E Γ γ R a D X 1 := by
  classical
  let G := singleGroupProduct E
  let I := G.vanishingIdeal Set.univ
  have hp : I.IsPrime := connected_group_prime G hconnected
  letI : I.IsPrime := hp
  have hI : IsMultihomogeneousIdeal G.ambient I := vanishingIdeal_multihomogeneous K _ _
  obtain ⟨Q,hQspan,hQ,hQnot⟩ := pad_initial_equation G hp D P hP hnonzero
  have hQvan (x) (hx : x ∈ samplingGrid γ ((G.dimension : ℝ)*R)) :
      G.ambient.eval Q (G.embedding x) = 0 := by
    have hle : Ideal.span ({P} : Set G.CoordinateRing) ≤
        RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding x))) := by
      apply Ideal.span_le.mpr
      rintro f rfl
      exact hvanish x hx
    exact hle hQspan
  have hzero : (0 : G.Point) ∈ idealZeroLocusOnGroup G (I ⊔ Ideal.span {Q}) := by
    change I ⊔ Ideal.span {Q} ≤ RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding 0)))
    apply sup_le
    · intro f hf
      exact G.ambient.eval_eq_zero_of_mem_vanishingIdeal hf ⟨0,Set.mem_univ _,rfl⟩
    · apply Ideal.span_le.mpr
      rintro f rfl
      exact hQvan 0 (zero_mem_grid G γ (mul_nonneg (Nat.cast_nonneg _) hR))
  have hequi (p : Ideal G.CoordinateRing) (hpm : p ∈ I.minimalPrimes) :
      idealDimension G.ambient p = idealDimension G.ambient I := by
    have heq : p = I := le_antisymm (hpm.2 ⟨hp,le_rfl⟩ hpm.le) hpm.le
    rw [heq]
  have hregular : IsRegular (Ideal.Quotient.mk I Q) :=
    isRegular_iff_ne_zero.mpr (fun h => hQnot (Ideal.Quotient.eq_zero_iff_mem.mp h))
  obtain ⟨J,hJ,hIJ,hequiJ,hdim,hdeg,hmin,hreg⟩ :=
    retained_cut E Γ I hI hequi Q D hD hQ hregular hzero
  have hdimI : idealDimension G.ambient I = G.dimension := single_group_dimension E
  refine ⟨{Q},?_,?_,J,hJ,?_,hequiJ,?_,?_,?_,?_,hreg⟩
  · intro f hf
    have heq : f = Q := Finset.mem_singleton.mp hf
    subst f
    exact ⟨fun _ => D,hQ,by simp⟩
  · intro f hf x hx
    have heq : f = Q := Finset.mem_singleton.mp hf
    subst f
    have heq : G.dimension-1+1 = G.dimension := Nat.sub_add_cancel hn
    change x ∈ samplingGrid γ (((G.dimension-1+1 : ℕ) : ℝ)*R) at hx
    exact hQvan x (by simpa only [heq] using hx)
  · simpa only [equationIdeal,Finset.coe_singleton] using hIJ
  · change idealDimension G.ambient J = G.dimension-1
    change idealDimension G.ambient J + 1 = idealDimension G.ambient I at hdim
    omega
  · have hdegR : (idealDegreeValue G.ambient J (fun _ => 1) : ℝ) ≤
        (D : ℝ) * (idealDegreeValue G.ambient I (fun _ => 1) : ℝ) := by exact_mod_cast hdeg
    simpa only [pow_one] using hdegR.trans hdegree
  · intro p hp
    exact ((hmin p).mp hp).2
  · intro p hp hmeet
    apply (hmin p).mpr
    exact ⟨by simpa only [equationIdeal,Finset.coe_singleton] using hp,hmeet⟩

theorem advance_stage (E : EmbeddedCommutativeGroup K)
    (Γ : Submodule ℤ (singleGroupProduct E).Point) {m : ℕ}
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 0 ≤ R)
    (a D : ℕ) (ha : 1 ≤ a) (hD : 0 < D) (X : ℝ) (hX : 0 ≤ X)
    (hXbound : ((a ^ (singleGroupProduct E).dimension * D : ℕ) : ℝ) ≤ X)
    (r : ℕ) (_hr : 1 ≤ r) (hrn : r ≤ (singleGroupProduct E).dimension)
    (F : Finset (singleGroupProduct E).CoordinateRing)
    (J : Ideal (singleGroupProduct E).CoordinateRing)
    (hF : ∀ f ∈ F, ∃ d : (singleGroupProduct E).FactorIndex → ℕ,
      (singleGroupProduct E).ambient.IsHomogeneous f d ∧ ∀ i, d i ≤ a ^ (r-1) * D)
    (hFvan : ∀ f ∈ F, ∀ x ∈ samplingGrid γ
      ((((singleGroupProduct E).dimension-r+1 : ℕ) : ℝ)*R),
      (singleGroupProduct E).ambient.eval f ((singleGroupProduct E).embedding x) = 0)
    (hJ : IsMultihomogeneousIdeal (singleGroupProduct E).ambient J)
    (hIJ : equationIdeal (singleGroupProduct E) F ≤ J)
    (hequi : ∀ p ∈ J.minimalPrimes,
      idealDimension (singleGroupProduct E).ambient p = idealDimension (singleGroupProduct E).ambient J)
    (hdim : idealDimension (singleGroupProduct E).ambient J = (singleGroupProduct E).dimension-r)
    (hdeg : (idealDegreeValue (singleGroupProduct E).ambient J (fun _ => 1) : ℝ) ≤ X^r)
    (hretain : ∀ p ∈ (equationIdeal (singleGroupProduct E) F).minimalPrimes,
      (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup (singleGroupProduct E) p) → p ∈ J.minimalPrimes)
    (hreg : ∀ f, (∀ p ∈ J.minimalPrimes, f ∉ p) → IsRegular (Ideal.Quotient.mk J f))
    (Q : (singleGroupProduct E).CoordinateRing)
    (hQ : (singleGroupProduct E).ambient.IsHomogeneous Q (fun _ => a^r*D))
    (hQvan : ∀ x ∈ samplingGrid γ ((((singleGroupProduct E).dimension-r : ℕ) : ℝ)*R),
      (singleGroupProduct E).ambient.eval Q ((singleGroupProduct E).embedding x) = 0)
    (havoid : ∀ p ∈ J.minimalPrimes, Q ∉ p) :
    r < (singleGroupProduct E).dimension ∧ Stage E Γ γ R a D X (r+1) := by
  classical
  let G := singleGroupProduct E
  have hzeroI : (0 : G.Point) ∈ idealZeroLocusOnGroup G (equationIdeal G F) := by
    rw [zero_equationIdeal]
    exact fun f hf => hFvan f hf 0 (zero_mem_grid G γ (mul_nonneg (Nat.cast_nonneg _) hR))
  obtain ⟨p,hp,hp0⟩ := exists_minimalPrime_at_group_zero G (equationIdeal G F) 0 hzeroI
  have hpJ := hretain p hp ⟨0,Γ.zero_mem,hp0⟩
  have hzero : (0 : G.Point) ∈ idealZeroLocusOnGroup G (J ⊔ Ideal.span {Q}) := by
    change J ⊔ Ideal.span {Q} ≤ RingHom.ker (MvPolynomial.eval (G.ambient.coordinate (G.embedding 0)))
    apply sup_le
    · exact fun f hf => hp0 f (hpJ.le hf)
    · apply Ideal.span_le.mpr
      rintro f rfl
      exact hQvan 0 (zero_mem_grid G γ (mul_nonneg (Nat.cast_nonneg _) hR))
  obtain ⟨J',hJ',hJJ',hequi',hdim',hdeg',hmin',hreg'⟩ :=
    retained_cut E Γ J hJ hequi Q (a^r*D) (Nat.mul_pos (pow_pos (by omega) _) hD)
      hQ (hreg Q havoid) hzero
  have hrlt : r < G.dimension := by
    change idealDimension G.ambient J' + 1 = idealDimension G.ambient J at hdim'
    change idealDimension G.ambient J = G.dimension-r at hdim
    change r ≤ G.dimension at hrn
    omega
  have hnext : G.dimension-(r+1)+1 = G.dimension-r := by omega
  have heqI : equationIdeal G (insert Q F) = equationIdeal G F ⊔ Ideal.span {Q} := by
    simp only [equationIdeal,Finset.coe_insert,Ideal.span_insert]
    rw [sup_comm (Ideal.span {Q}) (Ideal.span (F : Set G.CoordinateRing)),← sup_assoc]
  refine ⟨hrlt,insert Q F,?_,?_,J',hJ',?_,hequi',?_,?_,?_,?_,hreg'⟩
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact ⟨fun _ => a^r*D,hQ,by simp⟩
    · obtain ⟨d,hd,hdB⟩ := hF f hf
      refine ⟨d,hd,fun i => ?_⟩
      simpa only [Nat.add_sub_cancel] using (hdB i).trans
        (Nat.mul_le_mul_right D (Nat.pow_le_pow_right ha (Nat.sub_le r 1)))
  · intro f hf x hx
    change x ∈ samplingGrid γ (((G.dimension-(r+1)+1 : ℕ) : ℝ)*R) at hx
    rw [hnext] at hx
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact hQvan x hx
    · apply hFvan f hf x
      apply grid_mono G γ (mul_le_mul_of_nonneg_right _ hR) hx
      exact_mod_cast Nat.le_succ (G.dimension-r)
  · change equationIdeal G (insert Q F) ≤ J'
    rw [heqI]
    exact (sup_le_sup_right hIJ _).trans hJJ'
  · change idealDimension G.ambient J' = G.dimension-(r+1)
    change idealDimension G.ambient J' + 1 = idealDimension G.ambient J at hdim'
    change idealDimension G.ambient J = G.dimension-r at hdim
    omega
  · have hbound : ((a^r*D : ℕ) : ℝ) ≤ X := by
      apply le_trans _ hXbound
      exact_mod_cast Nat.mul_le_mul_right D (Nat.pow_le_pow_right ha hrn)
    have hdegR : (idealDegreeValue G.ambient J' (fun _ => 1) : ℝ) ≤
        ((a^r*D : ℕ) : ℝ) * (idealDegreeValue G.ambient J (fun _ => 1) : ℝ) := by
      exact_mod_cast hdeg'
    calc
      _ ≤ ((a^r*D : ℕ) : ℝ) * X^r :=
        hdegR.trans (mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg _))
      _ ≤ X * X^r := mul_le_mul_of_nonneg_right hbound (pow_nonneg hX _)
      _ = X^(r+1) := (pow_succ' X r).symm
  · intro q hq
    exact ((hmin' q).mp hq).2
  · intro q hq hmeet
    change q ∈ (equationIdeal G (insert Q F)).minimalPrimes at hq
    rw [heqI] at hq
    exact (hmin' q).mpr ⟨retained_minimal_after_cut G Γ _ J hIJ hretain Q q hq hmeet,hmeet⟩

/-- Maximality of a retained cut, with the origin ruling out one further
regular cut in dimension zero, gives the required terminal stage. -/
theorem exists_terminal_stage (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (Γ : Submodule ℤ (singleGroupProduct E).Point) {m : ℕ}
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 0 ≤ R)
    (a D : ℕ) (ha : 1 ≤ a) (hD : 0 < D) (X : ℝ) (hX : 0 ≤ X)
    (hXbound : ((a ^ (singleGroupProduct E).dimension * D : ℕ) : ℝ) ≤ X)
    (hseed : Stage E Γ γ R a D X 1) :
    let G := singleGroupProduct E
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ F : Finset G.CoordinateRing,
        (∀ Q ∈ F, ∃ d : G.FactorIndex → ℕ,
          G.ambient.IsHomogeneous Q d ∧ ∀ i, d i ≤ a ^ (r-1) * D) ∧
        (∀ Q ∈ F, ∀ x ∈ samplingGrid γ (((G.dimension-r+1 : ℕ) : ℝ)*R),
          G.ambient.eval Q (G.embedding x) = 0) ∧
        ∃ J : Ideal G.CoordinateRing, IsMultihomogeneousIdeal G.ambient J ∧
          (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing) ≤ J) ∧
          (∀ q ∈ J.minimalPrimes,
            idealDimension G.ambient q = idealDimension G.ambient J) ∧
          idealDimension G.ambient J = G.dimension-r ∧
          ((idealDegreeValue G.ambient J (fun _ => 1) : ℚ) : ℝ) ≤ X^r ∧
          (∀ q ∈ J.minimalPrimes, ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) ∧
          (∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) → q ∈ J.minimalPrimes) ∧
          ∀ Q : G.CoordinateRing, G.ambient.IsHomogeneous Q (fun _ => a^r*D) →
            (∀ x ∈ samplingGrid γ (((G.dimension-r : ℕ) : ℝ)*R),
              G.ambient.eval Q (G.embedding x) = 0) →
            ∃ p ∈ J.minimalPrimes, Q ∈ p := by
  classical
  let G := singleGroupProduct E
  let r := Nat.findGreatest (Stage E Γ γ R a D X) G.dimension
  have hr : 1 ≤ r := Nat.le_findGreatest hn hseed
  have hrn : r ≤ G.dimension := Nat.findGreatest_le _
  have hs : Stage E Γ γ R a D X r := Nat.findGreatest_spec hn hseed
  obtain ⟨F,hF,hFvan,J,hJ,hIJ,hequi,hdim,hdeg,hmeet,hretain,hreg⟩ := hs
  refine ⟨r,hr,hrn,F,hF,hFvan,J,hJ,hIJ,hequi,hdim,hdeg,hmeet,hretain,?_⟩
  intro Q hQ hQvan
  by_contra havoid
  push Not at havoid
  obtain ⟨hrlt,hsnext⟩ := advance_stage E Γ γ R hR a D ha hD X hX hXbound r hr hrn
    F J hF hFvan hJ hIJ hequi hdim hdeg hretain hreg Q hQ hQvan havoid
  have hle : r+1 ≤ r := Nat.le_findGreatest (Nat.succ_le_of_lt hrlt) hsnext
  omega

end PhilipponMultiplicity.MWCutInduction

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzTerminalAssembly
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace PhilipponMultiplicity
universe u

theorem terminal_retained_cut_of_closure_degree
    (hclosuredegree : ∀
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (b : ℕ) (hb : 1 ≤ b)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0}),
    ((SectionThree.idealDegreeValue (singleGroupProduct E).ambient
      ((singleGroupProduct E).vanishingIdeal Set.univ) (fun _ => 1) : ℚ) : ℝ) ≤
        (b : ℝ) ^ (E.ambientDimension - (singleGroupProduct E).dimension))
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ F : Finset G.CoordinateRing,
        (∀ Q ∈ F, ∃ d : G.FactorIndex → ℕ,
          G.ambient.IsHomogeneous Q d ∧
            ∀ i, d i ≤ a ^ (r - 1) * D) ∧
        (∀ Q ∈ F, ∀ x ∈ samplingGrid γ (((G.dimension - r + 1 : ℕ) : ℝ) * R),
          G.ambient.eval Q (G.embedding x) = 0) ∧
        ∃ J : Ideal G.CoordinateRing, IsMultihomogeneousIdeal G.ambient J ∧
          (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing) ≤ J) ∧
          (∀ q ∈ J.minimalPrimes,
            SectionThree.idealDimension G.ambient q = SectionThree.idealDimension G.ambient J) ∧
          SectionThree.idealDimension G.ambient J = G.dimension - r ∧
          ((SectionThree.idealDegreeValue G.ambient J (fun _ => 1) : ℚ) : ℝ) ≤
            ((D : ℝ) / c) ^ r ∧
          (∀ q ∈ J.minimalPrimes, ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) ∧
          (∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) → q ∈ J.minimalPrimes) ∧
          ∀ Q : G.CoordinateRing, G.ambient.IsHomogeneous Q (fun _ => a ^ r * D) →
            (∀ x ∈ samplingGrid γ (((G.dimension - r : ℕ) : ℝ) * R),
              G.ambient.eval Q (G.embedding x) = 0) →
            ∃ p ∈ J.minimalPrimes, Q ∈ p := by
  dsimp only
  intro hvanish hnonzero Γ hΓ hγ
  let G := singleGroupProduct E
  let X : ℝ := (D : ℝ) * ((a : ℝ)^G.dimension *
    (b : ℝ)^(E.ambientDimension-G.dimension))
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have haPow : (1 : ℝ) ≤ (a : ℝ)^G.dimension := one_le_pow₀ haR
  have hbPow : (1 : ℝ) ≤ (b : ℝ)^(E.ambientDimension-G.dimension) := one_le_pow₀ hbR
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hXbound : ((a^G.dimension*D : ℕ) : ℝ) ≤ X := by
    push_cast
    dsimp only [X]
    have hmul := mul_le_mul_of_nonneg_left hbPow
      (show 0 ≤ (D : ℝ)*(a : ℝ)^G.dimension by positivity)
    nlinarith
  have hdegree := hclosuredegree K hK E hconnected b hb hclosure
  have hbase : (D : ℝ) * (SectionThree.idealDegreeValue G.ambient
      (G.vanishingIdeal Set.univ) (fun _ => 1) : ℝ) ≤ X := by
    calc
      _ ≤ (D : ℝ) * (b : ℝ)^(E.ambientDimension-G.dimension) :=
        mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg _)
      _ ≤ X := by
        dsimp only [X]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        nlinarith [show (0 : ℝ) ≤ (b : ℝ)^(E.ambientDimension-G.dimension) by positivity]
  have hseed := MWCutInduction.initial_stage E hn hconnected Γ γ R
    (le_trans zero_le_one hR) a D hD X hbase P hP hvanish hnonzero
  have hterminal := MWCutInduction.exists_terminal_stage E hn Γ γ R
    (le_trans zero_le_one hR) a D ha hD X hX hXbound hseed
  simpa only [X, div_div_eq_mul_div, div_one] using hterminal

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ F : Finset G.CoordinateRing,
        (∀ Q ∈ F, ∃ d : G.FactorIndex → ℕ,
          G.ambient.IsHomogeneous Q d ∧
            ∀ i, d i ≤ a ^ (r - 1) * D) ∧
        (∀ Q ∈ F, ∀ x ∈ samplingGrid γ (((G.dimension - r + 1 : ℕ) : ℝ) * R),
          G.ambient.eval Q (G.embedding x) = 0) ∧
        ∃ J : Ideal G.CoordinateRing, IsMultihomogeneousIdeal G.ambient J ∧
          (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing) ≤ J) ∧
          (∀ q ∈ J.minimalPrimes,
            SectionThree.idealDimension G.ambient q = SectionThree.idealDimension G.ambient J) ∧
          SectionThree.idealDimension G.ambient J = G.dimension - r ∧
          ((SectionThree.idealDegreeValue G.ambient J (fun _ => 1) : ℚ) : ℝ) ≤
            ((D : ℝ) / c) ^ r ∧
          (∀ q ∈ J.minimalPrimes, ∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) ∧
          (∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (F : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) → q ∈ J.minimalPrimes) ∧
          ∀ Q : G.CoordinateRing, G.ambient.IsHomogeneous Q (fun _ => a ^ r * D) →
            (∀ x ∈ samplingGrid γ (((G.dimension - r : ℕ) : ℝ) * R),
              G.ambient.eval Q (G.embedding x) = 0) →
            ∃ p ∈ J.minimalPrimes, Q ∈ p := by
  exact terminal_retained_cut_of_closure_degree
    (@connected_projective_closure_degree_bound) K hK E hn hconnected a b ha hb
    htranslation hclosure m D hm hD γ R hR P hP
