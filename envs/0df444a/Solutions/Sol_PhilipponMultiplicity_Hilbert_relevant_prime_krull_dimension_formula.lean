-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.relevant_prime_krull_dimension_formula
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T09:27:18.851911+00:00
-- url     : https://prove2.me/submissions/b0b01e7e-1c2a-487e-9872-081a8a528da1

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Definitions.Def_PhilipponMultiplicity_HilbertGrowth
import Theorems.Thm_PhilipponMultiplicity_Hilbert_cumulativeHilbertFunction_polynomial_bounds

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open Filter MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
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

namespace PolynomialGrowth.IntegralDimension

private lemma exists_ltSeries_comap_eq_last {R S : Type*} [CommRing R] [CommRing S]
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
    obtain ⟨L, hlen, -⟩ := exists_ltSeries_comap_eq_last hinj l
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

namespace PhilipponMultiplicity.Hilbert
instance degreeFiltration_finite {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (I : Ideal M.CoordinateRing) (n : ℕ) :
    Module.Finite K (degreeFiltration M I n) := by
  unfold degreeFiltration
  infer_instance

end PhilipponMultiplicity.Hilbert

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

theorem solution    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (q : Ideal M.CoordinateRing) (hq : q.IsPrime)
    (hhom : IsMultihomogeneousIdeal M q)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q) :
    ringKrullDim (M.CoordinateRing ⧸ q) =
      ((idealDimension M q + M.factorCount : ℕ) : WithBot ℕ∞) := by
  exact PhilipponMultiplicity.Hilbert.relevant_prime_krull_dimension_formula M q hq hhom hrel
