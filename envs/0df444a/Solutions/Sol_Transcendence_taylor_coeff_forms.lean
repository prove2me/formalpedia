-- Prove2me | solution 1 for Transcendence.taylor_coeff_forms
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T10:12:15.507913+00:00
-- url     : https://prove2.me/submissions/327284d9-9457-4272-b3e2-a52350b29e13

import Mathlib
import Theorems.Thm_Transcendence_polydisc_cauchy

/-!
# Cauchy-bounded Taylor coefficients as linear forms (Waldschmidt, DALAG §4.5)

`D^k G(0)(z, …, z)` expands along the coordinate directions as a sum over direction lists
`L : Fin k → ι` (`iteratedFDeriv_expand`); grouping the lists by their multiplicities `cnt L`
gives the coefficient `coef G T r τ` of `(z / r)^τ` for `τ` in the box `ι → Fin T` (`sum_tc_eq`;
no symmetry of derivatives is needed, and the coefficients of order `≥ T` vanish). Each mixed
derivative is at most `τ! M / r^K` by Cauchy's inequalities on the polydisc
(`Transcendence.polydisc_cauchy`), and the multinomial count `#{L | cnt L = τ} · τ! = K!`
(`card_mul_prod_factorial`, from the multinomial theorem in `MvPolynomial ι ℕ`) gives
`|coef G T r τ| ≤ M` (`norm_coef_le`). The coefficients are linear in `G` (`coef_sum`).
-/

namespace TaylorCoeffForms

open Finset Metric
open scoped Nat

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι]

lemma iteratedFDeriv_sum_const_mul {Λ : Type*} [Fintype Λ] (f : Λ → (ι → ℂ) → ℂ)
    (hf : ∀ l, AnalyticOnNhd ℂ (f l) Set.univ) (c : Λ → ℂ) (k : ℕ) :
    iteratedFDeriv ℂ k (fun z => ∑ l, c l * f l z) 0 =
      ∑ l, c l • iteratedFDeriv ℂ k (f l) 0 := by
  rw [iteratedFDeriv_fun_sum_apply fun l _ => contDiffAt_const.mul (hf l).contDiff.contDiffAt]
  refine sum_congr rfl fun l _ => ?_
  simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c l)
    (x := (0 : ι → ℂ)) (i := k) (hf l).contDiff.contDiffAt

variable [DecidableEq ι]

/-- The mixed derivative of `G` at `0` along the coordinate directions `L 0, …, L (k-1)`. -/
noncomputable def D (G : (ι → ℂ) → ℂ) {k : ℕ} (L : Fin k → ι) : ℂ :=
  iteratedFDeriv ℂ k G 0 (fun i => Pi.single (L i) 1)

/-- How many times the direction `ν` occurs in `L`. -/
def cnt {k : ℕ} (L : Fin k → ι) (ν : ι) : ℕ := (univ.filter fun i => L i = ν).card

lemma cnt_le {k : ℕ} (L : Fin k → ι) (ν : ι) : cnt L ν ≤ k := by
  unfold cnt
  calc _ ≤ (univ : Finset (Fin k)).card := card_filter_le _ _
    _ = k := by simp

lemma sum_cnt {k : ℕ} (L : Fin k → ι) : ∑ ν, cnt L ν = k := by
  unfold cnt
  rw [← card_eq_sum_card_fiberwise (f := L) (s := univ) (t := univ) (fun _ _ => mem_univ _)]
  simp

lemma prod_eq_prod_pow_cnt {M : Type*} [CommMonoid M] {k : ℕ} (L : Fin k → ι) (y : ι → M) :
    ∏ i, y (L i) = ∏ ν, y ν ^ cnt L ν := by
  rw [← prod_fiberwise' univ L y]
  apply prod_congr rfl
  intro ν _
  rw [prod_const]
  rfl

/-- Expansion of `D^k G(0)(z, …, z)` along the coordinate directions. -/
lemma iteratedFDeriv_expand (G : (ι → ℂ) → ℂ) (k : ℕ) (z : ι → ℂ) :
    iteratedFDeriv ℂ k G 0 (fun _ => z) = ∑ L : Fin k → ι, (∏ i, z (L i)) * D G L := by
  have hz : z = ∑ ν, z ν • (Pi.single ν (1 : ℂ) : ι → ℂ) := by
    ext μ; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  rw [ContinuousMultilinearMap.map_sum]
  apply sum_congr rfl
  intro L _
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/-- The normalised Taylor coefficient of `G` at `0` of multi-index `τ` (in the box `ι → Fin T`),
times `ρ^{|τ|}`; the multi-index is encoded by direction lists `L` with `cnt L = τ`. -/
noncomputable def coef (G : (ι → ℂ) → ℂ) (T : ℕ) (ρ : ℂ) (τ : ι → Fin T) : ℂ :=
  ∑ k ∈ range T, (k ! : ℂ)⁻¹ * ρ ^ k *
    ∑ L ∈ (univ.filter fun L : Fin k → ι => ∀ ν, cnt L ν = τ ν), D G L

/-- The Taylor polynomial of order `< T` of `G` at `ρ • y` in terms of the coefficients. -/
lemma sum_tc_eq (G : (ι → ℂ) → ℂ) (T : ℕ) (ρ : ℂ) (y : ι → ℂ) :
    ∑ k ∈ range T, (k ! : ℂ)⁻¹ * iteratedFDeriv ℂ k G 0 (fun _ => ρ • y) =
      ∑ τ : ι → Fin T, (∏ ν, y ν ^ (τ ν : ℕ)) * coef G T ρ τ := by
  simp only [coef, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  rw [iteratedFDeriv_expand, mul_sum]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  set τL : ι → Fin T := fun ν => ⟨cnt L ν, lt_of_le_of_lt (cnt_le L ν) hk⟩ with hτL
  rw [Fintype.sum_eq_single τL]
  · have hc : ∀ ν, cnt L ν = (τL ν : ℕ) := fun ν => rfl
    simp only [hc, implies_true, ite_true]
    have hp : ∏ i, (ρ • y) (L i) = ρ ^ k * ∏ ν, y ν ^ (τL ν : ℕ) := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_eq_prod_pow_cnt L y]
    rw [hp]
    ring
  · intro τ hτ
    have hne : ¬ ∀ ν, cnt L ν = (τ ν : ℕ) := by
      intro h
      apply hτ
      funext ν
      exact Fin.ext (h ν).symm
    simp [hne]

/-- The multinomial count `#{L | cnt L = τ} · ∏ τ_ν! = K!` for `∑ τ = K`, from the multinomial
theorem in `MvPolynomial ι ℕ`. -/
lemma card_mul_prod_factorial (τ : ι → ℕ) {K : ℕ} (hK : ∑ ν, τ ν = K) :
    (univ.filter fun L : Fin K → ι => ∀ ν, cnt L ν = τ ν).card * ∏ ν, (τ ν)! = K ! := by
  have h := MvPolynomial.coeff_sum_X_pow_of_fintype (R := ℕ) (Finsupp.equivFunOnFinite.symm τ) K
  rw [Fintype.sum_pow, MvPolynomial.coeff_sum] at h
  simp_rw [prod_eq_prod_pow_cnt _ MvPolynomial.X, MvPolynomial.coeff_prod_X_pow] at h
  have hc : ∀ L : Fin K → ι, (Finsupp.equivFunOnFinite.symm τ =
      Finsupp.indicator univ fun i _ => cnt L i) ↔ ∀ ν, cnt L ν = τ ν := fun L => by
    simp [Finsupp.ext_iff, Finsupp.indicator_apply, eq_comm]
  have hs : ((Finsupp.equivFunOnFinite.symm τ).sum fun _ m => m) = K := by
    rw [Finsupp.sum_fintype _ (fun _ m => m) (fun _ => rfl)]; simpa using hK
  simp only [hc, sum_boole, hs, ↓reduceIte, Nat.cast_id] at h
  rw [h, Finsupp.multinomial_eq_of_support_subset (subset_univ _), mul_comm,
    Finsupp.coe_equivFunOnFinite_symm, Nat.multinomial_spec, hK]

/-- **Cauchy's inequality for the coefficients**: each mixed derivative is bounded by
`Transcendence.polydisc_cauchy`, and the multinomial count sums the bounds to `M`. -/
lemma norm_coef_le {G : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ x ∈ closedBall (0 : ι → ℂ) r, ‖G x‖ ≤ M) (T : ℕ) (τ : ι → Fin T) :
    ‖coef G T (r : ℂ) τ‖ ≤ M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (mem_closedBall_self hr.le))
  set K := ∑ ν, (τ ν : ℕ) with hK
  have hzero : ∀ k ∈ range T, k ≠ K → (k ! : ℂ)⁻¹ * (r : ℂ) ^ k *
      ∑ L ∈ (univ.filter fun L : Fin k → ι => ∀ ν, cnt L ν = τ ν), D G L = 0 := fun k _ hk => by
    rw [filter_false_of_mem fun L _ hL => hk (by
      rw [← sum_cnt L]; exact sum_congr rfl fun ν _ => hL ν), sum_empty, mul_zero]
  rw [coef]
  by_cases hKT : K < T
  swap
  · rw [sum_eq_zero fun k hk => hzero k hk (by rintro rfl; exact hKT (mem_range.mp hk))]
    simpa using hM0
  rw [sum_eq_single K hzero (fun h => absurd (mem_range.mpr hKT) h)]
  set S := univ.filter fun L : Fin K → ι => ∀ ν, cnt L ν = τ ν
  have hD : ∀ L ∈ S, ‖D G L‖ ≤ (∏ ν, ((τ ν : ℕ)! : ℝ)) * M / r ^ K := fun L hL => by
    have hc : ∀ ν, (univ.filter fun l => L l = ν).card = (τ ν : ℕ) := (mem_filter.mp hL).2
    simpa only [hc, D] using Transcendence.polydisc_cauchy hG 0 hr hM K L
  have hcount : (S.card : ℝ) * ∏ ν, ((τ ν : ℕ)! : ℝ) = K ! := by
    exact_mod_cast card_mul_prod_factorial (fun ν => (τ ν : ℕ)) hK.symm
  have hKf : (0 : ℝ) < K ! := by exact_mod_cast K.factorial_pos
  rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  calc (K ! : ℝ)⁻¹ * r ^ K * ‖∑ L ∈ S, D G L‖
      ≤ (K ! : ℝ)⁻¹ * r ^ K * ∑ L ∈ S, (∏ ν, ((τ ν : ℕ)! : ℝ)) * M / r ^ K := by
        gcongr; exact (norm_sum_le _ _).trans (sum_le_sum hD)
    _ = M := by
        rw [sum_const, nsmul_eq_mul]
        field_simp
        linear_combination M * hcount

lemma D_sum {Λ : Type*} [Fintype Λ] (f : Λ → (ι → ℂ) → ℂ)
    (hf : ∀ l, AnalyticOnNhd ℂ (f l) Set.univ) (c : Λ → ℂ) {k : ℕ} (L : Fin k → ι) :
    D (fun z => ∑ l, c l * f l z) L = ∑ l, c l * D (f l) L := by
  unfold D
  rw [iteratedFDeriv_sum_const_mul f hf c k]
  simp

lemma coef_sum {Λ : Type*} [Fintype Λ] (f : Λ → (ι → ℂ) → ℂ)
    (hf : ∀ l, AnalyticOnNhd ℂ (f l) Set.univ) (c : Λ → ℂ) (T : ℕ) (ρ : ℂ) (τ : ι → Fin T) :
    coef (fun z => ∑ l, c l * f l z) T ρ τ = ∑ l, c l * coef (f l) T ρ τ := by
  simp only [coef, D_sum f hf c, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  apply sum_congr rfl
  intro l _
  ring

end TaylorCoeffForms

theorem solution {ι Λ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Λ]
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ) {r : ℝ} (hr : 0 < r)
    (B : Λ → ℝ) (hB : ∀ l, ∀ z ∈ Metric.closedBall (0 : ι → ℂ) r, ‖φ l z‖ ≤ B l) (T : ℕ) :
    ∃ u : (ι → Fin T) → Λ → ℂ, (∀ τ l, ‖u τ l‖ ≤ B l) ∧
      ∀ (c : Λ → ℂ) (z : ι → ℂ),
        ∑ k ∈ Finset.range T, (k.factorial : ℂ)⁻¹ *
            iteratedFDeriv ℂ k (fun x => ∑ l, c l * φ l x) 0 (fun _ => z) =
          ∑ τ, (∏ ν, (z ν / r) ^ (τ ν : ℕ)) * ∑ l, u τ l * c l := by
  refine ⟨fun τ l => TaylorCoeffForms.coef (φ l) T (r : ℂ) τ,
    fun τ l => TaylorCoeffForms.norm_coef_le (hφ l) hr (hB l) T τ, fun c z => ?_⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz : z = (r : ℂ) • ((r : ℂ)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hrC, one_smul]
  conv_lhs => rw [hz]
  rw [TaylorCoeffForms.sum_tc_eq]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [TaylorCoeffForms.coef_sum φ hφ c]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_inv_mul, mul_comm (c _)]
