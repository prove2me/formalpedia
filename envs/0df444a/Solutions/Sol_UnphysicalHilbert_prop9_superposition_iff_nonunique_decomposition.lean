-- Prove2me | solution 1 for UnphysicalHilbert.prop9_superposition_iff_nonunique_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:58:29.317176+00:00
-- url     : https://prove2.me/submissions/f70ff2ae-b5d2-4228-afe5-52e75561c8a0

import Mathlib
import Definitions.Def_UnphysicalHilbert_StateSpace

open UnphysicalHilbert
open scoped InnerProductSpace

namespace UHMix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma mixture_apply {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x : H) :
    mixture a ψ x = ∑ i, ((a i : ℂ) * ⟪ψ i, x⟫_ℂ) • ψ i := by
  simp only [mixture, ketBra, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    innerₛₗ_apply_apply, smul_smul]

lemma mixture_mem_span {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x : H) :
    mixture a ψ x ∈ Submodule.span ℂ (Set.range ψ) := by
  rw [mixture_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma inner_mixture_self {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x : H) :
    ⟪x, mixture a ψ x⟫_ℂ = ((∑ i, a i * ‖⟪ψ i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [mixture_apply, inner_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (ψ i) x, mul_assoc, RCLike.conj_mul]
  simp [norm_inner_symm]

lemma eq_zero_of_mixture_eq_zero {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (ψ : ι → H) (w : H) (hw : w ∈ Submodule.span ℂ (Set.range ψ)) (h0 : mixture a ψ w = 0) :
    w = 0 := by
  have h1 := inner_mixture_self a ψ w
  rw [h0, inner_zero_right] at h1
  have h2 : ∑ i, a i * ‖⟪ψ i, w⟫_ℂ‖ ^ 2 = 0 := by exact_mod_cast h1.symm
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by have := ha i; positivity)] at h2
  have h3 : ∀ i, ⟪w, ψ i⟫_ℂ = 0 := by
    intro i
    have := h2 i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ha i).ne'
    · rw [← inner_conj_symm]
      have : ⟪ψ i, w⟫_ℂ = 0 := by simpa using h
      simp [this]
  have h4 : Submodule.span ℂ (Set.range ψ) ≤ LinearMap.ker (innerₛₗ ℂ w) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [h3 i]
  have h5 := h4 hw
  simp only [LinearMap.mem_ker, innerₛₗ_apply_apply] at h5
  exact inner_self_eq_zero.mp h5

lemma range_mixture {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ψ : ι → H) :
    LinearMap.range (mixture a ψ) = Submodule.span ℂ (Set.range ψ) := by
  set W := Submodule.span ℂ (Set.range ψ)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩; exact mixture_mem_span a ψ x
  · intro w hw
    have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ψ)
    let ρW : W →ₗ[ℂ] W := (mixture a ψ).restrict (fun x _ => mixture_mem_span a ψ x)
    have hinj : Function.Injective ρW := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      apply Subtype.ext
      apply eq_zero_of_mixture_eq_zero a ha ψ x x.2
      have := congrArg Subtype.val hx
      simpa [ρW] using this
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨w, hw⟩
    exact ⟨y, by have := congrArg Subtype.val hy; simpa [ρW] using this⟩

end UHMix

open UnphysicalHilbert
open scoped InnerProductSpace

namespace UHMix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma ketBra_apply (ψ x : H) : ketBra ψ x = ⟪ψ, x⟫_ℂ • ψ := by
  simp [ketBra, innerₛₗ_apply_apply]

/-- trace of a mixture over an orthonormal basis of a subspace containing the vectors -/
lemma trace_mixture {ι : Type*} [Fintype ι] (W : Submodule ℂ H) {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ W) (p : ι → ℝ) (φ : ι → H) (hφ : ∀ k, φ k ∈ W) :
    ∑ j, RCLike.re ⟪(b j : H), mixture p φ (b j)⟫_ℂ = ∑ k, p k * ‖φ k‖ ^ 2 := by
  have h1 : ∀ j, RCLike.re ⟪(b j : H), mixture p φ (b j)⟫_ℂ =
      ∑ k, p k * ‖⟪(b j : W), (⟨φ k, hφ k⟩ : W)⟫_ℂ‖ ^ 2 := by
    intro j
    rw [inner_mixture_self]
    rw [show ∀ r : ℝ, RCLike.re ((r : ℂ)) = r from fun r => Complex.ofReal_re r]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_inner, norm_inner_symm]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, b.sum_sq_norm_inner_right]
  simp

lemma spectral_decomp (R : H →ₗ[ℂ] H) (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hRW : ∀ x, R x ∈ W) (hperp : ∀ z ∈ Wᗮ, R z = 0)
    (hsym : ∀ x y, ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ) (hpos : ∀ x, 0 ≤ RCLike.re ⟪x, R x⟫_ℂ) :
    ∃ (m : ℕ) (lam : Fin m → ℝ) (e : Fin m → H), (∀ k, 0 < lam k) ∧ (∀ k, ‖e k‖ = 1) ∧
      (∀ k, e k ∈ W) ∧ R = mixture lam e := by
  set T : W →ₗ[ℂ] W := R.restrict (fun x _ => hRW x) with hTdef
  have hTapp : ∀ w : W, ((T w : W) : H) = R w := fun w => rfl
  have hT : T.IsSymmetric := by
    intro x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hTapp, hTapp, hsym]
  set d := Module.finrank ℂ W
  set b := hT.eigenvectorBasis (rfl : Module.finrank ℂ W = d)
  set ev := hT.eigenvalues (rfl : Module.finrank ℂ W = d)
  have hb : ∀ j, R (b j) = (ev j : ℂ) • ((b j : W) : H) := by
    intro j
    rw [← hTapp, hT.apply_eigenvectorBasis]; rfl
  have hbn : ∀ j, ‖((b j : W) : H)‖ = 1 := fun j => by
    exact b.orthonormal.1 j
  have hev : ∀ j, 0 ≤ ev j := by
    intro j
    have := hpos (b j)
    rw [hb, inner_smul_right, inner_self_eq_norm_sq_to_K, hbn] at this
    simpa using this
  -- R as a sum over the eigenbasis
  have hR : R = ∑ j, ((ev j : ℝ) : ℂ) • ketBra ((b j : W) : H) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy, z, hz, rfl⟩ := W.exists_add_mem_mem_orthogonal x
    rw [map_add, hperp z hz, add_zero, LinearMap.sum_apply]
    have hz' : ∀ j, ⟪((b j : W) : H), z⟫_ℂ = 0 := fun j =>
      Submodule.inner_right_of_mem_orthogonal (b j).2 hz
    simp only [LinearMap.smul_apply, ketBra_apply, inner_add_right, hz', add_zero]
    have hy' := b.sum_repr' (⟨y, hy⟩ : W)
    have : R y = R ((⟨y, hy⟩ : W) : H) := rfl
    rw [this, ← hy']
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hb, Submodule.coe_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, mul_comm]
  -- drop zero eigenvalues
  set S := Finset.univ.filter (fun j => 0 < ev j)
  have hRS : R = ∑ j ∈ S, ((ev j : ℝ) : ℂ) • ketBra ((b j : W) : H) := by
    rw [hR, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rfl
    · have : ev j = 0 := le_antisymm (not_lt.mp h) (hev j)
      simp [this]
  refine ⟨S.card, fun k => ev (S.equivFin.symm k).1, fun k => ((b (S.equivFin.symm k).1 : W) : H),
    fun k => (Finset.mem_filter.mp (S.equivFin.symm k).2).2, fun k => hbn _, fun k => (b _).2, ?_⟩
  rw [hRS, mixture, ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp S.equivFin.symm (fun x : S => ((ev x.1 : ℝ) : ℂ) • ketBra ((b x.1 : W) : H))).symm

end UHMix

open UnphysicalHilbert
open scoped InnerProductSpace

namespace UHMix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma ketBra_symm (φ x y : H) : ⟪ketBra φ x, y⟫_ℂ = ⟪x, ketBra φ y⟫_ℂ := by
  rw [ketBra_apply, ketBra_apply, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

lemma mixture_symm {ι : Type*} [Fintype ι] (a : ι → ℝ) (ψ : ι → H) (x y : H) :
    ⟪mixture a ψ x, y⟫_ℂ = ⟪x, mixture a ψ y⟫_ℂ := by
  simp only [mixture, LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, ketBra_symm]

lemma inner_ketBra_self (ψ x : H) : ⟪x, ketBra ψ x⟫_ℂ = ((‖⟪ψ, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [ketBra_apply, inner_smul_right, ← inner_conj_symm ψ x, RCLike.conj_mul]
  push_cast; rw [RCLike.norm_conj, norm_inner_symm]; norm_cast

lemma cs_bound {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (ψs : Fin n → H) (u x : H) :
    ‖⟪mixture a ψs u, x⟫_ℂ‖ ^ 2 ≤
      (∑ i, a i * ‖⟪ψs i, u⟫_ℂ‖ ^ 2) * (∑ i, a i * ‖⟪ψs i, x⟫_ℂ‖ ^ 2) := by
  have h1 : ⟪mixture a ψs u, x⟫_ℂ = ∑ i, (a i : ℂ) * ((starRingEnd ℂ) ⟪ψs i, u⟫_ℂ * ⟪ψs i, x⟫_ℂ) := by
    rw [mixture_apply, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, map_mul, Complex.conj_ofReal, mul_assoc]
  have h2 : ‖⟪mixture a ψs u, x⟫_ℂ‖ ≤ ∑ i, a i * (‖⟪ψs i, u⟫_ℂ‖ * ‖⟪ψs i, x⟫_ℂ‖) := by
    rw [h1]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha i), RCLike.norm_conj]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => √(a i) * ‖⟪ψs i, u⟫_ℂ‖) (fun i => √(a i) * ‖⟪ψs i, x⟫_ℂ‖)
  have hs : ∀ i, √(a i) ^ 2 = a i := fun i => Real.sq_sqrt (ha i).le
  simp only [mul_pow, hs] at h3
  have h4 : ∑ i, √(a i) * ‖⟪ψs i, u⟫_ℂ‖ * (√(a i) * ‖⟪ψs i, x⟫_ℂ‖) =
      ∑ i, a i * (‖⟪ψs i, u⟫_ℂ‖ * ‖⟪ψs i, x⟫_ℂ‖) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hs i
    calc √(a i) * ‖⟪ψs i, u⟫_ℂ‖ * (√(a i) * ‖⟪ψs i, x⟫_ℂ‖)
        = √(a i) ^ 2 * (‖⟪ψs i, u⟫_ℂ‖ * ‖⟪ψs i, x⟫_ℂ‖) := by ring
      _ = _ := by rw [this]
  rw [h4] at h3
  calc ‖⟪mixture a ψs u, x⟫_ℂ‖ ^ 2 ≤ (∑ i, a i * (‖⟪ψs i, u⟫_ℂ‖ * ‖⟪ψs i, x⟫_ℂ‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ _ := h3

end UHMix

open UnphysicalHilbert
open scoped InnerProductSpace

namespace UHMix

lemma mixture_cons {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {m : ℕ}
    (t : ℝ) (lam : Fin m → ℝ) (ψ : H) (e : Fin m → H) :
    mixture (Fin.cons t lam : Fin (m + 1) → ℝ) (Fin.cons ψ e) = (t : ℂ) • ketBra ψ + mixture lam e := by
  simp only [mixture, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem prop8
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) (hψ : ‖ψ‖ = 1) (ρ : H →ₗ[ℂ] H) (hρ : IsFiniteRankDensityOperator ρ)
    (hψρ : ψ ∈ LinearMap.range ρ) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ) (φ : Fin (n + 1) → H),
      φ 0 = ψ ∧ IsNormalizedFamily φ ∧ IsStrictConvexWeights p ∧ ρ = mixture p φ := by
  obtain ⟨n, a, ψs, ha, hψs, rfl⟩ := hρ
  set W := Submodule.span ℂ (Set.range ψs) with hW
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range ψs)
  have hψW : ψ ∈ W := by rw [hW, ← range_mixture a ha.1 ψs]; exact hψρ
  have hψsW : ∀ i, ψs i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨u, hu⟩ := hψρ
  set q : H → ℝ := fun x => ∑ i, a i * ‖⟪ψs i, x⟫_ℂ‖ ^ 2 with hq
  have hq0 : ∀ x, 0 ≤ q x := fun x => Finset.sum_nonneg fun i _ => by have := ha.1 i; positivity
  set t : ℝ := 1 / (1 + q u) with ht
  have ht0 : 0 < t := by have := hq0 u; positivity
  have htq : t * q u ≤ 1 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_le_one (by linarith [hq0 u])]; linarith
  set R : H →ₗ[ℂ] H := mixture a ψs - (t : ℂ) • ketBra ψ with hR
  have hRapp : ∀ x, R x = mixture a ψs x - (t : ℂ) • ketBra ψ x := fun x => rfl
  -- hypotheses of the spectral decomposition
  have hRW : ∀ x, R x ∈ W := by
    intro x
    rw [hRapp, ketBra_apply]
    exact W.sub_mem (mixture_mem_span a ψs x) (W.smul_mem _ (W.smul_mem _ hψW))
  have hperp : ∀ z ∈ Wᗮ, R z = 0 := by
    intro z hz
    rw [hRapp, mixture_apply, ketBra_apply, Submodule.inner_right_of_mem_orthogonal hψW hz]
    simp [Submodule.inner_right_of_mem_orthogonal (hψsW _) hz]
  have hsym : ∀ x y, ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ := by
    intro x y
    rw [hRapp, hRapp, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      mixture_symm, ketBra_symm, Complex.conj_ofReal]
  have hpos : ∀ x, 0 ≤ RCLike.re ⟪x, R x⟫_ℂ := by
    intro x
    rw [hRapp, inner_sub_right, inner_smul_right, inner_mixture_self, inner_ketBra_self]
    have e1 : RCLike.re (((q x : ℝ) : ℂ) - (t : ℂ) * ((‖⟪ψ, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) =
        q x - t * ‖⟪ψ, x⟫_ℂ‖ ^ 2 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub]; exact Complex.ofReal_re _
    rw [e1]
    have hcs := cs_bound a ha.1 ψs u x
    rw [hu] at hcs
    have : t * ‖⟪ψ, x⟫_ℂ‖ ^ 2 ≤ t * (q u * q x) := mul_le_mul_of_nonneg_left hcs ht0.le
    nlinarith [hq0 x, hq0 u]
  obtain ⟨m, lam, e, hlam, hen, heW, hRe⟩ := spectral_decomp R W hRW hperp hsym hpos
  refine ⟨m, Fin.cons t lam, Fin.cons ψ e, rfl, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro k; refine Fin.cases ?_ (fun k => ?_) k
    · simpa using hψ
    · simpa using hen k
  · intro k; refine Fin.cases ?_ (fun k => ?_) k
    · simpa using ht0
    · simpa using hlam k
  · have hmix : mixture a ψs = mixture (Fin.cons t lam : Fin (m + 1) → ℝ) (Fin.cons ψ e) := by
      rw [mixture_cons, ← hRe, hR]; abel
    have h1 := trace_mixture W (stdOrthonormalBasis ℂ W) a ψs hψsW
    have h2 := trace_mixture W (stdOrthonormalBasis ℂ W) (Fin.cons t lam : Fin (m + 1) → ℝ)
      (Fin.cons ψ e) (fun k => Fin.cases hψW (fun k => by simpa using heW k) k)
    rw [← hmix, h1] at h2
    have hn1 : ∀ k, ‖(Fin.cons ψ e : Fin (m + 1) → H) k‖ = 1 := fun k =>
      Fin.cases (by simpa using hψ) (fun k => by simpa using hen k) k
    simp only [hψs _, hn1, one_pow, mul_one] at h2
    rw [← h2, ha.2]
  · rw [mixture_cons, ← hRe, hR]; abel

end UHMix

open UnphysicalHilbert
open scoped InnerProductSpace

open UHMix in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι]
    (ψ : H) (hψ : ‖ψ‖ = 1) (ϕ : ι → H) (hϕ : IsNormalizedFamily ϕ) (hψϕ : ∀ j, ϕ j ≠ ψ) :
    ψ ∈ Submodule.span ℂ (Set.range ϕ) ↔
      ∃ (n : ℕ) (φ : Fin (n + 1) → H) (a : Fin (n + 1) → ℝ) (b : ι → ℝ),
        φ 0 = ψ ∧ IsNormalizedFamily φ ∧ IsStrictConvexWeights a ∧
        IsStrictConvexWeights b ∧ mixture a φ = mixture b ϕ := by
  constructor
  · intro hmem
    have hne : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      have : Set.range ϕ = ∅ := Set.range_eq_empty ϕ
      rw [this, Submodule.span_empty, Submodule.mem_bot] at hmem
      rw [hmem, norm_zero] at hψ; exact zero_ne_one hψ
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    set b : ι → ℝ := fun _ => 1 / (Fintype.card ι : ℝ)
    have hb : IsStrictConvexWeights b := by
      refine ⟨fun _ => by positivity, ?_⟩
      simp only [b, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    set eqv := Fintype.equivFin ι
    have hρ : IsFiniteRankDensityOperator (mixture b ϕ) := by
      refine ⟨Fintype.card ι, b ∘ eqv.symm, ϕ ∘ eqv.symm, ⟨fun k => hb.1 (eqv.symm k), ?_⟩,
        fun k => hϕ (eqv.symm k), ?_⟩
      · rw [← hb.2]; exact Equiv.sum_comp eqv.symm b
      · simp only [mixture]
        exact (Equiv.sum_comp eqv.symm (fun i => ((b i : ℝ) : ℂ) • ketBra (ϕ i))).symm
    have hψρ : ψ ∈ LinearMap.range (mixture b ϕ) := by rw [range_mixture b hb.1]; exact hmem
    obtain ⟨n, p, φ, h0, hφ, hp, hρeq⟩ := prop8 ψ hψ (mixture b ϕ) hρ hψρ
    exact ⟨n, φ, p, b, h0, hφ, hp, hb, hρeq.symm⟩
  · rintro ⟨n, φ, a, b, h0, hφ, ha, hb, hab⟩
    have := congrArg LinearMap.range hab
    rw [range_mixture a ha.1, range_mixture b hb.1] at this
    rw [← this, ← h0]
    exact Submodule.subset_span ⟨0, rfl⟩