-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.pureEnsembleLinearity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:23:16.701763+00:00
-- url     : https://prove2.me/submissions/4a709063-434f-4819-a524-65ceb159b01a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

lemma g52e_cqf_sum {I ι : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (s : Finset ι)
    (A : ι → Matrix I I ℂ) :
    complexQuadraticForm v (∑ l ∈ s, A l) = ∑ l ∈ s, complexQuadraticForm v (A l) := by
  simp only [complexQuadraticForm, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

lemma g52e_unit {h : ℕ} (ψ : EuclideanSpace ℂ (Fin h)) (hψ : IsState ψ) :
    ∑ b, conj (ψ b) * ψ b = 1 := by
  have h1 : (inner ℂ ψ ψ) = ((‖ψ‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
  rw [hψ] at h1
  simp only [PiLp.inner_apply, RCLike.inner_apply] at h1
  calc ∑ b, conj (ψ b) * ψ b = ∑ x, ψ x * conj (ψ x) :=
        Finset.sum_congr rfl fun b _ => mul_comm _ _
    _ = 1 := by rw [h1]; norm_num

lemma g52e_proj_sqrt {h : ℕ} (P : Matrix (Fin h) (Fin h) ℂ) (hP : P.IsHermitian)
    (hPP : P * P = P) (r : ℝ) (hr : 0 ≤ r) :
    cfc Real.sqrt (r • P) = Real.sqrt r • P := by
  have hsa : IsSelfAdjoint P := hP
  have hspec : ∀ x ∈ spectrum ℝ P, x = 0 ∨ x = 1 := by
    have h1 : cfc (fun x : ℝ => x ^ 2) P = cfc (fun x : ℝ => x) P := by
      rw [cfc_pow_id (R := ℝ) P 2 hsa, cfc_id' (R := ℝ) (a := P) (ha := hsa), sq, hPP]
    have := eqOn_of_cfc_eq_cfc h1 (ha := hsa)
    intro x hx
    have hx2 : x ^ 2 = x := this hx
    have : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h0 | h0
    · left; exact h0
    · right; linarith
  rw [← cfc_comp_const_mul r Real.sqrt P (ha := hsa)]
  rw [cfc_congr (g := fun x => Real.sqrt r * x), cfc_const_mul_id (R := ℝ) _ P (ha := hsa)]
  intro x hx
  rcases hspec x hx with rfl | rfl <;> simp

lemma g52e_F2 {h : ℕ} (ψ : EuclideanSpace ℂ (Fin h)) (hψ : ∑ b, conj (ψ b) * ψ b = 1)
    (σ : Matrix (Fin h) (Fin h) ℂ) (hσ : σ.PosSemidef) :
    rootFidelity (pureDensity ψ) σ ^ 2 = (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re := by
  set P := pureDensity ψ with hPdef
  have hP : P.IsHermitian := by
    ext x y; simp [P, pureDensity, Matrix.conjTranspose_apply, mul_comm]
  have hPP : P * P = P := by
    ext x y
    simp only [P, pureDensity, Matrix.mul_apply, Matrix.of_apply]
    calc ∑ b, ψ x * conj (ψ b) * (ψ b * conj (ψ y))
        = ψ x * conj (ψ y) * ∑ b, conj (ψ b) * ψ b := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
      _ = ψ x * conj (ψ y) := by rw [hψ, mul_one]
  set c := ∑ a, ∑ b, conj (ψ a) * σ a b * ψ b with hc
  have hc0 : 0 ≤ c := by
    have := hσ.dotProduct_mulVec_nonneg (⇑ψ)
    convert this using 1
    simp only [c, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [Complex.nonneg_iff] at hc0
  have hcr : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hc0.2])
  have hPsP : P * σ * P = (c.re : ℝ) • P := by
    ext x y
    rw [← Complex.coe_smul, ← hcr]
    simp only [P, pureDensity, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      c, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hsq : cfc Real.sqrt P = P := by
    have := g52e_proj_sqrt P hP hPP 1 zero_le_one
    simpa using this
  have htrP : P.trace = 1 := by
    simp only [P, pureDensity, Matrix.trace, Matrix.diag, Matrix.of_apply]
    rw [← hψ]; refine Finset.sum_congr rfl fun b _ => ?_; ring
  unfold rootFidelity
  rw [hsq, hPsP, g52e_proj_sqrt P hP hPP _ hc0.1, Matrix.trace_smul, htrP]
  simp [Real.sq_sqrt hc0.1]

lemma g52e_chan_psd {h : ℕ} (X : Superop (Fin h) (Fin h)) (hX : IsChannel X)
    (P : Matrix (Fin h) (Fin h) ℂ) (hP : P.PosSemidef) : (X P).PosSemidef := by
  obtain ⟨m, E, -, hE⟩ := hX
  rw [hE]
  exact Matrix.posSemidef_sum _ fun l _ => hP.mul_mul_conjTranspose_same _

lemma g52e_r_le {h : ℕ} (X : Superop (Fin h) (Fin h)) (hX : IsChannel X)
    (ψ : EuclideanSpace ℂ (Fin h)) (hψs : IsState ψ) :
    (∑ a, ∑ b, conj (ψ a) * X (pureDensity ψ) a b * ψ b).re ≤ 1 := by
  obtain ⟨m, E, hK, hE⟩ := hX
  have hψ := g52e_unit ψ hψs
  rw [hE]
  let v : Fin m → EuclideanSpace ℂ (Fin h) := fun l => WithLp.toLp 2 ((E l).mulVec ⇑ψ)
  have hP' : pureDensity ψ = Matrix.vecMulVec (⇑ψ) (star ⇑ψ) := by
    ext x y; simp [pureDensity, Matrix.vecMulVec_apply]
  have hterm : ∀ l, (∑ a, ∑ b, conj (ψ a) * (E l * pureDensity ψ * (E l)ᴴ) a b * ψ b) =
      inner ℂ ψ (v l) * conj (inner ℂ ψ (v l)) := by
    intro l
    rw [hP', Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
    simp only [v, PiLp.inner_apply, RCLike.inner_apply, PiLp.toLp_apply, Matrix.vecMulVec_apply,
      Pi.star_apply, RCLike.star_def, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hle : ∀ l, (inner ℂ ψ (v l) * conj (inner ℂ ψ (v l))).re ≤ ‖v l‖ ^ 2 := by
    intro l
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have := norm_inner_le_norm (𝕜 := ℂ) ψ (v l)
    rw [hψs, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hsum : ∑ l, ‖v l‖ ^ 2 = 1 := by
    have hn : ∀ l, ‖v l‖ ^ 2 = (star ((E l).mulVec ⇑ψ) ⬝ᵥ ((E l).mulVec ⇑ψ)).re := by
      intro l
      rw [EuclideanSpace.norm_sq_eq, dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [v, PiLp.toLp_apply, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have hs2 : ∑ l, star ((E l).mulVec ⇑ψ) ⬝ᵥ ((E l).mulVec ⇑ψ) = 1 := by
      simp_rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      rw [← dotProduct_sum, ← Matrix.sum_mulVec]
      unfold IsKrausFamily at hK
      rw [hK, Matrix.one_mulVec]
      rw [← hψ]
      simp [dotProduct]
    rw [Finset.sum_congr rfl (fun l _ => hn l), ← Complex.re_sum, hs2, Complex.one_re]
  have hQ : (∑ a, ∑ b, conj (ψ a) * (krausApply E (pureDensity ψ)) a b * ψ b) =
      ∑ l, (∑ a, ∑ b, conj (ψ a) * (E l * pureDensity ψ * (E l)ᴴ) a b * ψ b) :=
    g52e_cqf_sum ψ Finset.univ _
  rw [hQ, Complex.re_sum]
  calc ∑ l, (∑ a, ∑ b, conj (ψ a) * (E l * pureDensity ψ * (E l)ᴴ) a b * ψ b).re
      = ∑ l, (inner ℂ ψ (v l) * conj (inner ℂ ψ (v l))).re := by simp only [hterm]
    _ ≤ ∑ l, ‖v l‖ ^ 2 := Finset.sum_le_sum fun l _ => hle l
    _ = 1 := hsum

/-- PDF p.2, (4) and following sentence: discrete pure-ensemble fidelity is affine in a channel. -/
theorem solution {I : Type*} {h : ℕ} (hh : 0 < h)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hmass : ∑' i, p i = 1)
    (psi : I → EuclideanSpace ℂ (Fin h)) (hpsi : ∀ i, IsState (psi i))
    (B C : Superop (Fin h) (Fin h)) (hB : IsChannel B) (hC : IsChannel C)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Summable (fun i => p i * rootFidelity (pureDensity (psi i)) (B (pureDensity (psi i))) ^ 2) ∧
    Summable (fun i => p i * rootFidelity (pureDensity (psi i)) (C (pureDensity (psi i))) ^ 2) ∧
    Summable (fun i => p i * rootFidelity (pureDensity (psi i))
      (channelMix t B C (pureDensity (psi i))) ^ 2) ∧
    IsChannel (channelMix t B C) ∧
    ensembleFidelity p psi (channelMix t B C) =
      t * ensembleFidelity p psi B + (1 - t) * ensembleFidelity p psi C := by
  have hPpsd : ∀ i, (pureDensity (psi i)).PosSemidef := by
    intro i
    have : pureDensity (psi i) = Matrix.vecMulVec (⇑(psi i)) (star ⇑(psi i)) := by
      ext x y; simp [pureDensity, Matrix.vecMulVec_apply]
    rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _
  let r : Superop (Fin h) (Fin h) → I → ℝ := fun X i =>
    (∑ a, ∑ b, conj (psi i a) * X (pureDensity (psi i)) a b * psi i b).re
  have hF : ∀ X, IsChannel X → ∀ i,
      rootFidelity (pureDensity (psi i)) (X (pureDensity (psi i))) ^ 2 = r X i := fun X hX i =>
    g52e_F2 (psi i) (g52e_unit _ (hpsi i)) _ (g52e_chan_psd X hX _ (hPpsd i))
  have hr0 : ∀ X, IsChannel X → ∀ i, 0 ≤ r X i := fun X hX i => by
    rw [← hF X hX i]; positivity
  have hr1 : ∀ X, IsChannel X → ∀ i, r X i ≤ 1 := fun X hX i => g52e_r_le X hX (psi i) (hpsi i)
  have hsum : ∀ X, IsChannel X → Summable (fun i => p i * r X i) := fun X hX =>
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hp i) (hr0 X hX i))
      (fun i => mul_le_of_le_one_right (hp i) (hr1 X hX i)) hs
  have hmixC : IsChannel (channelMix t B C) := by
    obtain ⟨m1, E1, hK1, hE1⟩ := hB
    obtain ⟨m2, E2, hK2, hE2⟩ := hC
    have ht1 : ((Real.sqrt t : ℝ) : ℂ) * ((Real.sqrt t : ℝ) : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht0]
    have ht2 : ((Real.sqrt (1 - t) : ℝ) : ℂ) * ((Real.sqrt (1 - t) : ℝ) : ℂ) = ((1 - t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
    refine ⟨m1 + m2, Fin.append (fun l => ((Real.sqrt t : ℝ) : ℂ) • E1 l)
      (fun l => ((Real.sqrt (1 - t) : ℝ) : ℂ) • E2 l), ?_, ?_⟩
    · unfold IsKrausFamily at hK1 hK2 ⊢
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Matrix.conjTranspose_smul, RCLike.star_def,
        Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Finset.smul_sum,
        hK1, hK2, ht1, ht2]
      first | (rw [← add_smul]; norm_num) | norm_num | simp
    · intro ρ
      unfold channelMix krausApply
      rw [Fin.sum_univ_add, hE1, hE2]
      unfold krausApply
      simp only [Fin.append_left, Fin.append_right, Matrix.conjTranspose_smul, RCLike.star_def,
        Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Finset.smul_sum, ht1, ht2]
      try push_cast
  have hlin : ∀ i, r (channelMix t B C) i = t * r B i + (1 - t) * r C i := by
    intro i
    simp only [r, channelMix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, add_mul,
      Finset.sum_add_distrib, Complex.add_re]
    have e1 : ∀ (c : ℂ) (Y : Matrix (Fin h) (Fin h) ℂ),
        ∑ a, ∑ b, conj (psi i a) * (c * Y a b) * psi i b =
          c * ∑ a, ∑ b, conj (psi i a) * Y a b * psi i b := by
      intro c Y; simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_; ring
    rw [e1, e1, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hFm := hF _ hmixC
  have hFB := hF B hB
  have hFC := hF C hC
  refine ⟨?_, ?_, ?_, hmixC, ?_⟩
  · simp only [hFB]; exact hsum B hB
  · simp only [hFC]; exact hsum C hC
  · simp only [hFm]; exact hsum _ hmixC
  · unfold ensembleFidelity
    simp only [hFm, hFB, hFC, hlin]
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add]
    · refine tsum_congr fun i => ?_; ring
    · exact (hsum B hB).mul_left t
    · exact (hsum C hC).mul_left (1 - t)


end

