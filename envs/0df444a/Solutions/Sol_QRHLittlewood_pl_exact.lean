-- Prove2me | solution 1 for QRHLittlewood.pl_exact
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T15:46:07.826987+00:00
-- url     : https://prove2.me/submissions/799415b2-442c-4cc1-9bbf-97cac73572c0

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

/- Rademacher's convexity bound (exponent 1/2, exact constant) for primitive Dirichlet L-functions.
Edges via the functional equation and |root number| = 1; a priori growth from the Mellin representation;
interior via a lossless Phragmén–Lindelöf argument with a strictly subharmonic comparison function. -/

open Complex LSeries

namespace QRHLittlewood



/-- For a primitive Dirichlet character modulo `N`, `|τ(χ)|² = N`. -/
theorem normSq_gaussSum_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by
  classical
  set ψ : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  set τ := gaussSum χ ψ
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar N
  set G : ZMod N → ℂ := fun a => ∑ x, χ x * ψ (a * x) with hGdef
  have hG : ∀ a, G a = χ⁻¹ a * τ := fun a => by
    have := gaussSum_mulShift_of_isPrimitive ψ hχ a
    simpa [gaussSum, AddChar.mulShift_apply, τ, G] using this
  set S : ℂ := ∑ x, χ x * (starRingEnd ℂ) (χ x) with hS
  have h1 : ∀ a x y, χ x * ψ (a * x) * ((starRingEnd ℂ) (χ y) * (starRingEnd ℂ) (ψ (a * y))) =
      χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) := fun a x y => by
    rw [← AddChar.map_neg_eq_conj, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← mul_neg]
    ring
  have expand : ∀ a, G a * (starRingEnd ℂ) (G a) =
      ∑ x, ∑ y, χ x * (starRingEnd ℂ) (χ y) * ψ (a * (x - y)) := fun a => by
    show (∑ x, χ x * ψ (a * x)) * (starRingEnd ℂ) (∑ y, χ y * ψ (a * y)) = _
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [(starRingEnd ℂ).map_mul]; exact h1 a x y
  have hL : ∑ a, G a * (starRingEnd ℂ) (G a) = N * S := by
    simp_rw [expand]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod N))) (t := Finset.univ)
      (f := fun a y => χ _ * (starRingEnd ℂ) (χ y) * ψ (a * (_ - y)))]
    simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero, ZMod.card]
    simp [hS, Finset.mul_sum, mul_comm]
  have hR : ∑ a, G a * (starRingEnd ℂ) (G a) = S * (τ * (starRingEnd ℂ) τ) := by
    simp_rw [hG, map_mul, ← MulChar.star_apply' χ, RCLike.star_def, Complex.conj_conj, hS,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have hS0 : S ≠ 0 := by
    have : S = ((∑ x, Complex.normSq (χ x) : ℝ) : ℂ) := by
      simp [hS, Complex.mul_conj]
    rw [this, Complex.ofReal_ne_zero]
    apply ne_of_gt
    exact lt_of_lt_of_le (by simp : (0 : ℝ) < Complex.normSq (χ 1))
      (Finset.single_le_sum (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ 1))
  have key : τ * (starRingEnd ℂ) τ = N := by
    have := hR.symm.trans hL
    rw [mul_comm (N : ℂ)] at this
    exact mul_left_cancel₀ hS0 this
  rw [Complex.mul_conj] at key
  exact_mod_cast key

/-- For a primitive Dirichlet character the root number has absolute value `1`. -/
theorem norm_rootNumber_of_isPrimitive {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖DirichletCharacter.rootNumber χ‖ = 1 := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hτ : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by
    rw [← normSq_gaussSum_of_isPrimitive hχ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hpow : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt N := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hN, Real.sqrt_eq_rpow]
    norm_num
  have hI : ‖(I : ℂ) ^ (if χ.Even then 0 else 1)‖ = 1 := by split_ifs <;> simp
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, hτ, hI, hpow, div_one,
    div_self (Real.sqrt_pos.2 hN).ne']




lemma norm_Gammaℝ_conj (z : ℂ) : ‖Gammaℝ ((starRingEnd ℂ) z)‖ = ‖Gammaℝ z‖ := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  simp only [Gammaℝ_def, norm_mul]
  rw [show (Real.pi : ℂ) = ((Real.pi : ℝ) : ℂ) from rfl, norm_cpow_eq_rpow_re_of_pos hπ,
    norm_cpow_eq_rpow_re_of_pos hπ]
  congr 1
  · simp
  · rw [show (starRingEnd ℂ) z / 2 = (starRingEnd ℂ) (z / 2) by
      rw [map_div₀, show (starRingEnd ℂ) 2 = 2 from Complex.conj_ofNat 2], Gamma_conj, norm_conj]

/-- On `Re z = -1/2` shifted by the parity `k`: `‖Γℝ(conj z + 2)‖ = ‖Γℝ z‖ ‖z‖ / (2π)`. -/
lemma norm_Gammaℝ_conj_add_two {z : ℂ} (hz : z ≠ 0) :
    ‖Gammaℝ ((starRingEnd ℂ) z + 2)‖ = ‖Gammaℝ z‖ * ‖z‖ / (2 * Real.pi) := by
  have hz' : (starRingEnd ℂ) z ≠ 0 := by simpa using hz
  rw [Gammaℝ_add_two hz', norm_div, norm_div, norm_mul, norm_Gammaℝ_conj, norm_conj]
  simp [abs_of_pos Real.pi_pos]
  ring

lemma inv_even_iff {q : ℕ} (χ : DirichletCharacter ℂ q) : χ⁻¹.Even ↔ χ.Even := by
  rcases χ.even_or_odd with h | h
  · have : χ⁻¹ (-1) = 1 := by rw [MulChar.inv_apply_eq_inv', h, inv_one]
    exact ⟨fun _ => h, fun _ => this⟩
  · have : χ⁻¹ (-1) = -1 := by rw [MulChar.inv_apply_eq_inv', h, inv_neg, inv_one]
    constructor
    · intro he; exact absurd (he.symm.trans this) (by norm_num)
    · intro he; exact absurd (he.symm.trans h) (by norm_num)

theorem norm_LFunction_le_zeta {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (riemannZeta (s.re : ℂ)).re := by
  have hσ : 1 < ((s.re : ℂ)).re := by simpa using hs
  have hsum1 : LSeriesSummable 1 (s.re : ℂ) := LSeriesSummable_one_iff.mpr hσ
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, ← LSeries_one_eq_riemannZeta hσ]
  have hle : ∀ n, ‖term (fun n => χ n) s n‖ ≤ ‖term 1 (s.re : ℂ) n‖ := fun n => by
    rw [norm_term_eq, norm_term_eq]
    split_ifs
    · rfl
    · simp only [ofReal_re, Pi.one_apply, norm_one]
      gcongr
      exact DirichletCharacter.norm_le_one χ _
  have hs1 : Summable fun n => ‖term 1 (s.re : ℂ) n‖ := hsum1.norm
  calc ‖LSeries (fun n => χ n) s‖ ≤ ∑' n, ‖term (fun n => χ n) s n‖ :=
        norm_tsum_le_tsum_norm (hs1.of_nonneg_of_le (fun _ => norm_nonneg _) hle)
    _ ≤ ∑' n, ‖term 1 (s.re : ℂ) n‖ :=
        Summable.tsum_le_tsum hle (hs1.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hs1
    _ = (LSeries 1 (s.re : ℂ)).re := by
        rw [LSeries, re_tsum hsum1]
        congr 1; funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · rw [term_of_ne_zero hn, norm_div, Pi.one_apply, norm_one]
          rw [show ((n : ℂ) ^ (s.re : ℂ)) = ((n : ℝ) ^ s.re : ℝ) by
            rw [ofReal_cpow (Nat.cast_nonneg n)]; simp]
          rw [norm_real, Real.norm_of_nonneg (by positivity), ← ofReal_one, ← ofReal_div, ofReal_re]



/-- The left edge `Re s = -1/2`: `‖L(s,χ)‖ ≤ ζ(3/2) · N ‖1+s‖ / (2π)` for primitive `χ`, given `‖ε(χ)‖ = 1`. -/
theorem norm_LFunction_left_edge {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hε : ‖DirichletCharacter.rootNumber χ‖ = 1) {s : ℂ} (hs : s.re = -1 / 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (riemannZeta (3 / 2 : ℂ)).re * ((N : ℝ) * ‖1 + s‖ / (2 * Real.pi)) := by
  classical
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 3 / 2 := by simp [hw, hs]; norm_num
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; norm_num at hs
  -- parity shift k and the Gamma factor
  set k : ℂ := if χ.Even then 0 else 1 with hk
  have hgf : ∀ z, DirichletCharacter.gammaFactor χ z = Gammaℝ (z + k) := fun z => by
    rcases χ.even_or_odd with h | h
    · simp [h.gammaFactor_def, hk, h]
    · simp [h.gammaFactor_def, hk, h.not_even]
  have hgf' : ∀ z, DirichletCharacter.gammaFactor χ⁻¹ z = Gammaℝ (z + k) := fun z => by
    rcases χ.even_or_odd with h | h
    · have := (inv_even_iff χ).2 h
      simp [DirichletCharacter.gammaFactor, this, hk, h]
    · have : ¬ χ⁻¹.Even := fun he => by
        have h2 := (inv_even_iff χ).1 he
        rw [DirichletCharacter.Even] at h2; rw [DirichletCharacter.Odd] at h
        rw [h] at h2; norm_num at h2
      simp [DirichletCharacter.gammaFactor, this, hk, h.not_even]
  have hkre : k.re = 0 ∨ k.re = 1 := by by_cases h : χ.Even <;> simp [hk, h]
  have hkim : k.im = 0 := by by_cases h : χ.Even <;> simp [hk, h]
  set z : ℂ := s + k with hz
  have hz0 : z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hz, hs] at this
    rcases hkre with h' | h' <;> linarith
  have hwz : w + k = (starRingEnd ℂ) z + 2 := by
    apply Complex.ext <;> simp [hw, hz, hs, hkim] <;> ring
  have hnz : ‖z‖ = ‖1 + s‖ := by
    have h1 : ‖z‖ ^ 2 = ‖1 + s‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp [hz, hs, hkim]
      rcases hkre with h' | h' <;> rw [h'] <;> ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1
  have hGs : Gammaℝ z ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]; rintro ⟨n, hn⟩
    have := congrArg Complex.im hn; simp [hz, hkim] at this
    have h2 := congrArg Complex.re hn; simp [hz, hs] at h2
    rcases hkre with h' | h' <;> rw [h'] at h2
    · have : (n : ℝ) = 1 / 4 := by linarith
      have h3 : (4 : ℝ) * n = 1 := by linarith
      norm_cast at h3; omega
    · have h3 : (4 : ℝ) * n = -1 := by linarith
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
  have hGw : Gammaℝ (w + k) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rcases hkre with h' | h' <;> simp [hwre, h'] <;> norm_num)
  -- L(s) = Λ(s)/γ(s), Λ(s) = Λ(1 - w) = N^(w - 1/2) ε Λ(χ⁻¹, w), Λ(χ⁻¹, w) = γ(w) L(χ⁻¹, w)
  have hL : DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s / Gammaℝ z := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0), hgf]
  have hFE : DirichletCharacter.completedLFunction χ s =
      (N : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ w := by
    rw [← hχ.completedLFunction_one_sub w, hw, sub_sub_cancel]
  have hw0 : w ≠ 0 := fun h => by simp [h] at hwre; norm_num at hwre
  have hLw : DirichletCharacter.completedLFunction χ⁻¹ w =
      DirichletCharacter.LFunction χ⁻¹ w * Gammaℝ (w + k) := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ w (Or.inl hw0), hgf',
      div_mul_cancel₀ _ hGw]
  have hNw : ‖(N : ℂ) ^ (w - 1 / 2)‖ = N := by
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hN]
    simp [hwre]; norm_num
  have hzeta := norm_LFunction_le_zeta χ⁻¹ (s := w) (by rw [hwre]; norm_num)
  rw [hwre] at hzeta
  have hgam : ‖Gammaℝ (w + k)‖ / ‖Gammaℝ z‖ = ‖1 + s‖ / (2 * Real.pi) := by
    rw [hwz, norm_Gammaℝ_conj_add_two hz0, hnz]
    field_simp [norm_ne_zero_iff.2 hGs]
  rw [hL, hFE, hLw, norm_div, norm_mul, norm_mul, norm_mul, hNw, hε]
  have hpos : 0 ≤ ‖1 + s‖ / (2 * Real.pi) := by positivity
  calc (N : ℝ) * 1 * (‖DirichletCharacter.LFunction χ⁻¹ w‖ * ‖Gammaℝ (w + k)‖) / ‖Gammaℝ z‖
      = N * ‖DirichletCharacter.LFunction χ⁻¹ w‖ * (‖Gammaℝ (w + k)‖ / ‖Gammaℝ z‖) := by ring
    _ = N * ‖DirichletCharacter.LFunction χ⁻¹ w‖ * (‖1 + s‖ / (2 * Real.pi)) := by rw [hgam]
    _ ≤ N * (riemannZeta (3 / 2 : ℂ)).re * (‖1 + s‖ / (2 * Real.pi)) := by
        gcongr
        simpa using hzeta
    _ = _ := by ring


/-- The left edge, unconditionally: for primitive `χ` and `Re s = -1/2`,
`‖L(s,χ)‖ ≤ ζ(3/2) · N ‖1+s‖ / (2π)`. -/
theorem norm_LFunction_left_edge' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : s.re = -1 / 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (riemannZeta (3 / 2 : ℂ)).re * ((N : ℝ) * ‖1 + s‖ / (2 * Real.pi)) :=
  norm_LFunction_left_edge hχ (norm_rootNumber_of_isPrimitive hχ) hs

end QRHLittlewood





open Complex Set Filter MeasureTheory HurwitzZeta

set_option autoImplicit false

namespace QRHLittlewood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The entire part `Λ₀` of a weak FE-pair is bounded on every closed vertical strip. -/
theorem WeakFEPair_Λ₀_bounded_strip [CompleteSpace E] (P : WeakFEPair E) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ₀ s‖ ≤ C := by
  set Q := P.toStrongFEPair
  have hQ : IsStrongFEPair Q := P.isStrongFEPair_toStrongFEPair
  have conv : ∀ c : ℝ, MellinConvergent Q.f (c : ℂ) := fun c => by
    obtain ⟨_, ht⟩ := exists_gt (c : ℂ).re
    obtain ⟨_, hu⟩ := exists_lt (c : ℂ).re
    exact mellinConvergent_of_isBigO_rpow Q.hf_int (hQ.hf_top _) ht (hQ.hf_zero _) hu
  have hint : ∀ c : ℝ, IntegrableOn (fun t : ℝ => t ^ (c - 1) * ‖Q.f t‖) (Ioi 0) := fun c => by
    have h : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ ((c : ℂ) - 1) • Q.f t‖) (Ioi 0) := (conv c).norm
    refine IntegrableOn.congr_fun h (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht]
    simp
  refine ⟨∫ t in Ioi (0 : ℝ), (t ^ (a - 1) * ‖Q.f t‖ + t ^ (b - 1) * ‖Q.f t‖), fun s hsa hsb => ?_⟩
  show ‖mellin Q.f s‖ ≤ _
  rw [mellin]
  refine norm_integral_le_of_norm_le ((hint a).add (hint b)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, ← add_mul]
  simp only [sub_re, one_re]
  gcongr
  rcases le_or_gt t 1 with h1 | h1
  · have := Real.rpow_le_rpow_of_exponent_ge ht h1 (show a - 1 ≤ s.re - 1 by linarith)
    linarith [Real.rpow_nonneg ht.le (b - 1)]
  · have := Real.rpow_le_rpow_of_exponent_le h1.le (show s.re - 1 ≤ b - 1 by linarith)
    linarith [Real.rpow_nonneg ht.le (a - 1)]

lemma hurwitzEven₀_bounded (x : UnitAddCircle) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedHurwitzZetaEven₀ x s‖ ≤ C := by
  obtain ⟨C, hC⟩ := WeakFEPair_Λ₀_bounded_strip (HurwitzZeta.hurwitzEvenFEPair x) (a / 2) (b / 2)
  refine ⟨C / 2, fun s ha hb => ?_⟩
  rw [completedHurwitzZetaEven₀, norm_div, Complex.norm_two]
  gcongr
  exact hC _ (by simp; linarith) (by simp; linarith)

lemma hurwitzOdd_bounded (x : UnitAddCircle) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖completedHurwitzZetaOdd x s‖ ≤ C := by
  obtain ⟨C, hC⟩ := WeakFEPair_Λ₀_bounded_strip (HurwitzZeta.hurwitzOddFEPair x) ((a + 1) / 2) ((b + 1) / 2)
  refine ⟨C / 2, fun s ha hb => ?_⟩
  rw [completedHurwitzZetaOdd, norm_div, Complex.norm_two, WeakFEPair.Λ]
  simp only [HurwitzZeta.hurwitzOddFEPair, smul_zero, sub_zero]
  gcongr
  exact hC _ (by simp; linarith) (by simp; linarith)

/-- For a nontrivial Dirichlet character modulo `N ≥ 2`, the completed L-function is bounded on
every closed vertical strip. -/
theorem completedLFunction_bounded_strip {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖DirichletCharacter.completedLFunction χ s‖ ≤ C := by
  classical
  choose Ce hCe using fun j : ZMod N => hurwitzEven₀_bounded (ZMod.toAddCircle j) a b
  choose Co hCo using fun j : ZMod N => hurwitzOdd_bounded (ZMod.toAddCircle j) a b
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set K : ℝ := max ((N : ℝ) ^ (-a)) ((N : ℝ) ^ (-b))
  refine ⟨K * (∑ j, Ce j) + K * (∑ j, Co j), fun s ha hb => ?_⟩
  have h0 : χ 0 = 0 := by
    have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
    exact MulChar.map_nonunit χ not_isUnit_zero
  have hsum : ∑ j, χ j = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hK : ‖(N : ℂ) ^ (-s)‖ ≤ K := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by simp, norm_cpow_eq_rpow_re_of_pos hNpos, neg_re]
    rcases le_total (1 : ℝ) N with h1 | h1
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_ge hNpos h1 (by linarith))
  have hK0 : 0 ≤ K := le_max_of_le_left (Real.rpow_nonneg hNpos.le _)
  rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq, h0, hsum]
  simp only [mul_zero, zero_div, sub_zero]
  rw [ZMod.completedLFunction₀]
  have hχn : ∀ j, ‖χ j‖ ≤ 1 := fun j => DirichletCharacter.norm_le_one χ j
  have he : ‖∑ j, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ ≤ ∑ j, Ce j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    calc ‖χ j‖ * _ ≤ 1 * Ce j := by
          gcongr
          · exact hχn j
          · exact hCe j s ha hb
      _ = Ce j := one_mul _
  have ho : ‖∑ j, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ ≤ ∑ j, Co j := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    calc ‖χ j‖ * _ ≤ 1 * Co j := by
          gcongr
          · exact hχn j
          · exact hCo j s ha hb
      _ = Co j := one_mul _
  calc _ ≤ ‖(N : ℂ) ^ (-s) * ∑ j, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖ +
        ‖(N : ℂ) ^ (-s) * ∑ j, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖ := norm_add_le _ _
    _ ≤ K * (∑ j, Ce j) + K * (∑ j, Co j) := by
        rw [norm_mul, norm_mul]
        gcongr

end QRHLittlewood


open Complex Set MeasureTheory

set_option autoImplicit false

namespace QRHLittlewood

/-- `‖Γ(z)‖ ≤ Γ(Re z)` for `Re z > 0`. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) : ‖Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Gamma_eq_integral hz, Real.Gamma_eq_integral hz, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x (hx : 0 < x) => ?_)
  rw [norm_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- `‖sin z‖ ≤ exp |Im z|`. -/
theorem norm_sin_le_exp (z : ℂ) : ‖sin z‖ ≤ Real.exp |z.im| := by
  rw [sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h1 : ‖exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  calc ‖exp (-z * I) - exp (z * I)‖ / 2 ≤ (‖exp (-z * I)‖ + ‖exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by
        gcongr <;> simp [le_abs_self, neg_le_abs]
    _ = Real.exp |z.im| := by ring

/-- For `w` with `0 < Re (2 - w)` and `w ≠ 1`: `‖1/Γ(w)‖ ≤ Γ(Re(2-w)) exp(π|Im w|) / (π ‖1 - w‖)`. -/
theorem norm_inv_Gamma_le {w : ℂ} (hw1 : w ≠ 1) (hre : 0 < (2 - w).re) (hG : Gamma w ≠ 0) :
    ‖(Gamma w)⁻¹‖ ≤ Real.Gamma (2 - w).re * Real.exp (Real.pi * |w.im|) / (Real.pi * ‖1 - w‖) := by
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw1)
  have hrefl := Gamma_mul_Gamma_one_sub w
  have hrec : Gamma (2 - w) = (1 - w) * Gamma (1 - w) := by
    rw [show (2 : ℂ) - w = (1 - w) + 1 by ring, Gamma_add_one _ h1w]
  have hG1 : Gamma (1 - w) ≠ 0 := fun h => by
    rw [h, mul_zero] at hrec; exact Gamma_ne_zero_of_re_pos hre hrec
  have hsin : sin (Real.pi * w) ≠ 0 := by
    intro h; rw [h, div_zero] at hrefl
    exact mul_ne_zero hG hG1 hrefl
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : Gamma w * Gamma (1 - w) * sin (Real.pi * w) = Real.pi := by
    rw [hrefl, div_mul_cancel₀ _ hsin]
  -- 1/Γ(w) = Γ(1-w) sin(πw)/π = Γ(2-w) sin(πw) / (π (1-w))
  have hinv : (Gamma w)⁻¹ = Gamma (2 - w) * sin (Real.pi * w) / (Real.pi * (1 - w)) := by
    rw [hrec, eq_div_iff (mul_ne_zero hπ h1w)]
    have hii : Gamma w * (Gamma w)⁻¹ = 1 := mul_inv_cancel₀ hG
    linear_combination (-(Gamma w)⁻¹ * (1 - w)) * hprod +
      ((1 - w) * Gamma (1 - w) * sin (Real.pi * w)) * hii
  rw [hinv, norm_div, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hs := norm_sin_le_exp (Real.pi * w)
  have him : (↑Real.pi * w).im = Real.pi * w.im := by simp
  rw [him, abs_mul, abs_of_pos Real.pi_pos] at hs
  have hg := norm_Gamma_le_Gamma_re hre
  gcongr

end QRHLittlewood


open Complex Set

set_option autoImplicit false

namespace QRHLittlewood

lemma Gamma_real_le_on (x : ℝ) (h1 : 3 / 4 ≤ x) (h2 : x ≤ 9 / 4) :
    Real.Gamma x ≤ max (Real.Gamma (3 / 4)) (Real.Gamma (9 / 4)) :=
  Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num : (3/4 : ℝ) ∈ Ioi 0)
    (by norm_num : (9/4 : ℝ) ∈ Ioi 0) ⟨h1, h2⟩

/-- A priori growth: for a nontrivial Dirichlet character modulo `N ≥ 2`, on `-1/2 ≤ Re s ≤ 3/2`
with `|Im s| ≥ 1`, `‖L(s, χ)‖ ≤ C exp(π |Im s| / 2)`. -/
theorem LFunction_growth {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 1 ≤ |s.im| →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * Real.exp (Real.pi * |s.im| / 2) := by
  classical
  obtain ⟨CΛ, hΛ⟩ := completedLFunction_bounded_strip hN hχ (-1 / 2) (3 / 2)
  set G := max (Real.Gamma (3 / 4)) (Real.Gamma (9 / 4))
  refine ⟨CΛ * (Real.pi ^ (5 / 4 : ℝ) * (G * 2 / Real.pi)), fun s ha hb ht => ?_⟩
  have hs0 : s ≠ 0 := fun h => by simp [h] at ht; linarith
  set k : ℂ := if χ.Even then 0 else 1 with hk
  have hgf : DirichletCharacter.gammaFactor χ s = Gammaℝ (s + k) := by
    rcases χ.even_or_odd with h | h
    · simp [h.gammaFactor_def, hk, h]
    · simp [h.gammaFactor_def, hk, h.not_even]
  have hkre : k.re = 0 ∨ k.re = 1 := by by_cases h : χ.Even <;> simp [hk, h]
  have hkim : k.im = 0 := by by_cases h : χ.Even <;> simp [hk, h]
  set w : ℂ := (s + k) / 2 with hw
  have hwim : w.im = s.im / 2 := by simp [hw, hkim]
  have hwre1 : -1 / 4 ≤ w.re := by simp [hw]; rcases hkre with h | h <;> rw [h] <;> linarith
  have hwre2 : w.re ≤ 5 / 4 := by simp [hw]; rcases hkre with h | h <;> rw [h] <;> linarith
  have hw1 : w ≠ 1 := fun h => by
    have := congrArg Complex.im h; rw [hwim] at this; simp at this; rw [this] at ht; simp at ht; linarith
  have hGw : Gamma w ≠ 0 := Gamma_ne_zero (fun m h => by
    have := congrArg Complex.im h; rw [hwim] at this; simp at this; rw [this] at ht; simp at ht; linarith)
  have hre2 : 0 < (2 - w).re := by simp; linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  -- L = Λ / Γℝ(s+k) = Λ π^{(s+k)/2} / Γ(w)
  have hL : DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s * ((Real.pi : ℂ) ^ w * (Gamma w)⁻¹) := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0), hgf, Gammaℝ_def,
      div_eq_mul_inv, mul_inv, ← cpow_neg]
    congr 2; rw [hw]; ring
  have hpow : ‖(Real.pi : ℂ) ^ w‖ ≤ Real.pi ^ (5 / 4 : ℝ) := by
    rw [show (Real.pi : ℂ) = ((Real.pi : ℝ) : ℂ) from rfl, norm_cpow_eq_rpow_re_of_pos hπ]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) hwre2
  have h1w : 1 / 2 ≤ ‖1 - w‖ := by
    have := Complex.abs_im_le_norm (1 - w)
    simp [hwim, abs_div] at this
    linarith
  have hinv := norm_inv_Gamma_le hw1 hre2 hGw
  have hGre : Real.Gamma (2 - w).re ≤ G := Gamma_real_le_on _ (by simp; linarith) (by simp; linarith)
  have hinv' : ‖(Gamma w)⁻¹‖ ≤ G * 2 / Real.pi * Real.exp (Real.pi * |s.im| / 2) := by
    refine hinv.trans ?_
    rw [hwim, abs_div, abs_two]
    have hG0 : 0 ≤ Real.Gamma (2 - w).re := (Real.Gamma_pos_of_pos hre2).le
    calc Real.Gamma (2 - w).re * Real.exp (Real.pi * (|s.im| / 2)) / (Real.pi * ‖1 - w‖)
        ≤ G * Real.exp (Real.pi * (|s.im| / 2)) / (Real.pi * (1 / 2)) := by
          gcongr
      _ = _ := by ring_nf
  rw [hL, norm_mul, norm_mul]
  have hΛ' := hΛ s ha hb
  have hCΛ : 0 ≤ CΛ := (norm_nonneg _).trans hΛ'
  calc ‖DirichletCharacter.completedLFunction χ s‖ * (‖(Real.pi : ℂ) ^ w‖ * ‖(Gamma w)⁻¹‖)
      ≤ CΛ * (Real.pi ^ (5 / 4 : ℝ) * (G * 2 / Real.pi * Real.exp (Real.pi * |s.im| / 2))) := by
        gcongr
    _ = _ := by ring

end QRHLittlewood


open Complex Set Filter Topology

set_option autoImplicit false

namespace QRHLittlewood

/-- Second-derivative test (necessary form): at a local maximum, the second derivative is `≤ 0`. -/
theorem second_deriv_nonpos_of_isLocalMax {φ φ' : ℝ → ℝ} {c : ℝ} (hmax : IsLocalMax φ 0)
    (hd : ∀ᶠ x in 𝓝 0, HasDerivAt φ (φ' x) x) (hd2 : HasDerivAt φ' c 0) : c ≤ 0 := by
  by_contra hc
  push Not at hc
  have h0 : φ' 0 = 0 := hmax.hasDerivAt_eq_zero hd.self_of_nhds
  -- φ' x / x → c > 0, so φ' > 0 on a right neighbourhood
  have hslope := hd2.tendsto_slope_zero_right
  simp only [zero_add, h0, sub_zero] at hslope
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < φ' x := by
    filter_upwards [hslope.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with x hx (hx0 : 0 < x)
    have : 0 < x⁻¹ * φ' x := by simpa [smul_eq_mul] using hx
    exact pos_of_mul_pos_right this (inv_pos.2 hx0).le
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < φ' x ∧ HasDerivAt φ (φ' x) x ∧ φ x ≤ φ 0 :=
    hpos.and (nhdsWithin_le_nhds (hd.and hmax))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  set x := u / 2
  have hx0 : 0 < x := by positivity
  have hxu : x < u := by simp only [x]; linarith
  have hcont : ContinuousOn φ (Icc 0 x) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · subst h; exact hd.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hsub ⟨h, lt_of_le_of_lt hy.2 hxu⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ φ' hx0 hcont
    (fun y hy => (hsub ⟨hy.1, hy.2.trans hxu⟩).2.1)
  have hξpos := (hsub ⟨hξ.1, hξ.2.trans hxu⟩).1
  have hle := (hsub ⟨hx0, hxu⟩).2.2
  rw [hξeq, sub_zero] at hξpos
  have : 0 < φ x - φ 0 := by
    have := mul_pos hξpos hx0; rwa [div_mul_cancel₀ _ hx0.ne'] at this
  linarith


/-! ### Line derivatives of `Φ(σ, t) = (t/2) arctan (t / (1 + σ))` -/


lemma Phi_x_deriv (U tp x : ℝ) (hU : 0 < U + x) :
    HasDerivAt (fun x => tp / 2 * Real.arctan (tp / (U + x)))
      (-(tp ^ 2) / (2 * ((U + x) ^ 2 + tp ^ 2))) x := by
  have h0 : HasDerivAt (fun x : ℝ => U + x) 1 x := (hasDerivAt_id' x).const_add U
  have h1 := (hasDerivAt_const x tp).div h0 (ne_of_gt hU)
  exact (h1.arctan.const_mul (tp / 2)).congr_deriv (by (try simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, add_zero, Nat.cast_ofNat]); first | (field_simp; ring) | ring | field_simp)

lemma Phi_x_deriv2 (U tp : ℝ) (hU : 0 < U) :
    HasDerivAt (fun x => -(tp ^ 2) / (2 * ((U + x) ^ 2 + tp ^ 2))) (tp ^ 2 * U / (U ^ 2 + tp ^ 2) ^ 2) 0 := by
  have h0 : HasDerivAt (fun x : ℝ => U + x) 1 0 := (hasDerivAt_id' 0).const_add U
  have hD := ((h0.pow 2).add_const (tp ^ 2)).const_mul 2
  have hne : (2 * ((U + 0) ^ 2 + tp ^ 2)) ≠ 0 := by positivity
  exact ((hasDerivAt_const (0 : ℝ) (-(tp ^ 2))).div hD hne).congr_deriv (by (try simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, add_zero, Nat.cast_ofNat]); first | (field_simp; ring) | ring | field_simp)

lemma Phi_y_deriv (U tp y : ℝ) (hU : 0 < U) :
    HasDerivAt (fun y => (tp + y) / 2 * Real.arctan ((tp + y) / U))
      (Real.arctan ((tp + y) / U) / 2 + (tp + y) / 2 * (U / (U ^ 2 + (tp + y) ^ 2))) y := by
  have h0 : HasDerivAt (fun y : ℝ => tp + y) 1 y := (hasDerivAt_id' y).const_add tp
  have h1 := h0.div_const U
  have h2 := h0.div_const 2
  have key : (1 : ℝ) / (1 + ((tp + y) / U) ^ 2) * (1 / U) = U / (U ^ 2 + (tp + y) ^ 2) := by
    have h3 : U ^ 2 + (tp + y) ^ 2 ≠ 0 := by positivity
    have h4 : U ≠ 0 := hU.ne'
    rw [div_pow, one_add_div (pow_ne_zero 2 h4), one_div_div, div_mul_div_comm, mul_one,
      sq, mul_div_mul_right _ _ h4]
  exact (h2.mul h1.arctan).congr_deriv (by rw [key]; ring)

lemma Phi_y_deriv2 (U tp : ℝ) (hU : 0 < U) :
    HasDerivAt (fun y => Real.arctan ((tp + y) / U) / 2 + (tp + y) / 2 * (U / (U ^ 2 + (tp + y) ^ 2)))
      (U / (U ^ 2 + tp ^ 2) - tp ^ 2 * U / (U ^ 2 + tp ^ 2) ^ 2) 0 := by
  have h0 : HasDerivAt (fun y : ℝ => tp + y) 1 0 := (hasDerivAt_id' 0).const_add tp
  have hD := (h0.pow 2).const_add (U ^ 2)
  have hne : U ^ 2 + (tp + 0) ^ 2 ≠ 0 := by positivity
  have h3 := (hasDerivAt_const (0 : ℝ) U).div hD hne
  exact (((h0.div_const U).arctan.div_const 2).add ((h0.div_const 2).mul h3)).congr_deriv (by (try simp only [Pi.div_apply, Pi.pow_apply, Pi.add_apply, add_zero, Nat.cast_ofNat]); first | (field_simp; ring) | ring | field_simp)

/-! ### Line derivatives of the barrier `H(σ, t) = cos (k (σ - 1/2)) cosh (k t)` -/

lemma H_x_deriv (k a c x : ℝ) :
    HasDerivAt (fun x => Real.cos (k * (a + x)) * c) (-(k * Real.sin (k * (a + x))) * c) x := by
  have h0 : HasDerivAt (fun x : ℝ => k * (a + x)) k x := by
    simpa using ((hasDerivAt_id' x).const_add a).const_mul k
  exact (h0.cos.mul_const c).congr_deriv (by ring)

lemma H_x_deriv2 (k a c : ℝ) :
    HasDerivAt (fun x => -(k * Real.sin (k * (a + x))) * c) (-(k ^ 2 * Real.cos (k * a)) * c) 0 := by
  have h0 : HasDerivAt (fun x : ℝ => k * (a + x)) k 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add a).const_mul k
  exact ((h0.sin.const_mul k).neg.mul_const c).congr_deriv (by rw [add_zero]; ring)

lemma H_y_deriv (k c b y : ℝ) :
    HasDerivAt (fun y => c * Real.cosh (k * (b + y))) (c * (k * Real.sinh (k * (b + y)))) y := by
  have h0 : HasDerivAt (fun y : ℝ => k * (b + y)) k y := by
    simpa using ((hasDerivAt_id' y).const_add b).const_mul k
  exact (h0.cosh.const_mul c).congr_deriv (by ring)

lemma H_y_deriv2 (k c b : ℝ) :
    HasDerivAt (fun y => c * (k * Real.sinh (k * (b + y)))) (c * (k ^ 2 * Real.cosh (k * b))) 0 := by
  have h0 : HasDerivAt (fun y : ℝ => k * (b + y)) k 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add b).const_mul k
  exact ((h0.sinh.const_mul k).const_mul c).congr_deriv (by rw [add_zero]; ring)


/-- `arg z = arctan (Im z / Re z)` for `Re z > 0`. -/
lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  rw [arg_of_re_nonneg hz.le, Real.arctan_eq_arcsin]
  congr 1
  have hn : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
  have h1 : Real.sqrt (1 + (z.im / z.re) ^ 2) = Real.sqrt (z.re ^ 2 + z.im ^ 2) / z.re := by
    have e : 1 + (z.im / z.re) ^ 2 = (z.re ^ 2 + z.im ^ 2) / z.re ^ 2 := by field_simp
    rw [e, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hz.le]
  rw [hn, h1]
  have : 0 < Real.sqrt (z.re ^ 2 + z.im ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-! ### The holomorphic part along the two coordinate lines -/

lemma re_line_x {ℓ : ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hℓ : DifferentiableOn ℂ ℓ (Metric.ball p r)) :
    (∀ᶠ x : ℝ in 𝓝 0, HasDerivAt (fun x : ℝ => (ℓ (p + (x : ℂ))).re) (deriv ℓ (p + (x : ℂ))).re x) ∧
      HasDerivAt (fun x : ℝ => (deriv ℓ (p + (x : ℂ))).re) (deriv (deriv ℓ) p).re 0 := by
  have hopen : IsOpen (Metric.ball p r) := Metric.isOpen_ball
  have hℓ' : DifferentiableOn ℂ (deriv ℓ) (Metric.ball p r) := hℓ.deriv hopen
  constructor
  · have : ∀ᶠ x : ℝ in 𝓝 0, p + (x : ℂ) ∈ Metric.ball p r := by
      have hc : Continuous fun x : ℝ => p + (x : ℂ) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds p hr : _ ∈ 𝓝 (p + ((0 : ℝ) : ℂ)))
    filter_upwards [this] with x hx
    have hd : HasDerivAt ℓ (deriv ℓ (p + x)) (p + x) :=
      (hℓ.differentiableAt (hopen.mem_nhds hx)).hasDerivAt
    exact (hd.comp_const_add p (x : ℂ)).real_of_complex
  · have hd : HasDerivAt (deriv ℓ) (deriv (deriv ℓ) p) (p + ((0 : ℝ) : ℂ)) := by
      simpa using (hℓ'.differentiableAt (hopen.mem_nhds (Metric.mem_ball_self hr))).hasDerivAt
    exact (hd.comp_const_add p ((0 : ℝ) : ℂ)).real_of_complex

lemma comp_line_I {g : ℂ → ℂ} {p w : ℂ} (hg : DifferentiableAt ℂ g (p + w * I)) :
    HasDerivAt (fun w : ℂ => g (p + w * I)) (deriv g (p + w * I) * I) w := by
  have hlin : HasDerivAt (fun w : ℂ => p + w * I) I w := by
    simpa using ((hasDerivAt_id' w).mul_const I).const_add p
  exact hg.hasDerivAt.comp w hlin

lemma re_line_y {ℓ : ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hℓ : DifferentiableOn ℂ ℓ (Metric.ball p r)) :
    (∀ᶠ y : ℝ in 𝓝 0, HasDerivAt (fun y : ℝ => (ℓ (p + (y : ℂ) * I)).re) (deriv ℓ (p + (y : ℂ) * I) * I).re y) ∧
      HasDerivAt (fun y : ℝ => (deriv ℓ (p + (y : ℂ) * I) * I).re) (-(deriv (deriv ℓ) p).re) 0 := by
  have hopen : IsOpen (Metric.ball p r) := Metric.isOpen_ball
  have hℓ' : DifferentiableOn ℂ (deriv ℓ) (Metric.ball p r) := hℓ.deriv hopen
  have hlin : ∀ w : ℂ, HasDerivAt (fun w : ℂ => p + w * I) I w := fun w => by
    simpa using ((hasDerivAt_id' w).mul_const I).const_add p
  constructor
  · have : ∀ᶠ y : ℝ in 𝓝 0, p + (y : ℂ) * I ∈ Metric.ball p r := by
      have hc : Continuous fun y : ℝ => p + (y : ℂ) * I := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds p hr : _ ∈ 𝓝 (p + ((0 : ℝ) : ℂ) * I))
    filter_upwards [this] with y hy
    have hd : HasDerivAt ℓ (deriv ℓ (p + y * I)) (p + y * I) :=
      (hℓ.differentiableAt (hopen.mem_nhds hy)).hasDerivAt
    have he : HasDerivAt (fun w : ℂ => ℓ (p + w * I)) (deriv ℓ (p + y * I) * I) (y : ℂ) :=
      hd.comp (y : ℂ) (hlin y)
    exact he.real_of_complex
  · have hd : HasDerivAt (deriv ℓ) (deriv (deriv ℓ) p) (p + ((0 : ℝ) : ℂ) * I) := by
      simpa using (hℓ'.differentiableAt (hopen.mem_nhds (Metric.mem_ball_self hr))).hasDerivAt
    have he0 : HasDerivAt (fun w : ℂ => deriv ℓ (p + w * I)) (deriv (deriv ℓ) p * I) ((0 : ℝ) : ℂ) := by
      have := comp_line_I (g := deriv ℓ) (p := p) (w := ((0 : ℝ) : ℂ))
        (by simpa using hℓ'.differentiableAt (hopen.mem_nhds (Metric.mem_ball_self hr)))
      simpa using this
    have he : HasDerivAt (fun w : ℂ => deriv ℓ (p + w * I) * I) (deriv (deriv ℓ) p * I * I) ((0 : ℝ) : ℂ) :=
      he0.mul_const I
    convert he.real_of_complex using 1
    simp [mul_assoc]


/-- `Φ(s) = (Im s / 2) · arctan (Im s / (1 + Re s))`. -/
noncomputable def Phi (s : ℂ) : ℝ := s.im / 2 * Real.arctan (s.im / (1 + s.re))

/-- The barrier `H(s) = cos (π/4 · (Re s - 1/2)) · cosh (π/4 · Im s)`. -/
noncomputable def Hb (s : ℂ) : ℝ :=
  Real.cos (Real.pi / 4 * (s.re - 1 / 2)) * Real.cosh (Real.pi / 4 * s.im)

/-- Local contradiction: `Re ℓ + Φ - ε H` cannot have a local maximum where `1 + Re p > 0`. -/
theorem no_local_max {ℓ : ℂ → ℂ} {p : ℂ} {r ε : ℝ} (hr : 0 < r)
    (hℓ : DifferentiableOn ℂ ℓ (Metric.ball p r)) (hU : 0 < 1 + p.re)
    (hmax : IsLocalMax (fun s => (ℓ s).re + Phi s - ε * Hb s) p) : False := by
  set U := 1 + p.re
  set tp := p.im
  set k : ℝ := Real.pi / 4
  set a : ℝ := p.re - 1 / 2
  -- the x-line
  have hx := re_line_x hr hℓ
  have hmax1 : IsLocalMax (fun x : ℝ => (ℓ (p + (x : ℂ))).re + Phi (p + (x : ℂ)) - ε * Hb (p + (x : ℂ))) 0 := by
    have hc : Continuous fun x : ℝ => p + (x : ℂ) := by fun_prop
    have hm' : IsLocalMax (fun s => (ℓ s).re + Phi s - ε * Hb s) ((fun x : ℝ => p + (x : ℂ)) 0) := by
      simpa using hmax
    exact IsLocalMax.comp_continuous (g := fun x : ℝ => p + (x : ℂ)) hm' hc.continuousAt
  have eqx : ∀ x : ℝ, (ℓ (p + (x : ℂ))).re + Phi (p + (x : ℂ)) - ε * Hb (p + (x : ℂ)) =
      (ℓ (p + (x : ℂ))).re + tp / 2 * Real.arctan (tp / (U + x)) -
        ε * (Real.cos (k * (a + x)) * Real.cosh (k * tp)) := fun x => by
    simp only [Phi, Hb, add_re, ofReal_re, add_im, ofReal_im, add_zero, U, tp, k, a]
    ring_nf
  have hUx : ∀ᶠ x : ℝ in 𝓝 0, 0 < U + x := by
    have : Tendsto (fun x : ℝ => U + x) (𝓝 0) (𝓝 (U + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.eventually (lt_mem_nhds hU)
  have c1 := second_deriv_nonpos_of_isLocalMax (φ := fun x : ℝ =>
      (ℓ (p + (x : ℂ))).re + tp / 2 * Real.arctan (tp / (U + x)) -
        ε * (Real.cos (k * (a + x)) * Real.cosh (k * tp)))
    (φ' := fun x => (deriv ℓ (p + (x : ℂ))).re + -(tp ^ 2) / (2 * ((U + x) ^ 2 + tp ^ 2)) -
        ε * (-(k * Real.sin (k * (a + x))) * Real.cosh (k * tp)))
    (by simpa only [eqx] using hmax1)
    (by
      filter_upwards [hx.1, hUx] with x h1 h2
      exact (h1.add (Phi_x_deriv U tp x h2)).sub ((H_x_deriv k a (Real.cosh (k * tp)) x).const_mul ε))
    ((hx.2.add (Phi_x_deriv2 U tp hU)).sub ((H_x_deriv2 k a (Real.cosh (k * tp))).const_mul ε))
  -- the y-line
  have hy := re_line_y hr hℓ
  have hmax2 : IsLocalMax (fun y : ℝ => (ℓ (p + (y : ℂ) * I)).re + Phi (p + (y : ℂ) * I) -
      ε * Hb (p + (y : ℂ) * I)) 0 := by
    have hc : Continuous fun y : ℝ => p + (y : ℂ) * I := by fun_prop
    have hm' : IsLocalMax (fun s => (ℓ s).re + Phi s - ε * Hb s) ((fun y : ℝ => p + (y : ℂ) * I) 0) := by
      simpa using hmax
    exact IsLocalMax.comp_continuous (g := fun y : ℝ => p + (y : ℂ) * I) hm' hc.continuousAt
  have eqy : ∀ y : ℝ, (ℓ (p + (y : ℂ) * I)).re + Phi (p + (y : ℂ) * I) - ε * Hb (p + (y : ℂ) * I) =
      (ℓ (p + (y : ℂ) * I)).re + (tp + y) / 2 * Real.arctan ((tp + y) / U) -
        ε * (Real.cos (k * a) * Real.cosh (k * (tp + y))) := fun y => by
    simp only [Phi, Hb, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, U, tp, k, a]
    ring_nf
  have c2 := second_deriv_nonpos_of_isLocalMax (φ := fun y : ℝ =>
      (ℓ (p + (y : ℂ) * I)).re + (tp + y) / 2 * Real.arctan ((tp + y) / U) -
        ε * (Real.cos (k * a) * Real.cosh (k * (tp + y))))
    (φ' := fun y => (deriv ℓ (p + (y : ℂ) * I) * I).re +
        (Real.arctan ((tp + y) / U) / 2 + (tp + y) / 2 * (U / (U ^ 2 + (tp + y) ^ 2))) -
        ε * (Real.cos (k * a) * (k * Real.sinh (k * (tp + y)))))
    (by simpa only [eqy] using hmax2)
    (by
      filter_upwards [hy.1] with y h1
      exact (h1.add (Phi_y_deriv U tp y hU)).sub ((H_y_deriv k (Real.cos (k * a)) tp y).const_mul ε))
    ((hy.2.add (Phi_y_deriv2 U tp hU)).sub ((H_y_deriv2 k (Real.cos (k * a)) tp).const_mul ε))
  -- the two second derivatives add up to `U / (U² + t²) > 0`
  have hpos : 0 < U / (U ^ 2 + tp ^ 2) := by positivity
  have hsum : (deriv (deriv ℓ) p).re + tp ^ 2 * U / (U ^ 2 + tp ^ 2) ^ 2 -
      ε * (-(k ^ 2 * Real.cos (k * a)) * Real.cosh (k * tp)) +
      (-(deriv (deriv ℓ) p).re + (U / (U ^ 2 + tp ^ 2) - tp ^ 2 * U / (U ^ 2 + tp ^ 2) ^ 2) -
        ε * (Real.cos (k * a) * (k ^ 2 * Real.cosh (k * tp)))) = U / (U ^ 2 + tp ^ 2) := by ring
  linarith


/-- The holomorphic majorant `Ψ(s) = log C + ((3/2 - s)/2) (log A + Log (1 + s))`. -/
noncomputable def Psi (C A : ℝ) (s : ℂ) : ℂ :=
  (Real.log C : ℂ) + (3 / 2 - s) / 2 * ((Real.log A : ℂ) + Complex.log (1 + s))

/-- The target exponent `W(s) = log C + ((3/2 - σ)/2) (log A + log ‖1 + s‖)`. -/
noncomputable def Wt (C A : ℝ) (s : ℂ) : ℝ :=
  Real.log C + (3 / 2 - s.re) / 2 * (Real.log A + Real.log ‖1 + s‖)

lemma Psi_re (C A : ℝ) {s : ℂ} (hs : 0 < 1 + s.re) : (Psi C A s).re = Wt C A s + Phi s := by
  have harg : (Complex.log (1 + s)).im = Real.arctan (s.im / (1 + s.re)) := by
    rw [Complex.log_im, arg_eq_arctan_of_re_pos (by simpa using hs)]; simp
  simp only [Psi, Wt, Phi, add_re, ofReal_re, mul_re, div_re, sub_re, add_im, ofReal_im, Complex.log_re,
    harg, sub_im, div_im]
  norm_num
  ring

lemma exp_Wt {C A : ℝ} (hC : 0 < C) (hA : 0 < A) {s : ℂ} (hs : 0 < ‖1 + s‖) :
    Real.exp (Wt C A s) = C * (A * ‖1 + s‖) ^ ((3 / 2 - s.re) / 2) := by
  rw [Wt, Real.exp_add, Real.exp_log hC, ← Real.log_mul hA.ne' hs.ne', mul_comm _ (Real.log _),
    ← Real.rpow_def_of_pos (by positivity)]


lemma Hb_nonneg {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) : 0 ≤ Hb s := by
  have hc : 0 ≤ Real.cos (Real.pi / 4 * (s.re - 1 / 2)) := Real.cos_nonneg_of_mem_Icc
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  exact mul_nonneg hc (Real.cosh_pos _).le

lemma cosh_ge_sq (x : ℝ) : x ^ 2 / 4 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have h2 := Real.add_one_le_exp (-|x|)
  have h3 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [abs_nonneg x]

lemma Hb_lower {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    (Real.pi / 4 * s.im) ^ 2 / 8 ≤ Hb s := by
  have hc : 1 / 2 ≤ Real.cos (Real.pi / 4 * (s.re - 1 / 2)) := by
    have hb : |Real.pi / 4 * (s.re - 1 / 2)| ≤ Real.pi / 4 := by
      rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]
    have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hb
    rw [Real.cos_abs] at this
    have h4 : (1 / 2 : ℝ) ≤ Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      have : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      linarith
    linarith
  have hch := cosh_ge_sq (Real.pi / 4 * s.im)
  unfold Hb
  nlinarith [Real.cosh_pos (Real.pi / 4 * s.im), sq_nonneg (Real.pi / 4 * s.im)]


/-- **Exact polynomial-boundary Phragmén–Lindelöf on `-1/2 ≤ Re s ≤ 3/2`.** If `f` is entire, bounded by
`C · A‖1+s‖` on `Re s = -1/2` and by `C` on `Re s = 3/2`, and of at most exponential growth in the strip,
then `‖f s‖ ≤ C (A ‖1+s‖)^((3/2 - Re s)/2)` throughout the strip. -/
theorem pl_exact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C A : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖f s‖ ≤ C * (A * ‖1 + s‖))
    (hright : ∀ s : ℂ, s.re = 3 / 2 → ‖f s‖ ≤ C)
    (hgrowth : ∃ B κ : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖f s‖ ≤ B * Real.exp (κ * |s.im|))
    (s₁ : ℂ) (h₁ : -1 / 2 ≤ s₁.re) (h₂ : s₁.re ≤ 3 / 2) :
    ‖f s₁‖ ≤ C * (A * ‖1 + s₁‖) ^ ((3 / 2 - s₁.re) / 2) := by
  have hnorm : ∀ s : ℂ, -1 / 2 ≤ s.re → 1 / 2 ≤ ‖1 + s‖ := fun s hs => by
    have := Complex.re_le_norm (1 + s); simp at this; linarith
  by_contra hcon
  push Not at hcon
  have hn1 : 0 < ‖1 + s₁‖ := by linarith [hnorm s₁ h₁]
  rw [← exp_Wt hC hA hn1] at hcon
  have hf1 : 0 < ‖f s₁‖ := (Real.exp_pos _).trans hcon
  set δ := Real.log ‖f s₁‖ - Wt C A s₁ with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, sub_pos, ← Real.exp_lt_exp, Real.exp_log hf1]; exact hcon
  set ε : ℝ := δ / (2 * (Hb s₁ + 1)) with hε
  have hH1 := Hb_nonneg h₁ h₂
  have hε0 : 0 < ε := by positivity
  set G : ℂ → ℝ := fun s => ‖f s‖ * Real.exp (-Wt C A s - ε * Hb s) with hG
  have hG1 : 1 < G s₁ := by
    have e : G s₁ = Real.exp (δ - ε * Hb s₁) := by
      simp only [hG, hδ]
      rw [sub_sub, show Real.log ‖f s₁‖ - (Wt C A s₁ + ε * Hb s₁) =
        Real.log ‖f s₁‖ + (-Wt C A s₁ - ε * Hb s₁) by ring, Real.exp_add, Real.exp_log hf1]
    rw [e, ← Real.exp_zero]
    apply Real.exp_lt_exp.2
    have : ε * Hb s₁ ≤ δ / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  -- growth constants
  obtain ⟨B, κ, hB⟩ := hgrowth
  set B' := max B 1
  set m0 := Real.log A + Real.log (1 / 2)
  set K0 := Real.exp (-Real.log C + |m0|)
  have hWlow : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → Real.exp (-Wt C A s) ≤ K0 := by
    intro s h1 h2
    apply Real.exp_le_exp.2
    have hX : m0 ≤ Real.log A + Real.log ‖1 + s‖ := by
      have := Real.log_le_log (by norm_num) (hnorm s h1); linarith
    have he0 : 0 ≤ (3 / 2 - s.re) / 2 := by linarith
    have he1 : (3 / 2 - s.re) / 2 ≤ 1 := by linarith
    have : -|m0| ≤ (3 / 2 - s.re) / 2 * (Real.log A + Real.log ‖1 + s‖) := by
      have h1' := mul_le_mul_of_nonneg_left hX he0
      rcases le_total 0 m0 with hm | hm
      · rw [abs_of_nonneg hm]; nlinarith
      · rw [abs_of_nonpos hm]; nlinarith
    simp only [Wt]; linarith
  set c : ℝ := ε * (Real.pi / 4) ^ 2 / 8
  have hc0 : 0 < c := by positivity
  have hGle : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      G s ≤ B' * K0 * Real.exp (κ * |s.im| - c * s.im ^ 2) := by
    intro s h1 h2
    have hfB : ‖f s‖ ≤ B' * Real.exp (κ * |s.im|) :=
      (hB s h1 h2).trans (by gcongr; exact le_max_left _ _)
    have hH := Hb_lower h1 h2
    have hcH : c * s.im ^ 2 ≤ ε * Hb s := by
      have := mul_le_mul_of_nonneg_left hH hε0.le
      calc c * s.im ^ 2 = ε * ((Real.pi / 4 * s.im) ^ 2 / 8) := by simp only [c]; ring
        _ ≤ ε * Hb s := this
    have hexp : Real.exp (-Wt C A s - ε * Hb s) ≤ K0 * Real.exp (-(c * s.im ^ 2)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      exact mul_le_mul (hWlow s h1 h2) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
        (Real.exp_pos _).le
    calc G s = ‖f s‖ * Real.exp (-Wt C A s - ε * Hb s) := rfl
      _ ≤ B' * Real.exp (κ * |s.im|) * (K0 * Real.exp (-(c * s.im ^ 2))) := by gcongr
      _ = B' * K0 * Real.exp (κ * |s.im| - c * s.im ^ 2) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring
  have hBK : 0 < B' * K0 := by positivity
  set M := |Real.log (B' * K0)| + 1
  set T := max (|s₁.im| + 1) ((|κ| + M) / c + 1)
  have hTop : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → T ≤ |s.im| → G s < 1 := by
    intro s h1 h2 hT
    have hT1 : 1 ≤ |s.im| := le_trans (by simp only [T]; exact le_max_of_le_left (by linarith [abs_nonneg s₁.im])) hT
    have hT2 : (|κ| + M) / c + 1 ≤ |s.im| := le_trans (le_max_right _ _) hT
    have hcT : |κ| + M ≤ c * |s.im| := by
      have := (div_le_iff₀ hc0).1 (by linarith : (|κ| + M) / c ≤ |s.im|); linarith
    have hexp : κ * |s.im| - c * s.im ^ 2 ≤ -M := by
      have hsq : s.im ^ 2 = |s.im| * |s.im| := by rw [← sq_abs]; ring
      have hk : κ ≤ |κ| := le_abs_self κ
      have hM0 : 0 < M := by simp only [M]; positivity
      have e1 := mul_le_mul_of_nonneg_left hcT (abs_nonneg s.im)
      have e2 : M ≤ M * |s.im| := le_mul_of_one_le_right hM0.le hT1
      have e3 : κ * |s.im| ≤ |κ| * |s.im| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
      rw [hsq]; nlinarith
    calc G s ≤ B' * K0 * Real.exp (κ * |s.im| - c * s.im ^ 2) := hGle s h1 h2
      _ ≤ B' * K0 * Real.exp (-M) := by gcongr
      _ < 1 := by
        rw [← Real.exp_log hBK, ← Real.exp_add, ← Real.exp_zero]
        apply Real.exp_lt_exp.2
        have := le_abs_self (Real.log (B' * K0)); simp only [M]; linarith
  -- the compact rectangle and a maximum point
  set R : Set ℂ := Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-T) T
  have hRc : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hT₁ : |s₁.im| + 1 ≤ T := le_max_left _ _
  have hs₁R : s₁ ∈ R := ⟨⟨h₁, h₂⟩, abs_le.1 (by linarith)⟩
  have hWcont : ContinuousOn (Wt C A) R := by
    have hn : ∀ s ∈ R, ‖1 + s‖ ≠ 0 := fun s hs => by linarith [hnorm s hs.1.1]
    unfold Wt
    refine continuousOn_const.add (ContinuousOn.mul (by fun_prop) ?_)
    exact continuousOn_const.add (ContinuousOn.log (by fun_prop) hn)
  have hGcont : ContinuousOn G R := by
    have hHc : Continuous Hb := by unfold Hb; fun_prop
    exact (hf.continuous.norm.continuousOn).mul
      (Real.continuous_exp.comp_continuousOn ((hWcont.neg).sub (continuousOn_const.mul hHc.continuousOn)))
  obtain ⟨p, hpR, hpmax⟩ := hRc.exists_isMaxOn ⟨s₁, hs₁R⟩ hGcont
  have hGp : 1 < G p := hG1.trans_le (hpmax hs₁R)
  have hp1 := hpR.1.1
  have hp2 := hpR.1.2
  -- G ≤ 1 on the two vertical edges
  have hedge : ∀ s : ℂ, (s.re = -1 / 2 ∨ s.re = 3 / 2) → G s ≤ 1 := by
    intro s hs
    have h1 : -1 / 2 ≤ s.re := by rcases hs with h | h <;> rw [h] <;> norm_num
    have h2 : s.re ≤ 3 / 2 := by rcases hs with h | h <;> rw [h] <;> norm_num
    have hn : 0 < ‖1 + s‖ := by linarith [hnorm s h1]
    have hfW : ‖f s‖ ≤ Real.exp (Wt C A s) := by
      rw [exp_Wt hC hA hn]
      rcases hs with h | h
      · rw [h, show (3 / 2 - -1 / 2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]; exact hleft s h
      · rw [h, show (3 / 2 - 3 / 2 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero, mul_one]; exact hright s h
    have hH := Hb_nonneg h1 h2
    calc G s = ‖f s‖ * Real.exp (-Wt C A s - ε * Hb s) := rfl
      _ ≤ Real.exp (Wt C A s) * Real.exp (-Wt C A s) := by
          gcongr; nlinarith
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpre1 : -1 / 2 < p.re := lt_of_le_of_ne hp1 (fun h => by linarith [hedge p (Or.inl h.symm)])
  have hpre2 : p.re < 3 / 2 := lt_of_le_of_ne hp2 (fun h => by linarith [hedge p (Or.inr h)])
  have hpim : |p.im| < T := by
    by_contra h; push Not at h; linarith [hTop p hp1 hp2 h]
  have hRnhds : R ∈ 𝓝 p := by
    have hopen : IsOpen (Ioo (-1 / 2 : ℝ) (3 / 2) ×ℂ Ioo (-T) T) := isOpen_Ioo.reProdIm isOpen_Ioo
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hpre1, hpre2⟩, abs_lt.1 hpim⟩) ?_
    rintro z ⟨⟨a1, a2⟩, b1, b2⟩; exact ⟨⟨a1.le, a2.le⟩, b1.le, b2.le⟩
  have hloc : IsLocalMax G p := hpmax.isLocalMax hRnhds
  -- holomorphic normalisation
  set Mf : ℂ → ℂ := fun s => f s * Complex.exp (-(Psi C A s))
  have hPsi : ∀ s : ℂ, 0 < 1 + s.re → DifferentiableAt ℂ (Psi C A) s := fun s hs => by
    have hslit : 1 + s ∈ slitPlane := Or.inl (by simpa using hs)
    unfold Psi
    exact (differentiableAt_const _).add ((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => (3 / 2 - s) / 2) s).mul
      ((differentiableAt_const _).add (((differentiableAt_const _).add differentiableAt_id).clog hslit)))
  have hMdiff : ∀ s : ℂ, 0 < 1 + s.re → DifferentiableAt ℂ Mf s := fun s hs =>
    (hf s).mul ((hPsi s hs).neg.cexp)
  have hUp : 0 < 1 + p.re := by linarith
  have hfp : f p ≠ 0 := fun h => by
    have : G p = 0 := by simp [hG, h]
    linarith
  have hMp : Mf p ≠ 0 := mul_ne_zero hfp (Complex.exp_ne_zero _)
  -- neighbourhood conditions
  have hE1 : ∀ᶠ s in 𝓝 p, 0 < 1 + s.re := by
    have : Continuous fun s : ℂ => 1 + s.re := by fun_prop
    exact this.continuousAt.eventually (lt_mem_nhds hUp)
  have hE2 : ∀ᶠ s in 𝓝 p, Mf s / Mf p ∈ slitPlane := by
    have hc : ContinuousAt (fun s => Mf s / Mf p) p := (hMdiff p hUp).continuousAt.div_const _
    have h1 : Mf p / Mf p ∈ slitPlane := by rw [div_self hMp]; exact Or.inl (by norm_num)
    exact hc.eventually (isOpen_slitPlane.mem_nhds h1)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hE1.and hE2)
  set ℓ : ℂ → ℂ := fun s => Complex.log (Mf s / Mf p)
  have hℓ : DifferentiableOn ℂ ℓ (Metric.ball p r) := fun s hs =>
    (((hMdiff s (hball hs).1).div_const _).clog (hball hs).2).differentiableWithinAt
  -- G = ‖Mf p‖ · exp (Re ℓ + Φ - ε H) on the ball
  have hrep : ∀ s : ℂ, 0 < 1 + s.re → Mf s / Mf p ∈ slitPlane →
      G s = ‖Mf p‖ * Real.exp ((ℓ s).re + Phi s - ε * Hb s) := by
    intro s h1 h2
    have hMs : Mf s ≠ 0 := fun h => by rw [h, zero_div] at h2; exact slitPlane_ne_zero h2 rfl
    have hnM : ‖Mf s‖ = ‖f s‖ * Real.exp (-(Wt C A s + Phi s)) := by
      simp only [Mf, norm_mul, Complex.norm_exp, neg_re, Psi_re C A h1]
    have hl : (ℓ s).re = Real.log ‖Mf s‖ - Real.log ‖Mf p‖ := by
      simp only [ℓ, Complex.log_re, norm_div]
      rw [Real.log_div (norm_ne_zero_iff.2 hMs) (norm_ne_zero_iff.2 hMp)]
    have hMpos : 0 < ‖Mf p‖ := norm_pos_iff.2 hMp
    have hMspos : 0 < ‖Mf s‖ := norm_pos_iff.2 hMs
    rw [show (ℓ s).re + Phi s - ε * Hb s = (ℓ s).re + (Phi s - ε * Hb s) by ring, Real.exp_add, hl,
      Real.exp_sub, Real.exp_log hMspos, Real.exp_log hMpos, hnM]
    simp only [hG]
    field_simp
    rw [mul_assoc, ← Real.exp_add]
    congr 2; ring
  -- local maximum of Re ℓ + Φ - ε H at p
  have hgmax : IsLocalMax (fun s => (ℓ s).re + Phi s - ε * Hb s) p := by
    filter_upwards [hloc, hE1, hE2] with s hs h1 h2
    have e1 := hrep s h1 h2
    have e2 := hrep p hUp (by rw [div_self hMp]; exact Or.inl (by norm_num))
    have hMpos : 0 < ‖Mf p‖ := norm_pos_iff.2 hMp
    have : ‖Mf p‖ * Real.exp ((ℓ s).re + Phi s - ε * Hb s) ≤
        ‖Mf p‖ * Real.exp ((ℓ p).re + Phi p - ε * Hb p) := by rw [← e1, ← e2]; exact hs
    exact Real.exp_le_exp.1 (le_of_mul_le_mul_left this hMpos)
  exact no_local_max hr hℓ hUp hgmax

end QRHLittlewood


open Complex Set Real

set_option autoImplicit false

namespace QRHLittlewood

/-- Rademacher's convexity bound for primitive Dirichlet L-functions, exponent 1/2 (exact constant). -/
theorem rademacher_convexity (q : ℕ) [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (s : ℂ) (hs1 : -1 / 2 ≤ s.re) (hs2 : s.re ≤ 3 / 2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤
      (riemannZeta (3 / 2)).re * ((q : ℝ) * ‖1 + s‖ / (2 * π)) ^ ((3 / 2 - s.re) / 2) := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl; rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hprim; omega
  have hq2 : 2 ≤ q := by omega
  set C : ℝ := (riemannZeta (3 / 2)).re
  have hC : 0 < C := by
    have := riemannZeta_re_pos_of_one_lt (x := 3 / 2) (by norm_num)
    simpa [C] using this
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set A : ℝ := (q : ℝ) / (2 * π)
  have hA : 0 < A := by positivity
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ1
  have hleft : ∀ z : ℂ, z.re = -1 / 2 → ‖DirichletCharacter.LFunction χ z‖ ≤ C * (A * ‖1 + z‖) := by
    intro z hz
    have := norm_LFunction_left_edge' hprim hz
    convert this using 2
    simp only [A]; ring
  have hright : ∀ z : ℂ, z.re = 3 / 2 → ‖DirichletCharacter.LFunction χ z‖ ≤ C := by
    intro z hz
    have := norm_LFunction_le_zeta χ (s := z) (by rw [hz]; norm_num)
    rw [hz] at this
    simpa [C] using this
  have hgrowth : ∃ B κ : ℝ, ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 →
      ‖DirichletCharacter.LFunction χ z‖ ≤ B * Real.exp (κ * |z.im|) := by
    obtain ⟨Cg, hCg⟩ := LFunction_growth hq2 hχ1
    obtain ⟨M, hM⟩ := (isCompact_Icc.reProdIm (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      (hdiff.continuous.continuousOn (s := Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-1) 1))
    refine ⟨max Cg M, π / 2, fun z h1 h2 => ?_⟩
    rcases le_or_gt |z.im| 1 with ht | ht
    · have := hM z ⟨⟨h1, h2⟩, abs_le.1 ht⟩
      have hM0 : 0 ≤ M := (norm_nonneg _).trans this
      calc _ ≤ M := this
        _ ≤ max Cg M * 1 := by rw [mul_one]; exact le_max_right _ _
        _ ≤ max Cg M * Real.exp (π / 2 * |z.im|) := by
            exact mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) (le_max_of_le_right hM0)
    · have h := hCg z h1 h2 ht.le
      have hC0 : 0 ≤ Cg := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (Real.exp_pos _)
      calc _ ≤ Cg * Real.exp (π * |z.im| / 2) := h
        _ ≤ max Cg M * Real.exp (π / 2 * |z.im|) := by
            rw [show π * |z.im| / 2 = π / 2 * |z.im| by ring]
            gcongr; exact le_max_left _ _
  have := pl_exact hdiff hC hA hleft hright hgrowth s hs1 hs2
  convert this using 3
  simp only [A]; ring

end QRHLittlewood





theorem solution {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C A : ℝ} (hC : 0 < C) (hA : 0 < A) (hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖f s‖ ≤ C * (A * ‖1 + s‖)) (hright : ∀ s : ℂ, s.re = 3 / 2 → ‖f s‖ ≤ C) (hgrowth : ∃ B κ : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 → ‖f s‖ ≤ B * Real.exp (κ * |s.im|)) (s₁ : ℂ) (h₁ : -1 / 2 ≤ s₁.re) (h₂ : s₁.re ≤ 3 / 2) : ‖f s₁‖ ≤ C * (A * ‖1 + s₁‖) ^ ((3 / 2 - s₁.re) / 2) :=
  QRHLittlewood.pl_exact hf hC hA hleft hright hgrowth s₁ h₁ h₂
