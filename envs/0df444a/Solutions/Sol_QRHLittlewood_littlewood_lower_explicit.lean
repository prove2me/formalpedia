-- Prove2me | solution 1 for QRHLittlewood.littlewood_lower_explicit
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T18:06:42.485384+00:00
-- url     : https://prove2.me/submissions/d4caf3d0-5896-4678-86c3-65b362937d32

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Separation.CompletelyRegular

/- Explicit Littlewood bound L(1,χ) ≥ 0.0617 / log log q for primitive real Dirichlet characters modulo
q ≥ 10^100 under the zero-free half-plane Re s > 7/8. Route: a logarithm F of L(2 - z) on |z| < 9/8 with
|L| ≤ 12 q^(1/8) on |s - 2| ≤ 9/8 and Carathéodory's coefficient inequality for the Taylor tail; the partial
sum of F at z = 1 is a sum over prime powers with truncated-exponential weights, and pairing the odd and
even powers of each prime (χ(p) ∈ {-1, 0, 1}) gives -P_N F(1) ≤ P_N log ζ(2 - z)(1) - log ζ(2) + (4/5)^(N+1) log 3;
the sharp truncation of log ζ(2 - z), a joint rounding of N = ⌈x⌉ and rational bounds close the constant. -/
section

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



end


section

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
end


section

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
end


section

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
end


section

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
end


section

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


end


section

open Real Finset Filter Topology

set_option autoImplicit false

namespace QRHLittlewood

/-- The real zeta function as a series. -/
noncomputable def zetaR (x : ℝ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ x

lemma zetaR_upper {x : ℝ} (hx : 1 < x) : zetaR x ≤ 1 + 1 / (x - 1) := by
  have h := ZetaAsymptotics.zeta_limit_aux1 hx
  have hT : 0 ≤ ZetaAsymptotics.termTSum x :=
    tsum_nonneg fun n => ZetaAsymptotics.term_nonneg (n + 1) x
  have : x * ZetaAsymptotics.termTSum x ≥ 0 := mul_nonneg (by linarith) hT
  unfold zetaR
  push_cast at h ⊢
  linarith

lemma zetaR_summable {x : ℝ} (hx : 1 < x) : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ x := by
  exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_rpow.mpr hx)

lemma zetaR_lower {x : ℝ} (hx : 1 < x) : 1 / (x - 1) ≤ zetaR x := by
  have hs := zetaR_summable hx
  -- partial integral bounds
  have hpart : ∀ N : ℕ, (1 - (1 + (N : ℝ)) ^ (1 - x)) / (x - 1) ≤ zetaR x := by
    intro N
    have hanti : AntitoneOn (fun t : ℝ => t ^ (-x)) (Set.Icc 1 (1 + (N : ℝ))) := by
      intro a ha b hb hab
      exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
    have hint := hanti.integral_le_sum
    have hval : ∫ t in (1 : ℝ)..1 + N, t ^ (-x) = (1 - (1 + (N : ℝ)) ^ (1 - x)) / (x - 1) := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (N : ℝ)) := by
        rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]
      rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
      rw [Real.one_rpow, show -x + 1 = -(x - 1) by ring, div_neg, show -(x - 1) = 1 - x by ring]
      ring
    rw [hval] at hint
    refine hint.trans ?_
    have : ∑ i ∈ range N, (1 + (i : ℝ)) ^ (-x) = ∑ i ∈ range N, 1 / ((i : ℝ) + 1) ^ x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_neg (by positivity), one_div, add_comm]
    rw [this]
    exact hs.sum_le_tsum (range N) (fun i _ => by positivity)
  have hlim : Tendsto (fun N : ℕ => (1 - (1 + (N : ℝ)) ^ (1 - x)) / (x - 1)) atTop (𝓝 (1 / (x - 1))) := by
    have h0 : Tendsto (fun N : ℕ => (1 + (N : ℝ)) ^ (1 - x)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < x - 1)).comp
        (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
      simpa [Function.comp_def, show -(x - 1) = 1 - x by ring] using this
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).div_const (x - 1)
    simpa using this
  exact le_of_tendsto' hlim hpart


lemma zetaR_pos {x : ℝ} (hx : 1 < x) : 0 < zetaR x :=
  lt_of_lt_of_le (by have : 0 < x - 1 := by linarith
                     positivity) (zetaR_lower hx)

/-- **Positive-series truncation.** If `b ≥ 0` and `∑ bₙ rⁿ = log ζ(2 - r)` on `[0, 1)`, then
`∑_{n ≤ N} bₙ ≤ log N + 4 log 3` for every `N ≥ 1`. -/
theorem truncation (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hsum : ∀ r : ℝ, 0 ≤ r → r < 1 → HasSum (fun n => b n * r ^ n) (Real.log (zetaR (2 - r))))
    (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ range (N + 1), b n ≤ Real.log N + 4 * Real.log 3 := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set r : ℝ := N / (N + 1) with hrdef
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hrdef, div_lt_one (by positivity)]; linarith
  -- r^N ≥ 1/3
  have hrN : 1 / 3 ≤ r ^ N := by
    have hpos : (0 : ℝ) < 1 + 1 / N := by positivity
    have hr : r = (1 + 1 / (N : ℝ))⁻¹ := by rw [hrdef]; field_simp
    have hb1 : (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp 1 := by
      calc (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp (1 / N) ^ N := by
            gcongr; linarith [Real.add_one_le_exp (1 / (N : ℝ))]
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    rw [hr, inv_pow]
    rw [one_div, inv_le_inv₀ (by norm_num) (by positivity)]
    linarith
  -- termwise bound
  have hterm : ∀ n ∈ range (N + 1), b n ≤ b n * r ^ n + 3 * (b n * (r ^ n - (r ^ 2) ^ n)) := by
    intro n hn
    have hn' : n ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hn)
    have h1 : r ^ N ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le hn'
    have h2 : r ^ n ≤ 1 := pow_le_one₀ hr0 hr1.le
    have h3 : (r ^ 2) ^ n = r ^ n * r ^ n := by rw [← pow_mul, mul_comm, pow_mul, sq]
    rw [h3]
    have key : 1 ≤ r ^ n + 3 * (r ^ n - r ^ n * r ^ n) := by nlinarith
    nlinarith [hb n]
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hr21 : r ^ 2 < 1 := by nlinarith
  have hS1 := hsum r hr0 hr1
  have hS2 := hsum (r ^ 2) hr2 hr21
  have hdiff : HasSum (fun n => b n * (r ^ n - (r ^ 2) ^ n))
      (Real.log (zetaR (2 - r)) - Real.log (zetaR (2 - r ^ 2))) := by
    have := hS1.sub hS2; simpa [mul_sub] using this
  have hnn1 : ∀ n, 0 ≤ b n * r ^ n := fun n => mul_nonneg (hb n) (pow_nonneg hr0 n)
  have hnn2 : ∀ n, 0 ≤ b n * (r ^ n - (r ^ 2) ^ n) := fun n => by
    apply mul_nonneg (hb n)
    rw [← pow_mul, sub_nonneg]
    exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hP1 : ∑ n ∈ range (N + 1), b n * r ^ n ≤ Real.log (zetaR (2 - r)) :=
    sum_le_hasSum _ (fun n _ => hnn1 n) hS1
  have hP2 : ∑ n ∈ range (N + 1), b n * (r ^ n - (r ^ 2) ^ n) ≤
      Real.log (zetaR (2 - r)) - Real.log (zetaR (2 - r ^ 2)) :=
    sum_le_hasSum _ (fun n _ => hnn2 n) hdiff
  -- the two zeta estimates
  have hx1 : 1 < 2 - r := by linarith
  have hx2 : 1 < 2 - r ^ 2 := by linarith
  have hz1 : zetaR (2 - r) ≤ N + 2 := by
    have := zetaR_upper hx1
    have e : 1 + 1 / (2 - r - 1) = N + 2 := by rw [hrdef]; field_simp; ring
    linarith
  have hf1 : Real.log (zetaR (2 - r)) ≤ Real.log (N + 2) :=
    Real.log_le_log (zetaR_pos hx1) hz1
  have hf2 : Real.log (zetaR (2 - r)) - Real.log (zetaR (2 - r ^ 2)) ≤ Real.log 3 := by
    rw [← Real.log_div (zetaR_pos hx1).ne' (zetaR_pos hx2).ne']
    apply Real.log_le_log (div_pos (zetaR_pos hx1) (zetaR_pos hx2))
    have hlow := zetaR_lower hx2
    have hpos2 : 0 < 2 - r ^ 2 - 1 := by linarith
    rw [div_le_iff₀ (zetaR_pos hx2)]
    calc zetaR (2 - r) ≤ N + 2 := hz1
      _ ≤ 3 * (1 / (2 - r ^ 2 - 1)) := by
          rw [hrdef, show (2 : ℝ) - (N / (N + 1)) ^ 2 - 1 = (2 * N + 1) / (N + 1) ^ 2 by field_simp; ring]
          rw [one_div_div, ← mul_div_assoc, le_div_iff₀ (by positivity)]
          nlinarith
      _ ≤ 3 * zetaR (2 - r ^ 2) := by gcongr
  have hlog3 : Real.log (N + 2) ≤ Real.log N + Real.log 3 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    exact Real.log_le_log (by positivity) (by linarith)
  calc ∑ n ∈ range (N + 1), b n
      ≤ ∑ n ∈ range (N + 1), (b n * r ^ n + 3 * (b n * (r ^ n - (r ^ 2) ^ n))) := sum_le_sum hterm
    _ = ∑ n ∈ range (N + 1), b n * r ^ n + 3 * ∑ n ∈ range (N + 1), b n * (r ^ n - (r ^ 2) ^ n) := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ Real.log N + 4 * Real.log 3 := by linarith

end QRHLittlewood
end


section

open Complex Metric Set LSeries

set_option autoImplicit false

namespace QRHLittlewood

/-- A nonvanishing holomorphic function on a disk has a holomorphic logarithm with prescribed value at the
centre, whose derivative is `f' / f`. -/
theorem exists_log_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (ball c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0) (w₀ : ℂ) (hw₀ : exp w₀ = f c) (hR : 0 < R) :
    ∃ F : ℂ → ℂ, F c = w₀ ∧ (∀ z ∈ ball c R, HasDerivAt F (deriv f z / f z) z) ∧
      ∀ z ∈ ball c R, exp (F z) = f z := by
  have hopen : IsOpen (ball c R) := isOpen_ball
  have hg : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c R) :=
    (hf.deriv hopen).div hf hne
  obtain ⟨F, hFc, hF⟩ := (hg.isExactOn_ball).with_val_at c w₀
  refine ⟨F, hFc, hF, ?_⟩
  -- h = exp F / f has zero derivative on the ball
  set h : ℂ → ℂ := fun z => exp (F z) / f z
  have hderiv : ∀ z ∈ ball c R, HasDerivAt h 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z := (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have := ((hF z hz).cexp).div hfz (hne z hz)
    refine this.congr_deriv ?_
    rw [mul_assoc, div_mul_cancel₀ _ (hne z hz), sub_self, zero_div]
  have hconst : ∀ z ∈ ball c R, h z = h c := by
    intro z hz
    exact hopen.is_const_of_deriv_eq_zero (isPreconnected_ball) (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hderiv w hw).deriv) hz (mem_ball_self hR)
  intro z hz
  have h1 := hconst z hz
  have hc1 : h c = 1 := by simp only [h, hFc, hw₀]; exact div_self (hne c (mem_ball_self hR))
  rw [hc1] at h1
  simp only [h] at h1
  exact (div_eq_one_iff_eq (hne z hz)).1 h1


lemma logMul_iterate_apply (f : ℕ → ℂ) (n m : ℕ) :
    (LSeries.logMul^[n] f) m = (Complex.log m) ^ n * f m := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ]; ring

/-- Coefficient domination: `‖L(logⁿ · χΛ, s)‖ ≤ L(logⁿ · Λ, Re s)` (a nonnegative real) for `Re s > 1`. -/
lemma abscissa_vonMangoldt_le_one :
    abscissaOfAbsConv (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (x := 1)
    (fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
  exact_mod_cast this

lemma abscissa_twist_le_one {N : ℕ} (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) (x := 1)
    (fun y hy => DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by simpa using hy))
  exact_mod_cast this

/-- The terms of `L(logⁿ · Λ, σ)` at real `σ` are nonnegative reals. -/
lemma term_logMul_vonMangoldt_real (n : ℕ) (σ : ℝ) (m : ℕ) :
    term (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) (σ : ℂ) m =
      ((if m = 0 then 0 else Real.log m ^ n * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [term_of_ne_zero hm, logMul_iterate_apply, if_neg hm]
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [show (Complex.log (m : ℂ)) = ((Real.log m : ℝ) : ℂ) by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp, Complex.ofReal_log hm']]
    rw [show ((m : ℂ) ^ (σ : ℂ)) = (((m : ℝ) ^ σ : ℝ) : ℂ) by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp, Complex.ofReal_cpow hm']]
    push_cast; ring

lemma term_logMul_vonMangoldt_nonneg (n : ℕ) (σ : ℝ) (m : ℕ) :
    0 ≤ (if m = 0 then 0 else Real.log m ^ n * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ : ℝ) := by
  split_ifs with hm
  · rfl
  · have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hm
    have := Real.log_nonneg this
    have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    positivity

/-- Coefficient domination: `‖L(logⁿ · χΛ, s)‖ ≤ L(logⁿ · Λ, Re s)` (a nonnegative real) for `Re s > 1`. -/
theorem norm_LSeries_logMul_twist_le {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (LSeries.logMul^[n] (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))) s‖ ≤
      (LSeries (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) (s.re : ℂ)).re := by
  set g : ℕ → ℂ := LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
  set f : ℕ → ℂ := LSeries.logMul^[n] (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))
  have hgsum : LSeriesSummable g (s.re : ℂ) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissa_vonMangoldt_le_one (by simpa using (EReal.coe_lt_coe_iff.2 hs))
  have hle : ∀ m, ‖term f s m‖ ≤ ‖term g (s.re : ℂ) m‖ := fun m => by
    rw [norm_term_eq, norm_term_eq]
    split_ifs with hm
    · rfl
    · simp only [f, g, logMul_iterate_apply, norm_mul, ofReal_re]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hs1 : Summable fun m => ‖term g (s.re : ℂ) m‖ := hgsum.norm
  calc ‖LSeries f s‖ ≤ ∑' m, ‖term f s m‖ :=
        norm_tsum_le_tsum_norm (hs1.of_nonneg_of_le (fun _ => norm_nonneg _) hle)
    _ ≤ ∑' m, ‖term g (s.re : ℂ) m‖ :=
        Summable.tsum_le_tsum hle (hs1.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hs1
    _ = (LSeries g (s.re : ℂ)).re := by
        rw [LSeries, re_tsum hgsum]
        congr 1; funext m
        rw [term_logMul_vonMangoldt_real, Complex.norm_real, ofReal_re,
          Real.norm_of_nonneg (term_logMul_vonMangoldt_nonneg n s.re m)]


/-- If `F` is a logarithm of `z ↦ Lf (2 - z)` near `0`, where `Lf` agrees with `L(χ, ·)` on `Re s > 1`,
then `F^{(n+1)}(0) = L(logⁿ · χΛ, 2)`. -/
theorem iteratedDeriv_succ_log {N : ℕ} (χ : DirichletCharacter ℂ N) {Lf F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hLf : EqOn Lf (LSeries (fun m => χ m)) {s | 1 < s.re})
    (hF : ∀ z ∈ ball (0 : ℂ) R, HasDerivAt F (deriv (fun w => Lf (2 - w)) z / Lf (2 - z)) z)
    (n : ℕ) :
    iteratedDeriv (n + 1) F 0 =
      LSeries (LSeries.logMul^[n] (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))) 2 := by
  set r := min R 1
  have hr : 0 < r := lt_min hR one_pos
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  -- on ball 0 r, deriv F = L(χΛ)(2 - z)
  have hderiv : deriv F =ᶠ[nhds 0] fun z => LSeries (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) (2 - z) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball (min_le_left _ _) hz
    have hz1 : 1 < (2 - z).re := by
      have h' : ‖z‖ < 1 := by simpa using lt_of_lt_of_le hz (min_le_right R 1)
      simp only [sub_re]; norm_num
      linarith [abs_le.1 (Complex.abs_re_le_norm z)]
    rw [(hF z hzR).deriv]
    -- local equality Lf = L(χ) near 2 - z
    have hloc : (fun w => Lf (2 - w)) =ᶠ[nhds z] fun w => LSeries (fun m => χ m) (2 - w) := by
      have hc : ContinuousAt (fun w : ℂ => 2 - w) z := by fun_prop
      filter_upwards [hc.preimage_mem_nhds (hopen.mem_nhds hz1)] with w hw
      exact hLf hw
    rw [hloc.deriv_eq, hLf hz1]
    rw [deriv_comp_const_sub, neg_div, ← neg_div, ← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz1]
    rfl
  rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq, iteratedDeriv_comp_const_sub]
  beta_reduce
  rw [sub_zero, LSeries_iteratedDeriv]
  · rw [smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
  · refine lt_of_le_of_lt (abscissa_twist_le_one χ) ?_
    norm_num
    exact_mod_cast (show (1 : ℝ) < 2 by norm_num)


/-- A function with real value at `0` and real derivative along a real interval stays real there. -/
theorem im_eq_zero_of_real_deriv {F : ℂ → ℂ} {R : ℝ}
    (hF : ∀ t : ℝ, |t| < R → HasDerivAt F (deriv F t) (t : ℂ))
    (hreal : ∀ t : ℝ, |t| < R → (deriv F t).im = 0) (h0 : (F 0).im = 0) :
    ∀ t : ℝ, |t| < R → (F t).im = 0 := by
  intro t ht
  have hR : 0 < R := lt_of_le_of_lt (abs_nonneg t) ht
  -- φ(x) = Im F(x) = Re(-I · F x) has derivative Im F'(x) = 0
  have hd : ∀ x ∈ Ioo (-R) R, HasDerivAt (fun x : ℝ => (F x).im) 0 x := by
    intro x hx
    have hx' : |x| < R := abs_lt.2 hx
    have h1 := ((hF x hx').const_mul (-I)).real_of_complex
    have e : (-I * deriv F x).re = (deriv F x).im := by simp
    rw [e, hreal x hx'] at h1
    convert h1 using 1
    funext y; simp
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) (show t ∈ Ioo (-R) R from abs_lt.1 ht)
    (show (0 : ℝ) ∈ Ioo (-R) R from ⟨by linarith, hR⟩)
  simpa [h0] using hconst


/-- An L-series with real coefficients is real at real arguments. -/
lemma LSeries_im_eq_zero {f : ℕ → ℂ} (hf : ∀ m, (f m).im = 0) (x : ℝ) : (LSeries f (x : ℂ)).im = 0 := by
  have hterm : ∀ m, (term f (x : ℂ) m).im = 0 := fun m => by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [term_of_ne_zero hm]
      have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      rw [show ((m : ℂ) ^ (x : ℂ)) = (((m : ℝ) ^ x : ℝ) : ℂ) by
        rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp, Complex.ofReal_cpow hm']]
      rw [show f m = ((f m).re : ℂ) from Complex.ext (by simp) (by simp [hf m])]
      rw [← Complex.ofReal_div]; simp
  by_cases hs : Summable (term f (x : ℂ))
  · rw [LSeries, Complex.im_tsum hs]; simp [hterm]
  · rw [LSeries, tsum_eq_zero_of_not_summable hs]; simp


/-- Logarithmic derivative of `z ↦ L(χ, 2 - z)` on `Re (2 - z) > 1`. -/
lemma logderiv_formula {N : ℕ} (χ : DirichletCharacter ℂ N) {Lf : ℂ → ℂ}
    (hLf : EqOn Lf (LSeries (fun m => χ m)) {s | 1 < s.re}) {z : ℂ} (hz1 : 1 < (2 - z).re) :
    deriv (fun w => Lf (2 - w)) z / Lf (2 - z) =
      LSeries (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) (2 - z) := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hloc : (fun w => Lf (2 - w)) =ᶠ[nhds z] fun w => LSeries (fun m => χ m) (2 - w) := by
    have hc : ContinuousAt (fun w : ℂ => 2 - w) z := by fun_prop
    filter_upwards [hc.preimage_mem_nhds (hopen.mem_nhds hz1)] with w hw
    exact hLf hw
  rw [hloc.deriv_eq, hLf hz1, deriv_comp_const_sub, neg_div, ← neg_div,
    ← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz1]
  rfl

lemma re_LSeries_logMul_vonMangoldt_nonneg (n : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (LSeries (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) (σ : ℂ)).re := by
  set g : ℕ → ℂ := LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
  have hgsum : LSeriesSummable g (σ : ℂ) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissa_vonMangoldt_le_one (by simpa using (EReal.coe_lt_coe_iff.2 hσ))
  rw [LSeries, re_tsum hgsum]
  refine tsum_nonneg fun m => ?_
  rw [term_logMul_vonMangoldt_real, ofReal_re]
  exact term_logMul_vonMangoldt_nonneg n σ m


lemma chi1_apply (m : ℕ) : (1 : DirichletCharacter ℂ 1) m = 1 := by
  rw [show (m : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]

lemma LSeries_chi1_eq_zetaR {x : ℝ} (hx : 1 < x) :
    LSeries (fun m => (1 : DirichletCharacter ℂ 1) m) (x : ℂ) = (zetaR x : ℂ) := by
  have hx' : 1 < ((x : ℂ)).re := by simpa using hx
  rw [show (fun m : ℕ => (1 : DirichletCharacter ℂ 1) m) = 1 from funext fun m => chi1_apply m,
    LSeries_one_eq_riemannZeta hx', zeta_eq_tsum_one_div_nat_add_one_cpow hx', zetaR, Complex.ofReal_tsum]
  congr 1; funext n
  have h : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow h]
  push_cast; ring


lemma logMul_vonMangoldt_im (n m : ℕ) :
    ((LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) m).im = 0 := by
  have hl : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
  rw [logMul_iterate_apply, hl, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

/-- The generating series of `log ζ(2 - r)`: nonnegative coefficients `bₙ` with
`b₀ = log ζ(2)`, `b_{n+1} = L(logⁿ · Λ, 2)/(n+1)!` and `∑ bₙ rⁿ = log ζ(2 - r)` on `[0, 1)`. -/
theorem log_zeta_series : ∃ b : ℕ → ℝ, (∀ n, 0 ≤ b n) ∧ b 0 = Real.log (zetaR 2) ∧
    (∀ n, b (n + 1) = (LSeries (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) 2).re /
      ((n + 1).factorial : ℝ)) ∧
    ∀ r : ℝ, 0 ≤ r → r < 1 → HasSum (fun n => b n * r ^ n) (Real.log (zetaR (2 - r))) := by
  set χ₁ : DirichletCharacter ℂ 1 := 1
  set Lf : ℂ → ℂ := LSeries (fun m => χ₁ m)
  have hLf : EqOn Lf (LSeries (fun m => χ₁ m)) {s | 1 < s.re} := fun _ _ => rfl
  set f : ℂ → ℂ := fun z => Lf (2 - z)
  have hball : ∀ z ∈ ball (0 : ℂ) 1, 1 < (2 - z).re := fun z hz => by
    have h' : ‖z‖ < 1 := by simpa using hz
    simp only [sub_re]; norm_num; linarith [abs_le.1 (Complex.abs_re_le_norm z)]
  have hab : abscissaOfAbsConv (fun m => χ₁ m) ≤ 1 := by
    have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := fun m => χ₁ m) (x := 1)
      (fun y hy => (DirichletCharacter.LSeriesSummable_iff one_ne_zero χ₁).2 (by simpa using hy))
    exact_mod_cast this
  have hfdiff : DifferentiableOn ℂ f (ball 0 1) := by
    intro z hz
    have hz1 := hball z hz
    have hd : DifferentiableAt ℂ Lf (2 - z) :=
      (LSeries_differentiableOn _).differentiableAt
        ((isOpen_re_gt_EReal _).mem_nhds (lt_of_le_of_lt hab (by exact_mod_cast hz1)))
    exact (hd.comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 2 - w) z)).differentiableWithinAt
  have hfne : ∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0 := fun z hz =>
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ₁ (hball z hz)
  have hz2 : LSeries (fun m => χ₁ m) ((2 : ℝ) : ℂ) = (zetaR 2 : ℂ) := LSeries_chi1_eq_zetaR (by norm_num)
  have hw0 : exp ((Real.log (zetaR 2) : ℝ) : ℂ) = f 0 := by
    rw [← Complex.ofReal_exp, Real.exp_log (zetaR_pos (by norm_num))]
    simp only [f, Lf, sub_zero]; rw [← hz2]; norm_num
  obtain ⟨G, hG0, hGd, hGexp⟩ := exists_log_on_ball hfdiff hfne _ hw0 one_pos
  have hGdiff : DifferentiableOn ℂ G (ball 0 1) := fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt
  have hcoef : ∀ n, iteratedDeriv (n + 1) G 0 =
      LSeries (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) 2 := by
    intro n
    rw [iteratedDeriv_succ_log χ₁ one_pos hLf hGd n]
    congr 2; funext m; rw [chi1_apply, one_mul]
  have hreal : ∀ n, (iteratedDeriv n G 0).im = 0 := by
    intro n; cases n with
    | zero => simp [hG0]
    | succ n => rw [hcoef, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
                exact LSeries_im_eq_zero (logMul_vonMangoldt_im n) 2
  set b : ℕ → ℝ := fun n => (iteratedDeriv n G 0).re / (n.factorial : ℝ)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro n; cases n with
    | zero =>
      simp only [b, iteratedDeriv_zero, hG0, ofReal_re, Nat.factorial_zero, Nat.cast_one, div_one]
      exact Real.log_nonneg (by have := zetaR_lower (show (1 : ℝ) < 2 by norm_num); norm_num at this; linarith)
    | succ n =>
      simp only [b, hcoef]
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
      exact div_nonneg (re_LSeries_logMul_vonMangoldt_nonneg n (by norm_num)) (by positivity)
  · simp [b, hG0]
  · intro n; simp only [b, hcoef]
  · intro r hr0 hr1
    have hrball : (r : ℂ) ∈ ball (0 : ℂ) 1 := by simpa [abs_of_nonneg hr0] using hr1
    have hT := (Complex.hasSum_taylorSeries_on_ball hGdiff hrball).mapL Complex.reCLM
    -- G r is real and equals log ζ(2 - r)
    have hGr_im : (G r).im = 0 := by
      refine im_eq_zero_of_real_deriv (R := 1) (fun t ht => ?_) (fun t ht => ?_) (by simp [hG0]) r
        (by rwa [abs_of_nonneg hr0])
      · have htb : (t : ℂ) ∈ ball (0 : ℂ) 1 := by simpa using ht
        exact (hGd t htb).differentiableAt.hasDerivAt
      · have htb : (t : ℂ) ∈ ball (0 : ℂ) 1 := by simpa using ht
        rw [(hGd t htb).deriv, logderiv_formula χ₁ hLf (hball t htb),
          show (2 : ℂ) - (t : ℂ) = ((2 - t : ℝ) : ℂ) by push_cast; ring]
        exact LSeries_im_eq_zero (fun m => by rw [chi1_apply, one_mul]; exact Complex.ofReal_im _) _
    have hGr : (G r).re = Real.log (zetaR (2 - r)) := by
      have he := hGexp r hrball
      have hval : f r = (zetaR (2 - r) : ℂ) := by
        simp only [f, Lf]; rw [show (2 : ℂ) - (r : ℂ) = ((2 - r : ℝ) : ℂ) by push_cast; ring]
        exact LSeries_chi1_eq_zetaR (by linarith)
      rw [hval, show G r = ((G r).re : ℂ) from Complex.ext (by simp) (by simp [hGr_im]),
        ← Complex.ofReal_exp] at he
      have := Complex.ofReal_injective he
      rw [← this, Real.log_exp]
    rw [← hGr]
    convert hT using 1
    funext n
    simp only [b, Complex.reCLM_apply, sub_zero, smul_eq_mul]
    rw [show (iteratedDeriv n G 0) = ((iteratedDeriv n G 0).re : ℂ) from
      Complex.ext (by simp) (by simp [hreal n])]
    rw [show ((r : ℂ) ^ n) = ((r ^ n : ℝ) : ℂ) by push_cast; ring,
      show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; ring]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    simp only [Complex.ofReal_re]
    try ring
    all_goals first | rfl | simp

end QRHLittlewood
end


section

open Complex Metric Set LSeries

set_option autoImplicit false

namespace QRHLittlewood

lemma zetaR_two : zetaR 2 = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow two_ne_zero, div_zero,
    sub_zero] at h
  rw [zetaR, ← h.tsum_eq]
  congr 1; funext n
  push_cast
  rw [Real.rpow_two]

lemma zetaR_two_lt : zetaR 2 < 5 / 3 := by
  rw [zetaR_two]
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- `|L(2, χ) - 1| ≤ ζ(2) - 1`. -/
lemma norm_LSeries_two_sub_one_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ‖LSeries (fun m => χ m) 2 - 1‖ ≤ zetaR 2 - 1 := by
  have hs1 : 1 < (2 : ℂ).re := by norm_num
  have hsum : LSeriesSummable (fun m => χ m) 2 :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).2 hs1
  have hsum2 : Summable fun m => term (fun m => χ m) 2 (m + 2) := by
    have := (summable_nat_add_iff 2).2 hsum; exact this
  have hsplit : LSeries (fun m => χ m) 2 - 1 = ∑' m, term (fun m => χ m) 2 (m + 2) := by
    rw [LSeries, hsum.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hsum).tsum_eq_zero_add]
    simp [term_of_ne_zero]
    congr 1; funext b; ring_nf
  have hzsum := zetaR_summable (show (1 : ℝ) < 2 by norm_num)
  have hz : zetaR 2 - 1 = ∑' m : ℕ, 1 / ((m : ℝ) + 2) ^ (2 : ℝ) := by
    rw [zetaR, hzsum.tsum_eq_zero_add]; push_cast; simp only [zero_add, Real.one_rpow, div_one]
    ring_nf
  have hb : ∀ m : ℕ, ‖term (fun m => χ m) 2 (m + 2)‖ ≤ 1 / ((m : ℝ) + 2) ^ (2 : ℝ) := fun m => by
    rw [norm_term_eq, if_neg (by omega)]
    simp only [show ((2 : ℂ)).re = 2 by norm_num]
    push_cast
    gcongr
    exact DirichletCharacter.norm_le_one χ _
  have hbs : Summable fun m : ℕ => 1 / ((m : ℝ) + 2) ^ (2 : ℝ) := by
    have := (summable_nat_add_iff 1).2 hzsum
    refine this.congr fun m => ?_
    push_cast; ring_nf
  rw [hsplit, hz]
  exact (norm_tsum_le_tsum_norm (hbs.of_nonneg_of_le (fun _ => norm_nonneg _) hb)).trans
    (Summable.tsum_le_tsum hb (hbs.of_nonneg_of_le (fun _ => norm_nonneg _) hb) hbs)


lemma riemannZeta_re_eq_zetaR {x : ℝ} (hx : 1 < x) : (riemannZeta (x : ℂ)).re = zetaR x := by
  have hx' : 1 < ((x : ℂ)).re := by simpa using hx
  rw [← LSeries_one_eq_riemannZeta hx', show (1 : ℕ → ℂ) = fun m : ℕ => (1 : DirichletCharacter ℂ 1) m from
    funext fun m => (chi1_apply m).symm, LSeries_chi1_eq_zetaR hx, ofReal_re]

/-- On the disk `|s - 2| < 35/32`, `‖L(s, χ)‖ ≤ 4 q` for primitive `χ` modulo `q ≥ 3`. -/
lemma norm_LFunction_disk_le {q : ℕ} [NeZero q] (hq : 3 ≤ q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) {s : ℂ} (hs : ‖s - 2‖ < 35 / 32) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 4 * q := by
  have hre : |s.re - 2| < 35 / 32 := by
    have := Complex.abs_re_le_norm (s - 2); simp at this; linarith
  have hqr : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hz32 : (riemannZeta (3 / 2 : ℂ)).re ≤ 3 := by
    have := riemannZeta_re_eq_zetaR (x := 3 / 2) (by norm_num)
    push_cast at this; rw [this]
    have := zetaR_upper (x := 3 / 2) (by norm_num); norm_num at this ⊢; linarith
  rcases le_or_gt (3 / 2) s.re with h | h
  · have h1 := norm_LFunction_le_zeta χ (s := s) (by linarith)
    rw [riemannZeta_re_eq_zetaR (by linarith)] at h1
    have h2 := zetaR_upper (x := s.re) (by linarith)
    have : 1 / (s.re - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  · have hR := rademacher_convexity q hq χ hprim s (by linarith [abs_lt.1 hre]) h.le
    have hn : ‖1 + s‖ < 5 := by
      calc ‖1 + s‖ = ‖3 + (s - 2)‖ := by ring_nf
        _ ≤ 3 + ‖s - 2‖ := by
            refine (norm_add_le _ _).trans ?_; simp
        _ < 5 := by linarith
    have hx : (q : ℝ) * ‖1 + s‖ / (2 * Real.pi) ≤ q := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three, norm_nonneg (1 + s)]
    have he0 : 0 ≤ (3 / 2 - s.re) / 2 := by linarith
    have he1 : (3 / 2 - s.re) / 2 ≤ 1 := by linarith [abs_lt.1 hre]
    set x := (q : ℝ) * ‖1 + s‖ / (2 * Real.pi)
    have hx0 : 0 ≤ x := by positivity
    have hpow : x ^ ((3 / 2 - s.re) / 2) ≤ 1 + x := by
      rcases le_or_gt x 1 with hx1 | hx1
      · exact (Real.rpow_le_one hx0 hx1 he0).trans (by linarith)
      · calc x ^ ((3 / 2 - s.re) / 2) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le he1
          _ ≤ 1 + x := by rw [Real.rpow_one]; linarith
    have hz0 : 0 ≤ (riemannZeta (3 / 2 : ℂ)).re := by
      have := riemannZeta_re_pos_of_one_lt (x := 3 / 2) (by norm_num); push_cast at this; linarith
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ (riemannZeta (3 / 2)).re * x ^ ((3 / 2 - s.re) / 2) := hR
      _ ≤ 3 * (1 + x) := mul_le_mul hz32 hpow (by positivity) (by norm_num)
      _ ≤ 4 * q := by linarith


/-- **Core estimate.** For a primitive real character `χ` modulo `q ≥ 16` with `L(s, χ) ≠ 0` on `Re s > 7/8`,
there is a real `u` with `L(1, χ) = exp u` and `|u| ≤ log log log q + 2750`. -/
theorem core_bound {q : ℕ} [NeZero q] (hq : 16 ≤ q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ u : ℝ, DirichletCharacter.LFunction χ 1 = (Real.exp u : ℂ) ∧
      |u| ≤ Real.log (Real.log (Real.log q)) + 2750 := by
  have hq3 : 3 ≤ q := by omega
  have hχ1 : χ ≠ 1 := by
    rintro rfl; rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hprim; omega
  set Lf := DirichletCharacter.LFunction χ
  have hLf : EqOn Lf (LSeries (fun m => χ m)) {s | 1 < s.re} := fun s hs =>
    DirichletCharacter.LFunction_eq_LSeries χ hs
  set f : ℂ → ℂ := fun z => Lf (2 - z)
  have hball : ∀ z ∈ ball (0 : ℂ) (9 / 8), 7 / 8 < (2 - z).re := fun z hz => by
    have h' : ‖z‖ < 9 / 8 := by simpa using hz
    simp only [sub_re]; norm_num; linarith [abs_le.1 (Complex.abs_re_le_norm z)]
  have hLdiff : Differentiable ℂ Lf := DirichletCharacter.differentiable_LFunction hχ1
  have hfdiff : DifferentiableOn ℂ f (ball 0 (9 / 8)) := fun z _ =>
    ((hLdiff (2 - z)).comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 2 - w) z)).differentiableWithinAt
  have hfne : ∀ z ∈ ball (0 : ℂ) (9 / 8), f z ≠ 0 := fun z hz => hH _ (hball z hz)
  -- normalisation at s = 2
  have hL2 : Lf 2 = LSeries (fun m => χ m) 2 := hLf (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  have hL2im : (Lf 2).im = 0 := by
    rw [hL2, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact LSeries_im_eq_zero (fun m => hreal m) 2
  have hL2near : ‖Lf 2 - 1‖ ≤ zetaR 2 - 1 := hL2 ▸ norm_LSeries_two_sub_one_le χ
  have hz2 := zetaR_two_lt
  have hL2re : 1 / 3 ≤ (Lf 2).re ∧ (Lf 2).re ≤ 5 / 3 := by
    have := Complex.abs_re_le_norm (Lf 2 - 1); simp at this
    constructor <;> linarith [abs_le.1 (this.trans hL2near)]
  set ℓ2 : ℝ := Real.log (Lf 2).re
  have hL2eq : Lf 2 = ((Lf 2).re : ℂ) := Complex.ext (by simp) (by simp [hL2im])
  have hw0 : exp (ℓ2 : ℂ) = f 0 := by
    simp only [f, sub_zero]; rw [← Complex.ofReal_exp, Real.exp_log (by linarith), ← hL2eq]
  have hℓ2 : |ℓ2| ≤ 2 := by
    rw [abs_le]; constructor
    · have := Real.one_sub_inv_le_log_of_pos (show 0 < (Lf 2).re by linarith)
      have : ((Lf 2).re)⁻¹ ≤ 3 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      linarith
    · have := Real.log_le_sub_one_of_pos (show 0 < (Lf 2).re by linarith); linarith
  obtain ⟨F, hF0, hFd, hFexp⟩ := exists_log_on_ball hfdiff hfne (ℓ2 : ℂ) hw0 (by norm_num)
  have hFdiff : DifferentiableOn ℂ F (ball 0 (9 / 8)) := fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt
  -- real part bound and Borel–Carathéodory
  set M : ℝ := Real.log (4 * q)
  have hqr : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hM : 0 < M := Real.log_pos (by linarith)
  have hRe : Set.MapsTo F (ball 0 (35 / 32)) {z | z.re ≤ M} := by
    intro z hz
    have hz' : z ∈ ball (0 : ℂ) (9 / 8) := ball_subset_ball (by norm_num) hz
    have he := hFexp z hz'
    have hn : ‖f z‖ ≤ 4 * q := norm_LFunction_disk_le hq3 hprim (by
      have : ‖z‖ < 35 / 32 := by simpa using hz
      simpa [norm_sub_rev] using this)
    simp only [Set.mem_setOf_eq]
    have : Real.exp (F z).re = ‖f z‖ := by rw [← he, Complex.norm_exp]
    rw [← Real.log_exp (F z).re, this]
    exact Real.log_le_log (norm_pos_iff.2 (hfne z hz')) hn
  set Mc : ℝ := 68 * M + 138
  have hBC : ∀ z ∈ closedBall (0 : ℂ) (17 / 16), ‖F z‖ ≤ Mc := by
    intro z hz
    have hzn : ‖z‖ ≤ 17 / 16 := by simpa using hz
    have hz' : z ∈ ball (0 : ℂ) (35 / 32) := by simp; linarith
    have hbc := Complex.borelCaratheodory hM (hFdiff.mono (ball_subset_ball (by norm_num))) hRe
      (by norm_num) hz'
    have hF0n : ‖F 0‖ ≤ 2 := by rw [hF0, Complex.norm_real, Real.norm_eq_abs]; exact hℓ2
    have hden : (1 : ℝ) / 32 ≤ 35 / 32 - ‖z‖ := by linarith
    have h1 : 2 * M * ‖z‖ / (35 / 32 - ‖z‖) ≤ 68 * M := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg z]
    have h2 : ‖F 0‖ * (35 / 32 + ‖z‖) / (35 / 32 - ‖z‖) ≤ 138 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg z, norm_nonneg (F 0)]
    linarith
  -- Cauchy estimates on the circle of radius 17/16
  set ρ : ℝ := 17 / 16
  have hρ : (1 : ℝ) < ρ := by norm_num
  have hcauchy : ∀ n, ‖iteratedDeriv n F 0‖ ≤ n.factorial * Mc / ρ ^ n := by
    intro n
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) ?_ ?_
    · exact hFdiff.diffContOnCl_ball (closedBall_subset_ball (by norm_num : (17 / 16 : ℝ) < 9 / 8))
    · intro z hz; exact hBC z (sphere_subset_closedBall hz)
  -- Taylor expansion at z = 1
  set a : ℕ → ℂ := fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0
  have h1ball : (1 : ℂ) ∈ ball (0 : ℂ) (9 / 8) := by simp; norm_num
  have hTay : HasSum a (F 1) := by
    have := Complex.hasSum_taylorSeries_on_ball hFdiff h1ball
    simpa [a, smul_eq_mul] using this
  have ha : ∀ n, ‖a n‖ ≤ Mc / ρ ^ n := by
    intro n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    simp only [a, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hf]
    calc ‖iteratedDeriv n F 0‖ ≤ n.factorial * Mc / ρ ^ n := hcauchy n
      _ = n.factorial * (Mc / ρ ^ n) := by ring
  -- coefficient domination by log ζ
  obtain ⟨b, hb0, hb00, hbsucc, hbsum⟩ := log_zeta_series
  have hdom : ∀ n, ‖a (n + 1)‖ ≤ b (n + 1) := by
    intro n
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    simp only [a, norm_mul, norm_inv, Complex.norm_natCast]
    rw [iteratedDeriv_succ_log χ (R := 9 / 8) (by norm_num) hLf hFd n, hbsucc n, inv_mul_eq_div]
    gcongr
    have := norm_LSeries_logMul_twist_le χ n (s := 2) (by norm_num)
    simpa using this
  -- the choice of N
  set L1 : ℝ := Real.log q
  set LL : ℝ := Real.log L1
  have hL1 : Real.exp 1 ≤ L1 := by
    have h16 : Real.log 16 ≤ L1 := Real.log_le_log (by norm_num) hqr
    have : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have h2 := Real.log_two_gt_d9
    have he := Real.exp_one_lt_d9
    linarith
  have hL1pos : 0 < L1 := lt_of_lt_of_le (Real.exp_pos 1) hL1
  have hLL : 1 ≤ LL := by
    have := Real.log_le_log (Real.exp_pos 1) hL1; rwa [Real.log_exp] at this
  have hlogρ : 1 / 17 ≤ Real.log ρ := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ρ by norm_num); norm_num at this ⊢; linarith
  have hlogρpos : 0 < Real.log ρ := lt_of_lt_of_le (by norm_num) hlogρ
  set N : ℕ := ⌈LL / Real.log ρ⌉₊
  have hNge : LL / Real.log ρ ≤ N := Nat.le_ceil _
  have hNle : (N : ℝ) ≤ LL / Real.log ρ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [h] at hNge; simp at hNge
    have : 0 < LL / Real.log ρ := by positivity
    linarith)
  have hρN : L1 ≤ ρ ^ N := by
    have : LL ≤ N * Real.log ρ := by rwa [div_le_iff₀ hlogρpos] at hNge
    calc L1 = Real.exp LL := (Real.exp_log hL1pos).symm
      _ ≤ Real.exp (N * Real.log ρ) := Real.exp_le_exp.2 this
      _ = ρ ^ N := by rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hlogN : Real.log N ≤ LL.log + 3 := by
    have hN18 : (N : ℝ) ≤ 18 * LL := by
      have : LL / Real.log ρ ≤ 17 * LL := by
        rw [div_le_iff₀ hlogρpos]; nlinarith
      linarith
    have h1 := Real.log_le_log (by exact_mod_cast hN1) hN18
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have : Real.log 18 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (3 : ℝ)
      have h2 := Real.exp_one_gt_d9
      calc (18 : ℝ) ≤ (2.7182818283 : ℝ) ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := by gcongr
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    linarith
  -- partial sum and tail
  have hsumN : ∑ n ∈ Finset.range (N + 1), ‖a n‖ ≤ 2 + (Real.log N + 4 * Real.log 3) := by
    rw [Finset.sum_range_succ']
    have ha0 : ‖a 0‖ ≤ 2 := by
      simp only [a, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero, hF0,
        Complex.norm_real, Real.norm_eq_abs]; exact hℓ2
    have hS : ∑ n ∈ Finset.range N, ‖a (n + 1)‖ ≤ ∑ n ∈ Finset.range (N + 1), b n := by
      rw [Finset.sum_range_succ' b]
      calc ∑ n ∈ Finset.range N, ‖a (n + 1)‖ ≤ ∑ n ∈ Finset.range N, b (n + 1) :=
            Finset.sum_le_sum fun n _ => hdom n
        _ ≤ _ := le_add_of_nonneg_right (hb0 0)
    have hT := truncation b hb0 (fun r h0 h1 => hbsum r h0 h1) N hN1
    linarith
  have hsumm : Summable a := hTay.summable
  have htail : ‖F 1 - ∑ n ∈ Finset.range (N + 1), a n‖ ≤ 16 * Mc / ρ ^ N := by
    rw [← hTay.tsum_eq, ← hsumm.sum_add_tsum_nat_add (N + 1), add_sub_cancel_left]
    have hgeo : Summable fun n : ℕ => Mc / ρ ^ (n + (N + 1)) := by
      have : Summable fun n : ℕ => (Mc / ρ ^ (N + 1)) * (1 / ρ) ^ n :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      refine this.congr fun n => ?_
      rw [pow_add, one_div_pow]; field_simp; ring
    have hle : ∀ n, ‖a (n + (N + 1))‖ ≤ Mc / ρ ^ (n + (N + 1)) := fun n => ha _
    refine (norm_tsum_le_tsum_norm (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
      ((Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hgeo).trans (le_of_eq ?_))
    have hval : ∑' n : ℕ, Mc / ρ ^ (n + (N + 1)) = (Mc / ρ ^ (N + 1)) * ∑' n : ℕ, (1 / ρ) ^ n := by
      rw [← tsum_mul_left]; congr 1; funext n; rw [pow_add, one_div_pow]; field_simp
    rw [hval, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    simp only [ρ]; field_simp; ring
  have hMc : Mc ≤ 170 * L1 := by
    have h4 : M = Real.log 4 + L1 := Real.log_mul (by norm_num) (by positivity)
    have hl4 : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ); have h2 := Real.exp_one_gt_d9
      calc (4 : ℝ) ≤ 2.7182818283 ^ 2 := by norm_num
        _ ≤ Real.exp 1 ^ 2 := by gcongr
        _ = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7 : ℝ) ≤ L1 := le_trans (by have := Real.exp_one_gt_d9; linarith) hL1
    simp only [Mc]; rw [h4]; linarith
  have htail' : ‖F 1 - ∑ n ∈ Finset.range (N + 1), a n‖ ≤ 2720 := by
    refine htail.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hρN, hMc, hL1pos]
  have hF1 : ‖F 1‖ ≤ LL.log + 2750 := by
    have h1 : ‖F 1‖ ≤ ‖∑ n ∈ Finset.range (N + 1), a n‖ + ‖F 1 - ∑ n ∈ Finset.range (N + 1), a n‖ :=
      norm_le_norm_add_norm_sub' _ _
    have h2 := norm_sum_le (Finset.range (N + 1)) a
    have hl3 : Real.log 3 ≤ 1.1 := by have := Real.log_three_lt_d9; linarith
    linarith
  -- F(1) is real
  have hderivreal : ∀ t : ℝ, |t| < 1 → (deriv F t).im = 0 := by
    intro t ht
    have htb : (t : ℂ) ∈ ball (0 : ℂ) (9 / 8) := by simp; linarith [abs_lt.1 ht]
    have h1 : 1 < (2 - (t : ℂ)).re := by simp; linarith [abs_lt.1 ht]
    rw [(hFd t htb).deriv, logderiv_formula χ hLf h1,
      show (2 : ℂ) - (t : ℂ) = ((2 - t : ℝ) : ℂ) by push_cast; ring]
    exact LSeries_im_eq_zero (fun m => by simp [hreal m]) _
  have hreal01 := im_eq_zero_of_real_deriv (F := F) (R := 1)
    (fun t ht => (hFd t (by simp; linarith [abs_lt.1 ht])).differentiableAt.hasDerivAt)
    hderivreal (by simp [hF0])
  have hF1im : (F 1).im = 0 := by
    have hc : ContinuousAt (fun t : ℝ => (F t).im) 1 := by
      have : ContinuousAt F ((1 : ℝ) : ℂ) := (hFd 1 (by simpa using h1ball)).differentiableAt.continuousAt
      exact (Complex.continuous_im.continuousAt.comp this).comp Complex.continuous_ofReal.continuousAt
    have hlim : Filter.Tendsto (fun t : ℝ => (F t).im) (nhdsWithin 1 (Set.Iio 1)) (nhds ((F ((1 : ℝ) : ℂ)).im)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun t : ℝ => (F t).im) =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact hreal01 t (abs_lt.2 ⟨by linarith [ht.1], ht.2⟩)
    have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
    simpa using this
  refine ⟨(F 1).re, ?_, ?_⟩
  · have he := hFexp 1 h1ball
    have hf1 : f 1 = Lf 1 := by show Lf (2 - 1) = Lf 1; norm_num
    rw [show F 1 = ((F 1).re : ℂ) from Complex.ext (by simp) (by simp [hF1im]), ← Complex.ofReal_exp] at he
    show Lf 1 = _
    rw [← hf1, ← he]
  · exact (Complex.abs_re_le_norm _).trans hF1

end QRHLittlewood

namespace QRHLittlewood

/-- **Goal.** Littlewood's lower bound under the zero-free half-plane `Re s > 7/8`. -/
theorem littlewood_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ (q : ℕ) [NeZero q], q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → (∀ a : ZMod q, (χ a).im = 0) →
      (∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) →
      c / Real.log (Real.log q) ≤ (DirichletCharacter.LFunction χ 1).re := by
  refine ⟨Real.exp (-2750), Real.exp_pos _, 16, fun q _ hq χ hprim hreal hH => ?_⟩
  obtain ⟨u, hu, hub⟩ := core_bound hq hprim hreal hH
  have hqr : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hL1 : 1 < Real.log q := by
    have := Real.log_le_log (by norm_num) hqr
    have h2 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9; linarith
  have hLL : 0 < Real.log (Real.log q) := Real.log_pos hL1
  rw [hu, Complex.ofReal_re, div_le_iff₀ hLL]
  have h1 : -(Real.log (Real.log (Real.log q)) + 2750) ≤ u := by linarith [neg_abs_le u]
  calc Real.exp (-2750) = Real.exp (-(Real.log (Real.log (Real.log q)) + 2750)) *
        Real.exp (Real.log (Real.log (Real.log q))) := by rw [← Real.exp_add]; ring_nf
    _ = Real.exp (-(Real.log (Real.log (Real.log q)) + 2750)) * Real.log (Real.log q) := by
        rw [Real.exp_log hLL]
    _ ≤ Real.exp u * Real.log (Real.log q) := by gcongr

end QRHLittlewood


end


section

open Complex Finset MeasureTheory Set

set_option autoImplicit false

namespace QRHLittlewood

/-- Partial sums of a nontrivial Dirichlet character are bounded by the modulus. -/
lemma norm_sum_range_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (m : ℕ) :
    ‖∑ k ∈ range m, χ k‖ ≤ q := by
  have hper : ∀ n, ∑ k ∈ range (n + q), χ k = ∑ k ∈ range n, χ k := by
    intro n
    rw [sum_range_add]
    have : ∑ k ∈ range q, χ ((n + k : ℕ) : ZMod q) = ∑ a : ZMod q, χ a := by
      have := (ZMod.natCast_self q)
      rw [← Fin.sum_univ_eq_sum_range (fun k => χ ((n + k : ℕ) : ZMod q))]
      refine Fintype.sum_bijective (fun k : Fin q => ((n + k : ℕ) : ZMod q)) ?_ _ _ (fun _ => rfl)
      rw [Fintype.bijective_iff_injective_and_card, ZMod.card, Fintype.card_fin]
      refine ⟨fun a b h => ?_, rfl⟩
      simp only [Nat.cast_add] at h
      have h' := add_left_cancel h
      rw [ZMod.natCast_eq_natCast_iff'] at h'
      exact Fin.ext (by rwa [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h')
    rw [show (∑ k ∈ range q, χ ((n + k : ℕ) : ZMod q)) = ∑ x ∈ range q, χ ↑(n + x) from rfl] at this
    rw [this, MulChar.sum_eq_zero_of_ne_one hχ, add_zero]
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases lt_or_ge m q with h | h
    · calc ‖∑ k ∈ range m, χ k‖ ≤ ∑ k ∈ range m, ‖χ k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ range m, (1 : ℝ) := sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
        _ = m := by simp
        _ ≤ q := by exact_mod_cast h.le
    · obtain ⟨n, rfl⟩ : ∃ n, m = n + q := ⟨m - q, by omega⟩
      rw [hper]
      exact ih n (by have := NeZero.pos q; omega)


/-- `S(t) = ∑_{k ≤ t} χ(k)`. -/
noncomputable def charSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ := ∑ k ∈ Icc 0 ⌊t⌋₊, χ k

lemma norm_charSum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (t : ℝ) :
    ‖charSum χ t‖ ≤ q := by
  rw [charSum, ← Nat.range_succ_eq_Icc_zero]
  exact norm_sum_range_le hχ _


lemma chi_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) : χ 0 = 0 := by
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.2 (by omega)
  exact MulChar.map_nonunit χ not_isUnit_zero

lemma charSum_self {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    charSum χ q = 0 := by
  rw [charSum, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero, sum_range_succ]
  have h1 : ∑ k ∈ range q, χ k = ∑ a : ZMod q, χ a := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => χ (k : ZMod q))]
    refine Fintype.sum_bijective (fun k : Fin q => ((k : ℕ) : ZMod q)) ?_ _ _ (fun _ => rfl)
    rw [Fintype.bijective_iff_injective_and_card, ZMod.card, Fintype.card_fin]
    refine ⟨fun a b h => ?_, rfl⟩
    rw [ZMod.natCast_eq_natCast_iff'] at h
    exact Fin.ext (by rwa [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h)
  rw [h1, MulChar.sum_eq_zero_of_ne_one hχ, ZMod.natCast_self, chi_zero hq, add_zero]


lemma charSum_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) : Measurable (charSum χ) := by
  unfold charSum
  exact (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Icc 0 n, χ k)).comp Nat.measurable_floor

lemma integrableOn_charSum_rpow {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => charSum χ t * (t : ℂ) ^ (-(s + 1))) (Ioi a) := by
  have hint : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1))) (Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul _
  refine hint.mono' ?_ ?_
  · refine ((charSum_measurable χ).mul ?_).aestronglyMeasurable
    exact (Complex.continuous_ofReal.measurable.pow_const _)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t (ht : a < t) => ?_)
    have ht0 : 0 < t := ha.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    gcongr
    exact norm_charSum_le hχ t


/-- For `Re s > 1`: `L(s, χ) = ∑_{k ≤ q} χ(k) k^{-s} + s ∫_q^∞ S(t) t^{-s-1} dt`. -/
theorem LSeries_eq_partial_add_integral {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ n) s = ∑ k ∈ Icc 0 q, (k : ℂ) ^ (-s) * χ k +
      s * ∫ t in Ioi (q : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
  -- partial sums from 1 agree with those from 0
  have hsum01 : ∀ n : ℕ, ∑ k ∈ Icc 1 n, χ k = ∑ k ∈ Icc 0 n, χ k := by
    intro n
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, Nat.cast_zero, chi_zero hq, zero_add]
    rfl
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, χ k) =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound q (Filter.Eventually.of_forall fun n => ?_)
    rw [hsum01, Real.rpow_zero, norm_one, mul_one, ← Nat.range_succ_eq_Icc_zero]
    exact norm_sum_range_le hχ _
  have hsumm : LSeriesSummable (fun n => χ n) s :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne q) χ).2 hs
  have hmain := LSeries_eq_mul_integral (fun n => χ n) le_rfl (by linarith) hsumm hO
  have hcongr : ∀ t : ℝ, (∑ k ∈ Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1)) = charSum χ t * (t : ℂ) ^ (-(s + 1)) :=
    fun t => by rw [hsum01]; rfl
  simp_rw [hcongr] at hmain
  have hint := integrableOn_charSum_rpow hχ (s := s) (by linarith) one_pos
  rw [hmain, ← Ioc_union_Ioi_eq_Ioi hq1, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hq1)), mul_add]
  congr 1
  -- finite Abel summation on [1, q]
  have hdiff : ∀ t ∈ Icc (1 : ℝ) q, DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-s)) t := fun t ht =>
    (hasDerivAt_ofReal_cpow_const (by linarith [ht.1]) (neg_ne_zero.2 hs0)).differentiableAt
  have hderiv : ∀ t : ℝ, 0 < t → deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t = -s * (t : ℂ) ^ (-(s + 1)) := by
    intro t ht
    rw [(hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.2 hs0)).deriv]; ring_nf
  have hdint : IntegrableOn (deriv fun y : ℝ => (y : ℂ) ^ (-s)) (Icc (1 : ℝ) q) := by
    have hc : ContinuousOn (fun t : ℝ => -s * (t : ℂ) ^ (-(s + 1))) (Icc (1 : ℝ) q) := by
      intro t ht
      have : (t : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
      exact (continuousAt_const.mul ((continuous_ofReal.continuousAt).cpow continuousAt_const this)).continuousWithinAt
    refine (hc.integrableOn_Icc).congr_fun (fun t ht => (hderiv t (by linarith [ht.1])).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_integral_mul₀' (fun k => χ k) (by simpa using chi_zero hq χ) q hdiff hdint
  have hSq : ∑ k ∈ Icc 0 q, χ k = 0 := by
    have := charSum_self hq hχ; rwa [charSum, Nat.floor_natCast] at this
  rw [hSq, mul_zero, zero_sub] at habel
  have e : ∑ k ∈ Icc 0 q, (k : ℂ) ^ (-s) * χ k = ∑ k ∈ Icc 0 q, ((k : ℝ) : ℂ) ^ (-s) * χ k := by simp
  rw [e, habel, ← integral_neg, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [hderiv t (by linarith [ht.1])]
  simp only [charSum]; ring


/-- The continuation `G(s) = ∑_{1 ≤ k ≤ q} χ(k) k^{-s} + s ∫_q^∞ S(t) t^{-s-1} dt`. -/
noncomputable def contG {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 q, (k : ℂ) ^ (-s) * χ k + s * ∫ t in Ioi (q : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1))

lemma contG_differentiableOn {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (contG χ) {s | 0 < s.re} := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  set g : ℝ → ℂ := (Ioi (q : ℝ)).indicator (charSum χ)
  have hmel : ∀ s : ℂ, mellin g (-s) = ∫ t in Ioi (q : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1)) := by
    intro s
    have h1 : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • g t =
        (Ioi (q : ℝ)).indicator (fun t => charSum χ t * (t : ℂ) ^ (-(s + 1))) t := by
      intro t
      by_cases ht : t ∈ Ioi (q : ℝ)
      · simp only [g, indicator_of_mem ht, smul_eq_mul]; ring_nf
      · simp only [g, indicator_of_notMem ht, smul_zero]
    rw [mellin]
    simp_rw [h1]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hq0.le]
  intro s hs
  have hs' : 0 < s.re := hs
  apply DifferentiableAt.differentiableWithinAt
  refine DifferentiableAt.add ?_ ?_
  · refine DifferentiableAt.fun_sum fun k hk => ?_
    have hk1 : (k : ℂ) ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; exact_mod_cast (by omega : k ≠ 0)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hk1)).mul_const _
  · refine differentiableAt_id.mul ?_
    have hfun : (fun s => ∫ t in Ioi (q : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1))) = fun s => mellin g (-s) :=
      funext fun s => (hmel s).symm
    rw [hfun]
    refine (mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_).comp s
      differentiableAt_id.neg
    · refine (locallyIntegrableOn_iff isLocallyClosed_Ioi).2 fun K _ hK => ?_
      refine Measure.integrableOn_of_bounded (M := q) hK.measure_lt_top.ne ?_ ?_
      · exact (((charSum_measurable χ).indicator measurableSet_Ioi)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun t => ?_
        by_cases ht : t ∈ Ioi (q : ℝ)
        · simp only [g, indicator_of_mem ht]; exact norm_charSum_le hχ t
        · simp only [g, indicator_of_notMem ht, norm_zero]; positivity
    · refine Asymptotics.IsBigO.of_bound q (Filter.Eventually.of_forall fun t => ?_)
      simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
      by_cases ht : t ∈ Ioi (q : ℝ)
      · simp only [g, indicator_of_mem ht]; exact norm_charSum_le hχ t
      · simp only [g, indicator_of_notMem ht, norm_zero]; positivity
    · simp; linarith
    · refine Asymptotics.IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT hq0] with t ht
      have : t ∉ Ioi (q : ℝ) := fun h => by simp at h; linarith [ht.2]
      simp [g, indicator_of_notMem this]
    · simp


/-- `L(s, χ) = G(s)` on `Re s > 0`. -/
theorem LFunction_eq_contG {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = contG χ s := by
  set U : Set ℂ := {s | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn).analyticOnNhd hU
  have hG : AnalyticOnNhd ℂ (contG χ) U := (contG_differentiableOn hq hχ).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds 2] contG χ := by
    have hV : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [hV] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries_eq_partial_add_integral hq hχ hz, contG]
    congr 1
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le q), Finset.sum_cons]
    have h0 : χ ((0 : ℕ) : ZMod q) = 0 := by simpa using chi_zero hq χ
    rw [h0, mul_zero, zero_add]
    rfl
  exact hL.eqOn_of_preconnected_of_eventuallyEq hG hUc h2 hev hs

/-- `∑_{k=1}^{q} k^{-σ} ≤ 8 q^{1/8}` for `σ ≥ 7/8`. -/
lemma sum_rpow_le {q : ℕ} (hq : 1 ≤ q) {σ : ℝ} (hσ : 7 / 8 ≤ σ) :
    ∑ k ∈ Icc 1 q, (k : ℝ) ^ (-σ) ≤ 8 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hmono : ∑ k ∈ Icc 1 q, (k : ℝ) ^ (-σ) ≤ ∑ k ∈ Icc 1 q, (k : ℝ) ^ (-(7 / 8 : ℝ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.1 hk).1
    exact Real.rpow_le_rpow_of_exponent_le this (by linarith)
  refine hmono.trans ?_
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-(7 / 8 : ℝ))) (Icc 1 (1 + (m : ℝ))) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by norm_num)
  have hint := hanti.sum_le_integral
  have hval : ∫ t in (1 : ℝ)..1 + m, t ^ (-(7 / 8 : ℝ)) = 8 * ((1 + (m : ℝ)) ^ (1 / 8 : ℝ) - 1) := by
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (m : ℝ)) := by
      rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) m])]; intro h; linarith [h.1]
    rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩), Real.one_rpow]; norm_num; ring
  have hsplit : ∀ m : ℕ, ∑ k ∈ Icc 1 (m + 1), (k : ℝ) ^ (-(7 / 8 : ℝ)) =
      1 + ∑ i ∈ range m, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(7 / 8 : ℝ)) := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      push_cast; ring_nf
  rw [hsplit m]
  push_cast at hint ⊢
  rw [hval] at hint
  have e : (1 + (m : ℝ)) ^ (1 / 8 : ℝ) = ((m : ℝ) + 1) ^ (1 / 8 : ℝ) := by rw [add_comm]
  rw [e] at hint
  linarith

/-- **T1.** On `|s - 2| ≤ 9/8`, `‖L(s, χ)‖ ≤ 12 q^{1/8}`. -/
theorem norm_LFunction_le_q_eighth {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : ‖s - 2‖ ≤ 9 / 8) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 12 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hre : |s.re - 2| ≤ 9 / 8 := by
    have := Complex.abs_re_le_norm (s - 2); simp at this; linarith
  have hσ : 7 / 8 ≤ s.re := by linarith [abs_le.1 hre]
  have hsn : ‖s‖ ≤ 25 / 8 := by
    calc ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
      _ ≤ ‖s - 2‖ + 2 := by refine (norm_add_le _ _).trans ?_; simp
      _ ≤ 25 / 8 := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  rw [LFunction_eq_contG hq hχ (by linarith), contG]
  have h1 : ‖∑ k ∈ Icc 1 q, (k : ℂ) ^ (-s) * χ k‖ ≤ 8 * (q : ℝ) ^ (1 / 8 : ℝ) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k hk => ?_).trans (sum_rpow_le (by omega) hσ))
    have hk : (0 : ℝ) < k := by exact_mod_cast (by have := (Finset.mem_Icc.1 hk).1; omega : 0 < k)
    rw [norm_mul, show (k : ℂ) = ((k : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hk, neg_re]
    exact mul_le_of_le_one_right (by positivity) (DirichletCharacter.norm_le_one χ _)
  have h2 : ‖∫ t in Ioi (q : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1))‖ ≤ (q : ℝ) ^ (1 - s.re) / s.re := by
    have hb : ∫ t in Ioi (q : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) = (q : ℝ) ^ (1 - s.re) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hq0]
      rw [show -(s.re + 1) + 1 = -s.re by ring, show (1 : ℝ) - s.re = 1 + -s.re by ring,
        Real.rpow_add hq0, Real.rpow_one]
      field_simp
    rw [← hb]
    refine norm_integral_le_of_norm_le ((integrableOn_Ioi_rpow_of_lt (by linarith) hq0).const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t (ht : (q : ℝ) < t) => ?_)
    have ht0 : 0 < t := hq0.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    gcongr
    exact norm_charSum_le hχ t
  have h3 : (q : ℝ) ^ (1 - s.re) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hpos : (0 : ℝ) < (q : ℝ) ^ (1 / 8 : ℝ) := by positivity
  calc ‖∑ k ∈ Icc 1 q, (k : ℂ) ^ (-s) * χ k + s * ∫ t in Ioi (q : ℝ), charSum χ t * (t : ℂ) ^ (-(s + 1))‖
      ≤ 8 * (q : ℝ) ^ (1 / 8 : ℝ) + ‖s‖ * ((q : ℝ) ^ (1 - s.re) / s.re) := by
        refine (norm_add_le _ _).trans (add_le_add h1 ?_)
        rw [norm_mul]; gcongr
    _ ≤ 8 * (q : ℝ) ^ (1 / 8 : ℝ) + 25 / 8 * ((q : ℝ) ^ (1 / 8 : ℝ) / (7 / 8)) := by
        gcongr
    _ ≤ 12 * (q : ℝ) ^ (1 / 8 : ℝ) := by nlinarith

end QRHLittlewood
end


section

open Complex MeasureTheory Set Filter Topology Metric Real

set_option autoImplicit false

namespace QRHLittlewood

/-- **Carathéodory's coefficient inequality** on a fixed circle: if `F` is holomorphic near the closed
disk of radius `r` and `Re F ≤ A` on it, then `‖F^{(n)}(0)‖ / n! ≤ 2 (A - Re F(0)) / r^n` for `n ≥ 1`. -/
theorem caratheodory_coeff_r {F : ℂ → ℂ} {r A : ℝ} (hr : 0 < r)
    (hF : DiffContOnCl ℂ F (ball 0 r)) (hA : ∀ z ∈ closedBall (0 : ℂ) r, (F z).re ≤ A)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedDeriv n F 0‖ / n.factorial ≤ 2 * (A - (F 0).re) / r ^ n := by
  set E : ℝ → ℂ := circleMap 0 r
  have hEn : ∀ θ, ‖E θ‖ = r := fun θ => by simp [E, abs_of_pos hr]
  have hE0 : ∀ θ, E θ ≠ 0 := fun θ h => by have := hEn θ; rw [h, norm_zero] at this; linarith
  have hEmem : ∀ θ, E θ ∈ closedBall (0 : ℂ) r := fun θ => by simp [mem_closedBall, hEn θ]
  have hFc : ContinuousOn F (closedBall 0 r) := by
    have := hF.continuousOn; rwa [closure_ball 0 hr.ne'] at this
  have hu : Continuous fun θ => F (E θ) :=
    hFc.comp_continuous (continuous_circleMap 0 r) hEmem
  have hd : ∀ z ∈ ball (0 : ℂ) r, DifferentiableAt ℂ F z := fun z hz =>
    hF.differentiableAt isOpen_ball hz
  -- (I1) Cauchy coefficient formula
  have hI1 := circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable hr n
    countable_empty hFc (fun z hz => hd z hz.1)
  -- define S = ∫ F(E θ) / (E θ)^n
  set S : ℂ := ∫ θ in (0 : ℝ)..2 * π, F (E θ) / E θ ^ n
  have hI1' : (2 * π * I / n.factorial) • iteratedDeriv n F 0 = I * S := by
    rw [← hI1, circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, sub_zero, smul_eq_mul]
    have := hE0 θ
    rw [show circleMap 0 r θ = E θ from rfl]
    field_simp
    ring
  -- (I2) ∫ E^n F(E) = 0
  have hI2 : ∫ θ in (0 : ℝ)..2 * π, E θ ^ n * F (E θ) = 0 := by
    have h := circleIntegral_eq_zero_of_differentiable_on_off_countable (f := fun z => z ^ (n - 1) * F z)
      hr.le countable_empty ((continuous_pow _).continuousOn.mul hFc)
      (fun z hz => (differentiableAt_pow _).mul (hd z hz.1))
    rw [circleIntegral] at h
    have h2 : ∫ θ in (0 : ℝ)..2 * π, I * (E θ ^ n * F (E θ)) = 0 := by
      rw [← h]; refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [deriv_circleMap, smul_eq_mul]
      rw [show circleMap 0 r θ = E θ from rfl]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; ring
    rw [intervalIntegral.integral_const_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left I_ne_zero
  -- (I3) ∫ 1 / E^n = 0
  have hI3 : ∫ θ in (0 : ℝ)..2 * π, 1 / E θ ^ n = 0 := by
    have h := circleIntegral.integral_sub_zpow_of_ne (n := -((n : ℤ) + 1)) (by omega) 0 0 r
    rw [circleIntegral] at h
    have h2 : ∫ θ in (0 : ℝ)..2 * π, I * (1 / E θ ^ n) = 0 := by
      rw [← h]; refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [deriv_circleMap, smul_eq_mul, sub_zero]
      rw [show circleMap 0 r θ = E θ from rfl]
      have := hE0 θ
      rw [zpow_neg, zpow_add₀ this, zpow_natCast, zpow_one]
      field_simp
    rw [intervalIntegral.integral_const_mul] at h2
    exact (mul_eq_zero.1 h2).resolve_left I_ne_zero
  -- (conj) ∫ conj(F(E)) / E^n = 0
  have hconjE : ∀ θ, 1 / E θ ^ n = (starRingEnd ℂ) (E θ) ^ n / ((r : ℂ) ^ 2) ^ n := by
    intro θ
    have h1 : E θ * (starRingEnd ℂ) (E θ) = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hEn θ]; push_cast; ring
    have := hE0 θ
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hc : (starRingEnd ℂ) (E θ) ≠ 0 := by simpa using hE0 θ
    rw [← h1, mul_pow]; field_simp
  have hQ : ∫ θ in (0 : ℝ)..2 * π, (starRingEnd ℂ) (F (E θ)) / E θ ^ n = 0 := by
    have h : ∀ θ, (starRingEnd ℂ) (F (E θ)) / E θ ^ n =
        (1 / ((r : ℂ) ^ 2) ^ n) * (starRingEnd ℂ) (E θ ^ n * F (E θ)) := by
      intro θ; rw [div_eq_mul_one_div, hconjE, map_mul, map_pow]; ring
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le two_pi_pos.le,
      integral_conj, ← intervalIntegral.integral_of_le two_pi_pos.le, hI2, map_zero, mul_zero]
  -- continuity facts
  have hcE : Continuous E := continuous_circleMap 0 r
  have hc1 : Continuous fun θ => F (E θ) / E θ ^ n := hu.div (hcE.pow n) (fun θ => pow_ne_zero _ (hE0 θ))
  have hc2 : Continuous fun θ => (starRingEnd ℂ) (F (E θ)) / E θ ^ n :=
    (continuous_conj.comp hu).div (hcE.pow n) (fun θ => pow_ne_zero _ (hE0 θ))
  have hc3 : Continuous fun θ => 1 / E θ ^ n := continuous_const.div (hcE.pow n) (fun θ => pow_ne_zero _ (hE0 θ))
  -- S equals the integral of the real kernel 2 (Re F - A)
  have hS : S = ∫ θ in (0 : ℝ)..2 * π, ((2 * ((F (E θ)).re - A) : ℝ) : ℂ) / E θ ^ n := by
    have h : ∀ θ, ((2 * ((F (E θ)).re - A) : ℝ) : ℂ) / E θ ^ n =
        F (E θ) / E θ ^ n + (starRingEnd ℂ) (F (E θ)) / E θ ^ n - (2 * A : ℂ) * (1 / E θ ^ n) := by
      intro θ
      have : ((2 * ((F (E θ)).re - A) : ℝ) : ℂ) = F (E θ) + (starRingEnd ℂ) (F (E θ)) - 2 * A := by
        rw [Complex.add_conj]; push_cast; ring
      rw [this]; ring
    simp_rw [h]
    have hi1 := hc1.intervalIntegrable (μ := volume) 0 (2 * π)
    have hi2 := hc2.intervalIntegrable (μ := volume) 0 (2 * π)
    have hi3 := (hc3.const_mul (2 * A : ℂ)).intervalIntegrable (μ := volume) 0 (2 * π)
    rw [intervalIntegral.integral_sub (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, hQ, hI3]
    simp [S]
  -- mean value property
  have hmean : ∫ θ in (0 : ℝ)..2 * π, F (E θ) = (2 * π : ℂ) * F 0 := by
    have hF' : DiffContOnCl ℂ F (ball 0 |r|) := by rwa [abs_of_pos hr]
    have h := hF'.circleAverage
    rw [Real.circleAverage_def] at h
    have h2 : (2 * π : ℝ) • ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ)) = (2 * π : ℝ) • F 0 := by
      rw [h]
    rw [smul_smul, mul_inv_cancel₀ two_pi_pos.ne', one_smul, Complex.real_smul] at h2
    rw [show (∫ θ in (0 : ℝ)..2 * π, F (E θ)) = ∫ θ in (0 : ℝ)..2 * π, F (circleMap 0 r θ) from rfl, h2]
    push_cast; ring
  -- bound on S
  have hSbound : ‖S‖ ≤ 2 * π * (2 * (A - (F 0).re) / r ^ n) := by
    rw [hS]
    have hle : ∀ θ ∈ Set.Ioc (0 : ℝ) (2 * π),
        ‖((2 * ((F (E θ)).re - A) : ℝ) : ℂ) / E θ ^ n‖ ≤ 2 * (A - (F (E θ)).re) / r ^ n := by
      intro θ _
      rw [norm_div, Complex.norm_real, norm_pow, hEn θ, Real.norm_eq_abs]
      have := hA _ (hEmem θ)
      rw [abs_of_nonpos (by linarith)]; ring_nf; rfl
    calc ‖∫ θ in (0 : ℝ)..2 * π, ((2 * ((F (E θ)).re - A) : ℝ) : ℂ) / E θ ^ n‖
        ≤ ∫ θ in (0 : ℝ)..2 * π, 2 * (A - (F (E θ)).re) / r ^ n :=
          intervalIntegral.norm_integral_le_of_norm_le two_pi_pos.le
            (Filter.Eventually.of_forall hle)
            ((((continuous_const.sub (continuous_re.comp hu)).const_mul 2).div_const _).intervalIntegrable _ _)
      _ = 2 * π * (2 * (A - (F 0).re) / r ^ n) := by
          have hre : ∫ θ in (0 : ℝ)..2 * π, (F (E θ)).re = 2 * π * (F 0).re := by
            have h1 : ∫ θ in (0 : ℝ)..2 * π, (F (E θ)).re = (∫ θ in (0 : ℝ)..2 * π, F (E θ)).re := by
              have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
                (hu.intervalIntegrable (μ := volume) 0 (2 * π))
              simpa using this
            rw [h1, hmean]; simp
          have hfun : (fun θ => 2 * (A - (F (E θ)).re) / r ^ n) =
              fun θ => (2 / r ^ n) * (A - (F (E θ)).re) := by funext θ; ring
          rw [hfun, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_sub (f := fun _ => A) (g := fun θ => (F (E θ)).re)
              (continuous_const.intervalIntegrable _ _) ((continuous_re.comp hu).intervalIntegrable _ _),
            intervalIntegral.integral_const, hre]
          simp; ring
  -- conclude
  have hD : iteratedDeriv n F 0 = (n.factorial : ℂ) / (2 * π) * S := by
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast two_pi_pos.ne'
    rw [smul_eq_mul] at hI1'
    field_simp at hI1' ⊢
    linear_combination hI1'
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [hD, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos, div_le_iff₀ hf]
  calc (n.factorial : ℝ) / (2 * π) * ‖S‖ ≤ n.factorial / (2 * π) * (2 * π * (2 * (A - (F 0).re) / r ^ n)) := by
        gcongr
    _ = 2 * (A - (F 0).re) / r ^ n * n.factorial := by field_simp


/-- **Carathéodory's coefficient inequality.** If `F` is holomorphic on `|z| < R` with `Re F ≤ A` there,
then `‖F^{(n)}(0)‖ / n! ≤ 2 (A - Re F(0)) / R^n` for `n ≥ 1`. -/
theorem caratheodory_coeff {F : ℂ → ℂ} {R A : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (ball 0 R)) (hA : ∀ z ∈ ball (0 : ℂ) R, (F z).re ≤ A)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedDeriv n F 0‖ / n.factorial ≤ 2 * (A - (F 0).re) / R ^ n := by
  have hr : ∀ r ∈ Ioo 0 R, ‖iteratedDeriv n F 0‖ / n.factorial ≤ 2 * (A - (F 0).re) / r ^ n := by
    intro r hr
    exact caratheodory_coeff_r hr.1 (hF.diffContOnCl_ball (closedBall_subset_ball hr.2))
      (fun z hz => hA z (closedBall_subset_ball hr.2 hz)) hn
  have hlim : Tendsto (fun r : ℝ => 2 * (A - (F 0).re) / r ^ n) (𝓝[<] R) (𝓝 (2 * (A - (F 0).re) / R ^ n)) := by
    have hc : ContinuousAt (fun r : ℝ => 2 * (A - (F 0).re) / r ^ n) R :=
      (continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero _ hR.ne'))
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hR] with r hr' using hr r hr'

end QRHLittlewood
end


section

open Complex MeasureTheory Set Filter Topology

set_option autoImplicit false

namespace QRHLittlewood

/-- `T(s) = ∫_1^∞ {t} t^{-s-1} dt`. -/
noncomputable def fracT (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

lemma fracT_differentiableOn : DifferentiableOn ℂ fracT {s | 0 < s.re} := by
  set g : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ))
  have hmel : ∀ s : ℂ, mellin g (-s) = fracT s := by
    intro s
    have h1 : ∀ t : ℝ, (t : ℂ) ^ (-s - 1) • g t =
        (Ioi (1 : ℝ)).indicator (fun t => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) t := by
      intro t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · simp only [g, indicator_of_mem ht, smul_eq_mul]; ring_nf
      · simp only [g, indicator_of_notMem ht, smul_zero]
    rw [mellin]; simp_rw [h1]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right zero_le_one, fracT]
  have hbound : ∀ t, ‖g t‖ ≤ 1 := fun t => by
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simp only [g, indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]; exact (Int.fract_lt_one t).le
    · simp [g, indicator_of_notMem ht]
  have hmeas : Measurable g := by
    have := (Complex.continuous_ofReal.measurable.comp (measurable_fract (R := ℝ))).indicator
      (measurableSet_Ioi (a := (1 : ℝ)))
    simpa [g, Function.comp_def] using this
  intro s hs
  have hs' : 0 < s.re := hs
  rw [show fracT = fun s => mellin g (-s) from funext fun s => (hmel s).symm]
  refine (mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_).comp s
    differentiableAt_id.neg |>.differentiableWithinAt
  · refine (locallyIntegrableOn_iff isLocallyClosed_Ioi).2 fun K _ hK => ?_
    exact Measure.integrableOn_of_bounded (M := 1) hK.measure_lt_top.ne hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  · refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]; exact hbound t
  · simp; linarith
  · refine Asymptotics.IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    have : t ∉ Ioi (1 : ℝ) := fun h => by simp at h; linarith [ht.2]
    simp [g, indicator_of_notMem this]
  · simp

lemma norm_fracT_le {s : ℂ} (hs : 0 < s.re) : ‖fracT s‖ ≤ 1 / s.re := by
  have hb : ∫ t in Ioi (1 : ℝ), t ^ (-(s.re + 1)) = 1 / s.re := by
    have := hs.ne'
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -(s.re + 1) + 1 = -s.re by ring]; field_simp
  rw [← hb, fracT]
  refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_)
  have ht0 : 0 < t := one_pos.trans ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg t)]
  simp only [neg_re, add_re, one_re]
  exact mul_le_of_le_one_left (by positivity) (Int.fract_lt_one t).le


lemma Ioi_one_eq_iUnion : Ioi (1 : ℝ) = ⋃ n : ℕ, Ioc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
  ext t
  simp only [mem_Ioi, mem_iUnion, mem_Ioc]
  constructor
  · intro ht
    refine ⟨⌈t⌉₊ - 2, ?_, ?_⟩
    · have h1 : (2 : ℕ) ≤ ⌈t⌉₊ := by
        have : (1 : ℝ) < ⌈t⌉₊ := lt_of_lt_of_le ht (Nat.le_ceil t)
        exact_mod_cast (show 1 < ⌈t⌉₊ by exact_mod_cast this)
      rw [Nat.cast_sub h1]; push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ t by linarith); linarith
    · have h1 : (2 : ℕ) ≤ ⌈t⌉₊ := by
        have : (1 : ℝ) < ⌈t⌉₊ := lt_of_lt_of_le ht (Nat.le_ceil t)
        exact_mod_cast (show 1 < ⌈t⌉₊ by exact_mod_cast this)
      rw [Nat.cast_sub h1]; push_cast; linarith [Nat.le_ceil t]
  · rintro ⟨n, h1, _⟩; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- For real `x > 1`, `T(x)` is Mathlib's real Euler–Maclaurin remainder `termTSum x`. -/
lemma fracT_ofReal {x : ℝ} (hx : 1 < x) : fracT x = ((ZetaAsymptotics.termTSum x : ℝ) : ℂ) := by
  set f : ℝ → ℝ := fun t => Int.fract t * t ^ (-(x + 1))
  have hf : IntegrableOn f (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (show -(x + 1) < -1 by linarith) one_pos).mono' ?_ ?_
    · exact (measurable_fract.mul (measurable_id.pow_const _)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Int.fract_nonneg t) (by positivity))]
      exact mul_le_of_le_one_left (by positivity) (Int.fract_lt_one t).le
  have hc : fracT x = ((∫ t in Ioi (1 : ℝ), f t : ℝ) : ℂ) := by
    rw [fracT, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 1 < t) => ?_
    simp only [f]; push_cast
    rw [Complex.ofReal_cpow (by linarith)]; push_cast; ring_nf
  rw [hc]; congr 1
  rw [Ioi_one_eq_iUnion, integral_iUnion (fun n => measurableSet_Ioc) ?_ (Ioi_one_eq_iUnion ▸ hf),
    ZetaAsymptotics.termTSum]
  · congr 1; funext n
    rw [ZetaAsymptotics.term, intervalIntegral.integral_of_le (by push_cast; linarith),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    push_cast
    rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hfl : Int.fract t = t - (n + 1) := by
      rw [Int.fract_eq_iff]
      exact ⟨by linarith [ht.1], by linarith [ht.2], (n : ℤ) + 1, by push_cast; ring⟩
    simp only [f, hfl]
    rw [Real.rpow_neg (by linarith [ht.1, (Nat.cast_nonneg n : (0:ℝ) ≤ n)])]; ring
  · intro i j hij
    simp only [Function.onFun]
    rw [Set.Ioc_disjoint_Ioc]
    rcases lt_or_gt_of_ne hij with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      exact (min_le_left _ _).trans (by rw [le_max_iff]; right; linarith)
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      exact (min_le_right _ _).trans (by rw [le_max_iff]; left; linarith)


lemma riemannZeta_ofReal_eq {x : ℝ} (hx : 1 < x) : riemannZeta (x : ℂ) = (zetaR x : ℂ) := by
  have hx' : 1 < ((x : ℂ)).re := by simpa using hx
  rw [← LSeries_one_eq_riemannZeta hx', show (1 : ℕ → ℂ) = fun m : ℕ => (1 : DirichletCharacter ℂ 1) m from
    funext fun m => (chi1_apply m).symm, LSeries_chi1_eq_zetaR hx]

/-- **First-order Euler–Maclaurin.** `ζ(s) = 1/(s - 1) + 1 - s T(s)` for `Re s > 1`. -/
theorem riemannZeta_eq_fracT {s : ℂ} (hs : 1 < s.re) : riemannZeta s = 1 / (s - 1) + 1 - s * fracT s := by
  set U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hne : ∀ z ∈ U, z ≠ 1 := fun z hz h => by simp [U, h] at hz
  have hZ : AnalyticOnNhd ℂ riemannZeta U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_riemannZeta (hne z hz)).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ (fun s => 1 / (s - 1) + 1 - s * fracT s) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    have hz0 : 0 < z.re := by have : 1 < z.re := hz; linarith
    have hT : DifferentiableAt ℂ fracT z :=
      (fracT_differentiableOn z hz0).differentiableAt
        ((isOpen_lt continuous_const continuous_re).mem_nhds hz0)
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.2 (hne z hz)
    exact (DifferentiableAt.sub ((DifferentiableAt.div (differentiableAt_const _)
      ((differentiableAt_id (x := z)).sub_const 1) hz1).add_const 1)
      ((differentiableAt_id (x := z)).mul hT)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), riemannZeta z = 1 / (z - 1) + 1 - z * fracT z := by
    set u : ℕ → ℂ := fun n => ((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hu : Tendsto u atTop (𝓝[≠] (2 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have : Tendsto (fun n : ℕ => (2 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (2 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at this
        have := (Complex.continuous_ofReal.tendsto 2).comp this
        simpa [u, Function.comp_def] using this
      · refine Eventually.of_forall fun n => ?_
        simp only [u, mem_compl_iff, mem_singleton_iff]
        intro h
        have h' := congrArg Complex.re h
        simp only [ofReal_re, re_ofNat] at h'
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine hu.frequently (Frequently.of_forall fun n => ?_)
    set x : ℝ := 2 + 1 / ((n : ℝ) + 1)
    have hx : 1 < x := by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                          simp only [x]; linarith
    show riemannZeta (x : ℂ) = 1 / ((x : ℂ) - 1) + 1 - (x : ℂ) * fracT x
    rw [riemannZeta_ofReal_eq hx, fracT_ofReal hx]
    have h := ZetaAsymptotics.zeta_limit_aux1 hx
    have hz : zetaR x = 1 / (x - 1) + 1 - x * ZetaAsymptotics.termTSum x := by
      unfold zetaR; push_cast at h ⊢; linarith
    rw [hz]; push_cast; ring
  exact hZ.eqOn_of_preconnected_of_frequently_eq hG (convex_halfSpace_re_gt 1).isPreconnected h2 hfreq hs

end QRHLittlewood
end


section

open Complex MeasureTheory Set Filter Topology Metric

set_option autoImplicit false

namespace QRHLittlewood

/-- `w(z) = (1 - z) T(2 - z)`. -/
noncomputable def wT (z : ℂ) : ℂ := (1 - z) * fracT (2 - z)

/-- The explicit logarithm of `h(z) = (1 - z) ζ(2 - z)`. -/
noncomputable def Lh (z : ℂ) : ℂ := Complex.log (2 - z) + Complex.log (1 - wT z)

lemma re_two_sub_pos {z : ℂ} (hz : ‖z‖ < 1.36) : 0.64 < (2 - z).re := by
  have := Complex.re_le_norm z; simp only [sub_re]; norm_num; linarith

lemma norm_wT_le {z : ℂ} (hz : ‖z‖ < 1.36) : ‖wT z‖ ≤ 0.94 := by
  have hσ := re_two_sub_pos hz
  set s := 2 - z
  have hT := norm_fracT_le (s := s) (by linarith)
  have hs1 : ‖s - 1‖ ≤ 0.94 * s.re := by
    have hzs : z = 2 - s := by simp [s]
    have hn : ‖s - 2‖ < 1.36 := by rw [show s - 2 = -z by simp [s], norm_neg]; exact hz
    have h1 : (s.re - 2) ^ 2 + s.im ^ 2 < 1.36 ^ 2 := by
      have := Complex.sq_norm (s - 2); rw [Complex.normSq_apply] at this; simp at this
      nlinarith [norm_nonneg (s - 2)]
    have h2 : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have h3 : ‖s - 1‖ ^ 2 ≤ (0.94 * s.re) ^ 2 := by rw [h2]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h3
  rw [wT, norm_mul, show (1 : ℂ) - z = s - 1 by simp [s]; ring]
  calc ‖s - 1‖ * ‖fracT s‖ ≤ (0.94 * s.re) * (1 / s.re) := by gcongr
    _ = 0.94 := by field_simp


lemma norm_log_le {w : ℂ} (hw : w ≠ 0) : ‖Complex.log w‖ ≤ |Real.log ‖w‖| + Real.pi := by
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |Real.log ‖w‖| + Real.pi := by
        rw [Complex.log_re, Complex.log_im]
        gcongr
        exact abs_le.2 ⟨by linarith [Complex.neg_pi_lt_arg w], Complex.arg_le_pi w⟩

lemma Lh_differentiableOn : DifferentiableOn ℂ Lh (ball 0 1.36) := by
  intro z hz
  have hz' : ‖z‖ < 1.36 := by simpa using hz
  have hσ := re_two_sub_pos hz'
  have hw := norm_wT_le hz'
  have hT : DifferentiableAt ℂ fracT (2 - z) :=
    (fracT_differentiableOn (2 - z) (by show 0 < (2 - z).re; linarith)).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds (show 0 < (2 - z).re by linarith))
  have h1 : (2 - z) ∈ slitPlane := Or.inl (by linarith)
  have h2 : (1 - wT z) ∈ slitPlane := Or.inl (by
    have := Complex.re_le_norm (wT z); simp only [sub_re, one_re]; linarith)
  have hwd : DifferentiableAt ℂ wT z :=
    ((differentiableAt_const _).sub differentiableAt_id).mul (hT.comp z ((differentiableAt_const _).sub differentiableAt_id))
  exact (((differentiableAt_const _).sub differentiableAt_id).clog h1 |>.add
    (((differentiableAt_const _).sub hwd).clog h2)).differentiableWithinAt

lemma norm_Lh_le {z : ℂ} (hz : ‖z‖ < 1.36) : ‖Lh z‖ ≤ 11 := by
  have hσ := re_two_sub_pos hz
  have hw := norm_wT_le hz
  have hs0 : (2 : ℂ) - z ≠ 0 := fun h => by rw [h] at hσ; simp at hσ; linarith
  have h1w : 0.06 ≤ ‖1 - wT z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (wT z); simp at this; linarith
  have h1w' : ‖1 - wT z‖ ≤ 1.94 := by
    have := norm_sub_le (1 : ℂ) (wT z); simp at this; linarith
  have hsn : 0.64 ≤ ‖(2 : ℂ) - z‖ := le_trans hσ.le (Complex.re_le_norm _)
  have hsn' : ‖(2 : ℂ) - z‖ ≤ 3.36 := by
    have := norm_sub_le (2 : ℂ) z; simp at this; linarith
  have hl1 : |Real.log ‖(2 : ℂ) - z‖| ≤ 1.3 := by
    rw [abs_le]; constructor
    · have := Real.one_sub_inv_le_log_of_pos (show 0 < ‖(2 : ℂ) - z‖ by linarith)
      have : ‖(2 : ℂ) - z‖⁻¹ ≤ 1 / 0.64 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
      norm_num at *; linarith
    · have := Real.log_le_sub_one_of_pos (show 0 < ‖(2 : ℂ) - z‖ by linarith)
      have : Real.log ‖(2 : ℂ) - z‖ ≤ Real.log 3.36 := Real.log_le_log (by linarith) hsn'
      have h336 : Real.log 3.36 ≤ 1.3 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h3 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1.3 by norm_num) 4
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h3
        norm_num at h3 ⊢
        linarith
      linarith
  have hl2 : |Real.log ‖1 - wT z‖| ≤ 2.9 := by
    rw [abs_le]; constructor
    · have := Real.one_sub_inv_le_log_of_pos (show 0 < ‖1 - wT z‖ by linarith)
      have hinv : ‖1 - wT z‖⁻¹ ≤ 1 / 0.06 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
      -- log x ≥ 1 - 1/x is too weak here; use log x ≥ log 0.06 ≥ -2.9
      have hlog : Real.log 0.06 ≤ Real.log ‖1 - wT z‖ := Real.log_le_log (by norm_num) h1w
      have h006 : -2.9 ≤ Real.log 0.06 := by
        rw [show (0.06 : ℝ) = (50 / 3)⁻¹ by norm_num, Real.log_inv, neg_le_neg_iff]
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have h3 := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2.9 by norm_num) 6
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h3
        norm_num at h3 ⊢
        linarith
      linarith
    · have := Real.log_le_sub_one_of_pos (show 0 < ‖1 - wT z‖ by linarith); linarith
  have hw0 : 1 - wT z ≠ 0 := fun h => by rw [h] at h1w; simp at h1w; linarith
  calc ‖Lh z‖ ≤ ‖Complex.log (2 - z)‖ + ‖Complex.log (1 - wT z)‖ := norm_add_le _ _
    _ ≤ (|Real.log ‖(2 : ℂ) - z‖| + Real.pi) + (|Real.log ‖1 - wT z‖| + Real.pi) :=
        add_le_add (norm_log_le hs0) (norm_log_le hw0)
    _ ≤ 11 := by linarith [Real.pi_lt_d2]


lemma Lh_one : Lh 1 = 0 := by simp [Lh, wT, show (2 : ℂ) - 1 = 1 by norm_num]

lemma exp_Lh {z : ℂ} (hz : ‖z‖ < 1.36) : Complex.exp (Lh z) = (2 - z) * (1 - wT z) := by
  have hσ := re_two_sub_pos hz
  have hw := norm_wT_le hz
  have hs0 : (2 : ℂ) - z ≠ 0 := fun h => by rw [h] at hσ; simp at hσ; linarith
  have hw0 : 1 - wT z ≠ 0 := fun h => by
    have := norm_sub_norm_le (1 : ℂ) (wT z); rw [h] at this; simp at this; linarith
  rw [Lh, Complex.exp_add, Complex.exp_log hs0, Complex.exp_log hw0]

/-- On `|z| < 1`: `(2 - z)(1 - w(z)) = (1 - z) ζ(2 - z)`. -/
lemma h_eq_zeta {z : ℂ} (hz : ‖z‖ < 1) : (2 - z) * (1 - wT z) = (1 - z) * riemannZeta (2 - z) := by
  have h1 : 1 < (2 - z).re := by have := Complex.re_le_norm z; simp only [sub_re]; norm_num; linarith
  have hz1 : (2 : ℂ) - z - 1 ≠ 0 := fun h => by
    have : z = 1 := by linear_combination -h
    rw [this] at hz; simp at hz
  rw [riemannZeta_eq_fracT h1, wT]
  field_simp
  ring

lemma Lh_zero : Lh 0 = ((Real.log (zetaR 2) : ℝ) : ℂ) := by
  have hT : fracT 2 = ((ZetaAsymptotics.termTSum 2 : ℝ) : ℂ) := by
    have := fracT_ofReal (x := 2) (by norm_num); simpa using this
  have hTb : ZetaAsymptotics.termTSum 2 ≤ 1 / 2 := by
    have := norm_fracT_le (s := 2) (by norm_num)
    rw [hT, Complex.norm_real, Real.norm_eq_abs] at this
    norm_num at this; linarith [le_abs_self (ZetaAsymptotics.termTSum 2)]
  have hb : 0 < 1 - ZetaAsymptotics.termTSum 2 := by linarith
  have hrel := h_eq_zeta (z := 0) (by simp)
  simp only [sub_zero, one_mul] at hrel
  have hz2 : riemannZeta 2 = (zetaR 2 : ℂ) := by
    have := riemannZeta_ofReal_eq (x := 2) (by norm_num); simpa using this
  rw [hz2, wT, sub_zero, one_mul, show (2 : ℂ) - 0 = 2 by simp, hT] at hrel
  have hprod : (2 : ℝ) * (1 - ZetaAsymptotics.termTSum 2) = zetaR 2 := by
    have := congrArg Complex.re hrel; simp at this; linarith
  simp only [Lh, wT, sub_zero, one_mul]
  rw [hT, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log hb.le, ← Complex.ofReal_add,
    ← Real.log_mul (by norm_num) hb.ne', hprod]

/-- Iterated derivatives of `(1 - z)⁻¹`. -/
lemma iteratedDeriv_one_sub_inv (k : ℕ) {z : ℂ} (hz : z ≠ 1) :
    iteratedDeriv k (fun w : ℂ => (1 - w)⁻¹) z = k.factorial * ((1 - z)⁻¹) ^ (k + 1) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hopen : IsOpen {w : ℂ | w ≠ 1} := isOpen_ne
    have hev : iteratedDeriv k (fun w : ℂ => (1 - w)⁻¹) =ᶠ[𝓝 z]
        fun w => (k.factorial : ℂ) * ((1 - w)⁻¹) ^ (k + 1) := by
      filter_upwards [hopen.mem_nhds hz] with w hw using ih hw
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    have hd : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
      have := ((hasDerivAt_id z).const_sub 1).inv h1z
      exact this.congr_deriv (by simp [div_eq_mul_inv, inv_pow])
    have this : HasDerivAt (fun w : ℂ => (k.factorial : ℂ) * (1 - w)⁻¹ ^ (k + 1))
        ((k.factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * ((1 - z)⁻¹) ^ k * ((1 - z)⁻¹ ^ 2))) z := by
      have := (hd.pow (k + 1)).const_mul (k.factorial : ℂ)
      simpa using this
    rw [this.deriv]
    push_cast [Nat.factorial_succ]
    ring


/-- The coefficients `bₙ` of `log ζ(2 - z)`. -/
noncomputable def bseq : ℕ → ℝ
  | 0 => Real.log (zetaR 2)
  | n + 1 => (LSeries (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) 2).re /
      ((n + 1).factorial : ℝ)

/-- **Sharp truncation.** `∑_{n ≤ N} bₙ ≤ H_N + 11 (1/1.35)^(N+1) / (1 - 1/1.35)`. -/
theorem sharp_truncation (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), bseq n ≤
      ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n + 11 * (1 / 1.35) ^ (N + 1) / (1 - 1 / 1.35) := by
  set χ₁ : DirichletCharacter ℂ 1 := 1
  set Lf : ℂ → ℂ := LSeries (fun m => χ₁ m)
  have hLf : EqOn Lf (LSeries (fun m => χ₁ m)) {s | 1 < s.re} := fun _ _ => rfl
  set Gz : ℂ → ℂ := fun z => Lh z - Complex.log (1 - z)
  have hball1 : ∀ z ∈ ball (0 : ℂ) 1, ‖z‖ < 1 := fun z hz => by simpa using hz
  have hre1 : ∀ z ∈ ball (0 : ℂ) 1, 1 < (2 - z).re := fun z hz => by
    have := Complex.re_le_norm z; have := hball1 z hz; simp only [sub_re]; norm_num; linarith
  have hslit : ∀ z ∈ ball (0 : ℂ) 1, (1 - z) ∈ slitPlane := fun z hz => Or.inl (by
    have := Complex.re_le_norm z; have := hball1 z hz; simp only [sub_re, one_re]; linarith)
  have hLf_zeta : ∀ z ∈ ball (0 : ℂ) 1, Lf (2 - z) = riemannZeta (2 - z) := fun z hz => by
    simp only [Lf]
    rw [show (fun m : ℕ => χ₁ m) = 1 from funext fun m => chi1_apply m]
    exact LSeries_one_eq_riemannZeta (hre1 z hz)
  have hexpG : ∀ z ∈ ball (0 : ℂ) 1, Complex.exp (Gz z) = Lf (2 - z) := by
    intro z hz
    have h1z : (1 : ℂ) - z ≠ 0 := slitPlane_ne_zero (hslit z hz)
    simp only [Gz]
    rw [Complex.exp_sub, Complex.exp_log h1z, exp_Lh (by linarith [hball1 z hz]),
      h_eq_zeta (hball1 z hz), hLf_zeta z hz]
    field_simp
  have hGdiff : DifferentiableOn ℂ Gz (ball 0 1) := by
    intro z hz
    have hLh := Lh_differentiableOn z (ball_subset_ball (by norm_num) hz)
    exact (hLh.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by norm_num) hz))).sub
      (((differentiableAt_const _).sub differentiableAt_id).clog (hslit z hz)) |>.differentiableWithinAt
  have hGd : ∀ z ∈ ball (0 : ℂ) 1, HasDerivAt Gz (deriv (fun w => Lf (2 - w)) z / Lf (2 - z)) z := by
    intro z hz
    have hGz := (hGdiff.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hf0 : Lf (2 - z) ≠ 0 := by rw [← hexpG z hz]; exact Complex.exp_ne_zero _
    have hev : (fun w => Complex.exp (Gz w)) =ᶠ[𝓝 z] fun w => Lf (2 - w) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hexpG w hw
    have hd := hGz.cexp
    rw [hev.deriv_eq.symm, hd.deriv, hexpG z hz, mul_div_cancel_left₀ _ hf0]
    exact hGz
  -- coefficients of Gz
  have hcoefG : ∀ n, iteratedDeriv (n + 1) Gz 0 =
      LSeries (LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))) 2 := by
    intro n
    rw [iteratedDeriv_succ_log χ₁ one_pos hLf hGd n]
    congr 2; funext m; rw [chi1_apply, one_mul]
  have hG0 : Gz 0 = ((Real.log (zetaR 2) : ℝ) : ℂ) := by simp [Gz, Lh_zero]
  have hbseq : ∀ n, bseq n = (iteratedDeriv n Gz 0 / (n.factorial : ℂ)).re := by
    intro n; cases n with
    | zero => simp [bseq, hG0]
    | succ n =>
      rw [hcoefG, bseq, Complex.div_re]
      simp only [Complex.natCast_re, Complex.natCast_im, mul_zero, add_zero, Complex.normSq_natCast]
      field_simp
      ring
  -- analyticity near 0
  set φ : ℂ → ℂ := fun z => Complex.log (1 - z)
  have hφd : DifferentiableOn ℂ φ (ball 0 1) := fun z hz =>
    (((differentiableAt_const _).sub differentiableAt_id).clog (hslit z hz)).differentiableWithinAt
  have hLh0 : AnalyticAt ℂ Lh 0 := Lh_differentiableOn.analyticAt (ball_mem_nhds 0 (by norm_num))
  have hφ0 : AnalyticAt ℂ φ 0 := hφd.analyticAt (ball_mem_nhds 0 one_pos)
  have hsplit : ∀ n, iteratedDeriv n Gz 0 = iteratedDeriv n Lh 0 - iteratedDeriv n φ 0 := fun n =>
    iteratedDeriv_fun_sub (hLh0.contDiffAt) (hφ0.contDiffAt)
  -- coefficients of log(1 - z)
  have hφcoef : ∀ k : ℕ, iteratedDeriv (k + 1) φ 0 = -(k.factorial : ℂ) := by
    intro k
    have hev : deriv φ =ᶠ[𝓝 0] fun w => -((1 - w)⁻¹) := by
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with w hw
      have h := ((hasDerivAt_id' w).const_sub 1).clog (hslit w hw)
      rw [h.deriv]; simp [div_eq_mul_inv]
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, iteratedDeriv_fun_neg,
      iteratedDeriv_one_sub_inv k (by norm_num)]
    simp
  have hφsum : ∑ n ∈ Finset.range (N + 1), iteratedDeriv n φ 0 / (n.factorial : ℂ) =
      -((∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n : ℝ) : ℂ) := by
    rw [Finset.sum_range_succ']
    simp only [iteratedDeriv_zero, φ, sub_zero, Complex.log_one, zero_div, add_zero, hφcoef]
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [show N + 1 - 1 = N by omega]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.factorial_succ]; push_cast
    have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : (1 + (k : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 1 + k := by positivity
      exact_mod_cast this.ne'
    have hk' : ((k : ℂ) + 1) ≠ 0 := by rwa [add_comm]
    field_simp
    ring
  -- Taylor expansion of Lh at z = 1 and its tail
  have h1ball : (1 : ℂ) ∈ ball (0 : ℂ) 1.36 := by simp; norm_num
  have hTay := Complex.hasSum_taylorSeries_on_ball Lh_differentiableOn h1ball
  simp only [sub_zero, one_pow, one_smul] at hTay
  set c : ℕ → ℂ := fun n => ((n.factorial : ℂ))⁻¹ • iteratedDeriv n Lh 0
  have hc : ∀ n, ‖c n‖ ≤ 11 * (1 / 1.35) ^ n := by
    intro n
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1.35) (C := 11) n
      (by norm_num) (Lh_differentiableOn.diffContOnCl_ball (closedBall_subset_ball (by norm_num)))
      (fun z hz => norm_Lh_le (by rw [mem_sphere_zero_iff_norm] at hz; linarith))
    simp only [c, norm_smul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_le_iff₀ hf]
    calc ‖iteratedDeriv n Lh 0‖ ≤ n.factorial * 11 / 1.35 ^ n := hC
      _ = n.factorial * (11 * (1 / 1.35) ^ n) := by rw [one_div_pow]; ring
  have hcsum : Summable c := hTay.summable
  have hgeo : Summable fun n : ℕ => 11 * (1 / 1.35 : ℝ) ^ (n + (N + 1)) :=
    ((summable_geometric_of_lt_one (r := (1 / 1.35 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (11 * (1 / 1.35 : ℝ) ^ (N + 1))).congr
      fun n => by rw [pow_add]; ring
  have htail : ‖∑' n, c (n + (N + 1))‖ ≤ 11 * (1 / 1.35) ^ (N + 1) / (1 - 1 / 1.35) := by
    have hle : ∀ n, ‖c (n + (N + 1))‖ ≤ 11 * (1 / 1.35 : ℝ) ^ (n + (N + 1)) := fun n => hc _
    refine (norm_tsum_le_tsum_norm (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
      ((Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hgeo).trans (le_of_eq ?_))
    have : ∑' n : ℕ, 11 * (1 / 1.35 : ℝ) ^ (n + (N + 1)) = 11 * (1 / 1.35) ^ (N + 1) * ∑' n : ℕ, (1 / 1.35 : ℝ) ^ n := by
      rw [← tsum_mul_left]; congr 1; funext n; rw [pow_add]; ring
    rw [this, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
  have hLhsum : ∑ n ∈ Finset.range (N + 1), c n = -∑' n, c (n + (N + 1)) := by
    have := hcsum.sum_add_tsum_nat_add (N + 1)
    rw [hTay.tsum_eq, Lh_one] at this
    linear_combination this
  -- assemble
  have hsumG : ∑ n ∈ Finset.range (N + 1), iteratedDeriv n Gz 0 / (n.factorial : ℂ) =
      -∑' n, c (n + (N + 1)) + ((∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n : ℝ) : ℂ) := by
    simp_rw [hsplit, sub_div, Finset.sum_sub_distrib, hφsum]
    rw [← hLhsum]
    simp only [c, smul_eq_mul]
    ring_nf
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  calc ∑ n ∈ Finset.range (N + 1), bseq n
      = (∑ n ∈ Finset.range (N + 1), iteratedDeriv n Gz 0 / (n.factorial : ℂ)).re := by
        rw [Complex.re_sum]; exact Finset.sum_congr rfl fun n _ => hbseq n
    _ = (-∑' n, c (n + (N + 1))).re + ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
        rw [hsumG, Complex.add_re, Complex.ofReal_re]
    _ ≤ ‖∑' n, c (n + (N + 1))‖ + ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
        gcongr
        exact (Complex.re_le_norm _).trans (by rw [norm_neg])
    _ ≤ _ := by linarith

end QRHLittlewood
end


section

open Complex Metric Set LSeries Filter Topology

set_option autoImplicit false

namespace QRHLittlewood

/-- `‖L(f, x)‖ ≤ ζ(x)` for `‖f m‖ ≤ 1` and real `x > 1`. -/
lemma norm_LSeries_le_zetaR {f : ℕ → ℂ} (hf : ∀ m, ‖f m‖ ≤ 1) {x : ℝ} (hx : 1 < x) :
    ‖LSeries f (x : ℂ)‖ ≤ zetaR x := by
  have hsum := zetaR_summable hx
  have hle : ∀ m, ‖term f (x : ℂ) m‖ ≤ (if m = 0 then 0 else 1 / ((m : ℝ)) ^ x) := by
    intro m
    rw [norm_term_eq]
    split_ifs
    · rfl
    · simp only [ofReal_re]; gcongr; exact hf m
  have hb : Summable fun m : ℕ => (if m = 0 then (0 : ℝ) else 1 / ((m : ℝ)) ^ x) := by
    rw [← summable_nat_add_iff 1]
    refine hsum.congr fun m => ?_
    simp
  have hval : ∑' m : ℕ, (if m = 0 then (0 : ℝ) else 1 / ((m : ℝ)) ^ x) = zetaR x := by
    rw [hb.tsum_eq_zero_add, zetaR]; simp
  calc ‖LSeries f (x : ℂ)‖ ≤ ∑' m, ‖term f (x : ℂ) m‖ :=
        norm_tsum_le_tsum_norm (hb.of_nonneg_of_le (fun _ => norm_nonneg _) hle)
    _ ≤ _ := Summable.tsum_le_tsum hle (hb.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hb
    _ = zetaR x := hval

/-- `1/ζ(2) ≤ ‖L(χ, 2)‖`. -/
lemma norm_LSeries_two_ge {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    1 / zetaR 2 ≤ ‖LSeries (fun m => χ m) 2‖ := by
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ (s := 2) (by norm_num)
  set g : ℕ → ℂ := fun m => χ m * (ArithmeticFunction.moebius m : ℂ)
  have hg : ‖LSeries g ((2 : ℝ) : ℂ)‖ ≤ zetaR 2 := by
    refine norm_LSeries_le_zetaR (fun m => ?_) (by norm_num)
    simp only [g, norm_mul]
    have h2 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _) h2
  have hz0 : 0 < zetaR 2 := zetaR_pos (by norm_num)
  have h1 : ‖LSeries (fun m => χ m) 2‖ * ‖LSeries g 2‖ = 1 := by
    rw [← norm_mul]
    have : LSeries (fun m => χ m) 2 * LSeries g 2 = 1 := hmul
    rw [this, norm_one]
  have hg' : ‖LSeries g 2‖ ≤ zetaR 2 := by simpa using hg
  have hpos : 0 < ‖LSeries g 2‖ := by
    rcases (norm_nonneg (LSeries g 2)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at h1; exact absurd h1 zero_ne_one
  rw [div_le_iff₀ hz0]
  calc 1 = ‖LSeries (fun m => χ m) 2‖ * ‖LSeries g 2‖ := h1.symm
    _ ≤ ‖LSeries (fun m => χ m) 2‖ * zetaR 2 := by gcongr


/-- **Explicit core.** For a primitive real character `χ` modulo `q ≥ 3` with `L(s,χ) ≠ 0` on `Re s > 7/8`,
`L(1, χ) = e^u` with `|u| ≤ ∑_{n ≤ N} bₙ + 18 (A + B) (8/9)^{N+1}` for every `N`, where
`A = log 12 + (log q)/8` and `B = log ζ(2)`. -/
theorem explicit_core {q : ℕ} [NeZero q] (hq : 3 ≤ q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ u : ℝ, DirichletCharacter.LFunction χ 1 = (Real.exp u : ℂ) ∧ ∀ N : ℕ,
      |u| ≤ ∑ n ∈ Finset.range (N + 1), bseq n +
        18 * (Real.log 12 + Real.log q / 8 + Real.log (zetaR 2)) * (8 / 9) ^ (N + 1) := by
  have hq2 : 2 ≤ q := by omega
  have hχ1 : χ ≠ 1 := by
    rintro rfl; rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hprim; omega
  set Lf := DirichletCharacter.LFunction χ
  have hLf : EqOn Lf (LSeries (fun m => χ m)) {s | 1 < s.re} := fun s hs =>
    DirichletCharacter.LFunction_eq_LSeries χ hs
  set f : ℂ → ℂ := fun z => Lf (2 - z)
  have hball : ∀ z ∈ ball (0 : ℂ) (9 / 8), 7 / 8 < (2 - z).re := fun z hz => by
    have h' : ‖z‖ < 9 / 8 := by simpa using hz
    simp only [sub_re]; norm_num; linarith [abs_le.1 (Complex.abs_re_le_norm z)]
  have hLdiff : Differentiable ℂ Lf := DirichletCharacter.differentiable_LFunction hχ1
  have hfdiff : DifferentiableOn ℂ f (ball 0 (9 / 8)) := fun z _ =>
    ((hLdiff (2 - z)).comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 2 - w) z)).differentiableWithinAt
  have hfne : ∀ z ∈ ball (0 : ℂ) (9 / 8), f z ≠ 0 := fun z hz => hH _ (hball z hz)
  -- normalisation at s = 2: L(2) real in [1/ζ(2), ζ(2)]
  have hL2 : Lf 2 = LSeries (fun m => χ m) 2 := hLf (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  have hL2im : (Lf 2).im = 0 := by
    rw [hL2, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact LSeries_im_eq_zero (fun m => hreal m) 2
  have hL2near : ‖Lf 2 - 1‖ ≤ zetaR 2 - 1 := hL2 ▸ norm_LSeries_two_sub_one_le χ
  have hz2 := zetaR_two_lt
  have hz2pos : 0 < zetaR 2 := zetaR_pos (by norm_num)
  have hL2pos : 0 < (Lf 2).re := by
    have := Complex.abs_re_le_norm (Lf 2 - 1); simp at this; linarith [abs_le.1 (this.trans hL2near)]
  have hL2eq : Lf 2 = ((Lf 2).re : ℂ) := Complex.ext (by simp) (by simp [hL2im])
  have hL2norm : ‖Lf 2‖ = (Lf 2).re := by rw [hL2eq, Complex.norm_real, Real.norm_of_nonneg hL2pos.le]; simp
  have hL2up : (Lf 2).re ≤ zetaR 2 := by
    rw [← hL2norm, hL2, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact norm_LSeries_le_zetaR (fun m => DirichletCharacter.norm_le_one χ _) (by norm_num)
  have hL2lo : 1 / zetaR 2 ≤ (Lf 2).re := by rw [← hL2norm, hL2]; exact norm_LSeries_two_ge χ
  set ℓ2 : ℝ := Real.log (Lf 2).re
  set B : ℝ := Real.log (zetaR 2)
  have hℓ2 : |ℓ2| ≤ B := by
    rw [abs_le]; constructor
    · have := Real.log_le_log (by positivity) hL2lo
      rw [one_div, Real.log_inv] at this; linarith
    · exact Real.log_le_log hL2pos hL2up
  have hw0 : exp (ℓ2 : ℂ) = f 0 := by
    simp only [f, sub_zero]; rw [← Complex.ofReal_exp, Real.exp_log hL2pos, ← hL2eq]
  obtain ⟨F, hF0, hFd, hFexp⟩ := exists_log_on_ball hfdiff hfne (ℓ2 : ℂ) hw0 (by norm_num)
  have hFdiff : DifferentiableOn ℂ F (ball 0 (9 / 8)) := fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt
  -- Re F ≤ A on the disk
  set A : ℝ := Real.log 12 + Real.log q / 8
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hRe : ∀ z ∈ ball (0 : ℂ) (9 / 8), (F z).re ≤ A := by
    intro z hz
    have he := hFexp z hz
    have hn : ‖f z‖ ≤ 12 * (q : ℝ) ^ (1 / 8 : ℝ) := norm_LFunction_le_q_eighth hq2 hχ1 (by
      have : ‖z‖ < 9 / 8 := by simpa using hz
      simp only [sub_sub_cancel_left, norm_neg]; linarith)
    have : Real.exp (F z).re = ‖f z‖ := by rw [← he, Complex.norm_exp]
    rw [← Real.log_exp (F z).re, this]
    calc Real.log ‖f z‖ ≤ Real.log (12 * (q : ℝ) ^ (1 / 8 : ℝ)) :=
          Real.log_le_log (norm_pos_iff.2 (hfne z hz)) hn
      _ = A := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hqpos]; ring
  -- coefficients
  set a : ℕ → ℂ := fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0
  have h1ball : (1 : ℂ) ∈ ball (0 : ℂ) (9 / 8) := by simp; norm_num
  have hTay : HasSum a (F 1) := by
    have := Complex.hasSum_taylorSeries_on_ball hFdiff h1ball
    simpa [a, smul_eq_mul] using this
  have hcar : ∀ n, 1 ≤ n → ‖a n‖ ≤ 2 * (A + B) * (8 / 9) ^ n := by
    intro n hn
    have h := caratheodory_coeff (by norm_num) hFdiff hRe hn
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hRe0 : (F 0).re = ℓ2 := by rw [hF0]; simp
    simp only [a, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_eq_div]
    calc ‖iteratedDeriv n F 0‖ / n.factorial ≤ 2 * (A - (F 0).re) / (9 / 8) ^ n := h
      _ ≤ 2 * (A + B) * (8 / 9) ^ n := by
          rw [hRe0, div_eq_mul_inv, ← inv_pow, show ((9 : ℝ) / 8)⁻¹ = 8 / 9 by norm_num]
          gcongr; linarith [neg_abs_le ℓ2]
  have hdom : ∀ n, ‖a (n + 1)‖ ≤ bseq (n + 1) := by
    intro n
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    simp only [a, norm_mul, norm_inv, Complex.norm_natCast]
    rw [iteratedDeriv_succ_log χ (R := 9 / 8) (by norm_num) hLf hFd n, bseq, inv_mul_eq_div]
    gcongr
    have := norm_LSeries_logMul_twist_le χ n (s := 2) (by norm_num)
    simpa using this
  have hdom0 : ‖a 0‖ ≤ bseq 0 := by
    simp only [a, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero, hF0,
      Complex.norm_real, Real.norm_eq_abs, bseq]; exact hℓ2
  have hdomall : ∀ n, ‖a n‖ ≤ bseq n := fun n => by
    cases n with
    | zero => exact hdom0
    | succ n => exact hdom n
  -- reality of F(1)
  have hderivreal : ∀ t : ℝ, |t| < 1 → (deriv F t).im = 0 := by
    intro t ht
    have htb : (t : ℂ) ∈ ball (0 : ℂ) (9 / 8) := by simp; linarith [abs_lt.1 ht]
    have h1 : 1 < (2 - (t : ℂ)).re := by simp; linarith [abs_lt.1 ht]
    rw [(hFd t htb).deriv, logderiv_formula χ hLf h1,
      show (2 : ℂ) - (t : ℂ) = ((2 - t : ℝ) : ℂ) by push_cast; ring]
    exact LSeries_im_eq_zero (fun m => by simp [hreal m]) _
  have hreal01 := im_eq_zero_of_real_deriv (F := F) (R := 1)
    (fun t ht => (hFd t (by simp; linarith [abs_lt.1 ht])).differentiableAt.hasDerivAt)
    hderivreal (by simp [hF0])
  have hF1im : (F 1).im = 0 := by
    have hc : ContinuousAt (fun t : ℝ => (F t).im) 1 := by
      have : ContinuousAt F ((1 : ℝ) : ℂ) := (hFd 1 (by simpa using h1ball)).differentiableAt.continuousAt
      exact (Complex.continuous_im.continuousAt.comp this).comp Complex.continuous_ofReal.continuousAt
    have hlim : Tendsto (fun t : ℝ => (F t).im) (nhdsWithin 1 (Set.Iio 1)) (nhds ((F ((1 : ℝ) : ℂ)).im)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun t : ℝ => (F t).im) =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact hreal01 t (abs_lt.2 ⟨by linarith [ht.1], ht.2⟩)
    have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
    simpa using this
  refine ⟨(F 1).re, ?_, fun N => ?_⟩
  · have he := hFexp 1 h1ball
    have hf1 : f 1 = Lf 1 := by show Lf (2 - 1) = Lf 1; norm_num
    rw [show F 1 = ((F 1).re : ℂ) from Complex.ext (by simp) (by simp [hF1im]), ← Complex.ofReal_exp] at he
    show Lf 1 = _
    rw [← hf1, ← he]
  · -- |F(1)| ≤ partial + tail
    have hsumm := hTay.summable
    have hsplit := hsumm.sum_add_tsum_nat_add (N + 1)
    rw [hTay.tsum_eq] at hsplit
    have hgeo : Summable fun n : ℕ => 2 * (A + B) * (8 / 9 : ℝ) ^ (n + (N + 1)) :=
      ((summable_geometric_of_lt_one (r := (8 / 9 : ℝ)) (by norm_num) (by norm_num)).mul_left
        (2 * (A + B) * (8 / 9) ^ (N + 1))).congr fun n => by rw [pow_add]; ring
    have hle : ∀ n, ‖a (n + (N + 1))‖ ≤ 2 * (A + B) * (8 / 9 : ℝ) ^ (n + (N + 1)) := fun n =>
      hcar _ (by omega)
    have htail : ‖∑' n, a (n + (N + 1))‖ ≤ 18 * (A + B) * (8 / 9) ^ (N + 1) := by
      refine (norm_tsum_le_tsum_norm (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
        ((Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hgeo).trans (le_of_eq ?_))
      have : ∑' n : ℕ, 2 * (A + B) * (8 / 9 : ℝ) ^ (n + (N + 1)) =
          2 * (A + B) * (8 / 9) ^ (N + 1) * ∑' n : ℕ, (8 / 9 : ℝ) ^ n := by
        rw [← tsum_mul_left]; congr 1; funext n; rw [pow_add]; ring
      rw [this, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
    have hpart : ‖∑ n ∈ Finset.range (N + 1), a n‖ ≤ ∑ n ∈ Finset.range (N + 1), bseq n :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => hdomall n)
    calc |(F 1).re| ≤ ‖F 1‖ := Complex.abs_re_le_norm _
      _ = ‖∑ n ∈ Finset.range (N + 1), a n + ∑' n, a (n + (N + 1))‖ := by rw [hsplit]
      _ ≤ ‖∑ n ∈ Finset.range (N + 1), a n‖ + ‖∑' n, a (n + (N + 1))‖ := norm_add_le _ _
      _ ≤ _ := by simp only [A, B] at htail ⊢; linarith

end QRHLittlewood
end


section

open Real Finset

set_option autoImplicit false

namespace QRHLittlewood

lemma exp_ge_of_sum {x y : ℝ} (hx : 0 ≤ x) (n : ℕ) (h : y ≤ ∑ i ∈ range n, x ^ i / i.factorial) :
    y ≤ Real.exp x := h.trans (Real.sum_le_exp_of_nonneg hx n)

lemma exp_le_small {x y : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) (hn : 0 < n)
    (h : (∑ m ∈ range n, x ^ m / m.factorial) + x ^ n * (n + 1) / (n.factorial * n) ≤ y) :
    Real.exp x ≤ y := (Real.exp_bound' h0 h1 hn).trans h

lemma log_nine_eighths_ge : 0.1177 ≤ Real.log (9 / 8) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  refine exp_le_small (by norm_num) (by norm_num) 6 (by norm_num) ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma log_nine_eighths_le : Real.log (9 / 8) ≤ 0.1178 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 6 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma neg_log_a_le : -Real.log (Real.log (9 / 8)) ≤ 2.1397 := by
  have ha := log_nine_eighths_ge
  rw [neg_le, Real.le_log_iff_exp_le (by linarith)]
  have h : Real.exp (-2.1397) ≤ 0.1177 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    refine exp_ge_of_sum (by norm_num) 16 ?_
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num
  linarith

lemma log_ten_ge : 2.3025 ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 2.3025 = Real.exp 1 ^ 2 * Real.exp 0.3025 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp 0.3025 ≤ 1.35324 := by
    refine exp_le_small (by norm_num) (by norm_num) 8 (by norm_num) ?_
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num
  rw [h1]
  have h3 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := by gcongr
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.3025]

lemma log_q_ge {q : ℝ} (hq : (10 : ℝ) ^ 100 ≤ q) : 230.25 ≤ Real.log q := by
  have h := Real.log_le_log (by positivity) hq
  rw [Real.log_pow] at h
  have := log_ten_ge
  push_cast at h; linarith

lemma t_ge {q : ℝ} (hq : (10 : ℝ) ^ 100 ≤ q) : 5.4391 ≤ Real.log (Real.log q) := by
  have h := log_q_ge hq
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 : Real.exp 5.4391 = Real.exp 1 ^ 5 * Real.exp 0.4391 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp 0.4391 ≤ 1.551338 := by
    refine exp_le_small (by norm_num) (by norm_num) 9 (by norm_num) ?_
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num
  have h3 : Real.exp 1 ^ 5 ≤ 2.7182818286 ^ 5 := by gcongr
  rw [h1]
  calc Real.exp 1 ^ 5 * Real.exp 0.4391 ≤ 2.7182818286 ^ 5 * 1.551338 := by
        gcongr
    _ ≤ 230.25 := by norm_num
    _ ≤ Real.log q := h

lemma exp_neg_22_le : Real.exp (-2.2) ≤ 0.1109 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 14 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma log_twelve_le : Real.log 12 ≤ 2.4851 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 16 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma log_five_thirds_le : Real.log (5 / 3) ≤ 0.5109 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 9 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma log_one_add_le : Real.log (1 + 3.011 / 5.4391) ≤ 0.44062 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 10 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma h64_le : eulerMascheroniSeq' 64 ≤ 0.58504 := by
  rw [eulerMascheroniSeq', if_neg (by norm_num)]
  have hl : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hH : (harmonic 64 : ℝ) ≤ 4.743891 := by
    have : harmonic 64 ≤ (4743891 / 1000000 : ℚ) := by
      simp only [harmonic, sum_range_succ, sum_range_zero]; norm_num
    have h' : (harmonic 64 : ℝ) ≤ ((4743891 / 1000000 : ℚ) : ℝ) := by exact_mod_cast this
    norm_num at h' ⊢
  push_cast
  rw [hl]; linarith

lemma harmonic_sub_log_le {N : ℕ} (hN : 64 ≤ N) : (harmonic N : ℝ) - Real.log N ≤ 0.58504 := by
  have h := Real.strictAnti_eulerMascheroniSeq'.antitone hN
  rw [eulerMascheroniSeq', if_neg (by omega)] at h
  exact h.trans h64_le

end QRHLittlewood
end


section

open Finset

set_option autoImplicit false

namespace QRHLittlewood

/-- Truncated exponential `E_N(u) = ∑_{n ≤ N} uⁿ/n!`. -/
noncomputable def EN (N : ℕ) (u : ℝ) : ℝ := ∑ n ∈ range (N + 1), u ^ n / n.factorial

lemma EN_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ EN N u :=
  sum_nonneg fun n _ => by positivity

lemma EN_le_exp (N : ℕ) {u : ℝ} (hu : 0 ≤ u) : EN N u ≤ Real.exp u :=
  Real.sum_le_exp_of_nonneg hu (N + 1)

/-- `E_N(u + v) ≤ eᵛ E_N(u)` for `u, v ≥ 0`. -/
lemma EN_add_le (N : ℕ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    EN N (u + v) ≤ Real.exp v * EN N u := by
  have h1 : EN N (u + v) = ∑ n ∈ range (N + 1), ∑ i ∈ range (n + 1),
      u ^ i / i.factorial * (v ^ (n - i) / (n - i).factorial) := by
    unfold EN
    refine sum_congr rfl fun n _ => ?_
    rw [add_pow, sum_div]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
    rw [Nat.cast_choose ℝ hi']
    have := Nat.factorial_pos i; have := Nat.factorial_pos (n - i); have := Nat.factorial_pos n
    field_simp
  rw [h1, sum_range_diag_flip (N + 1) (fun i j => u ^ i / i.factorial * (v ^ j / j.factorial)), EN, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [← mul_sum, mul_comm (Real.exp v)]
  exact mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hv _) (by positivity)

/-- `eᵘ - E_N(u) ≤ (4/5)^{N+1} e^{5u/4}` for `u ≥ 0`. -/
lemma exp_sub_EN_le (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp u - EN N u ≤ (4 / 5) ^ (N + 1) * Real.exp (5 / 4 * u) := by
  have hE : ∀ x : ℝ, HasSum (fun n => x ^ n / n.factorial) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  set f : ℕ → ℝ := fun n => if n ∈ range (N + 1) then u ^ n / n.factorial else 0
  have hfin : HasSum f (EN N u) := by
    have : HasSum f (∑ n ∈ range (N + 1), f n) := hasSum_sum_of_ne_finset_zero (fun n hn => if_neg hn)
    convert this using 1
    exact sum_congr rfl fun n hn => (if_pos hn).symm
  refine hasSum_le (fun n => ?_) ((hE u).sub hfin) ((hE (5 / 4 * u)).mul_left ((4 / 5) ^ (N + 1)))
  simp only [f]
  split_ifs with hn
  · simp only [sub_self]; positivity
  · have hn' : N + 1 ≤ n := by simpa using hn
    rw [sub_zero, mul_pow, ← mul_div_assoc, ← mul_assoc]
    have h1 : (1 : ℝ) ≤ (4 / 5) ^ (N + 1) * (5 / 4) ^ n := by
      calc (1 : ℝ) = (4 / 5) ^ (N + 1) * (5 / 4) ^ (N + 1) := by rw [← mul_pow]; norm_num
        _ ≤ (4 / 5) ^ (N + 1) * (5 / 4) ^ n := by gcongr; norm_num
    have : 0 ≤ u ^ n / n.factorial := by positivity
    calc u ^ n / n.factorial = 1 * u ^ n / n.factorial := by ring
      _ ≤ (4 / 5) ^ (N + 1) * (5 / 4) ^ n * u ^ n / n.factorial := by gcongr

/-- **Pairing lemma.** For `t ≥ 0` nonincreasing and summable, and `c ∈ {-1, 0, 1}`,
`2 ∑ⱼ t(2j+1) ≤ ∑ₖ c^{k+1} t(k) + ∑ₖ t(k)`. -/
lemma pair_ineq {t : ℕ → ℝ} (h0 : ∀ k, 0 ≤ t k) (hanti : ∀ k, t (k + 1) ≤ t k) (hs : Summable t)
    {c : ℝ} (hc : c = -1 ∨ c = 0 ∨ c = 1) :
    ∑' j, 2 * t (2 * j + 1) ≤ ∑' k, c ^ (k + 1) * t k + ∑' k, t k := by
  have hc1 : |c| ≤ 1 := by rcases hc with rfl | rfl | rfl <;> norm_num
  have hcs : Summable fun k => c ^ (k + 1) * t k := by
    refine hs.of_norm_bounded fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (h0 k)]
    exact mul_le_of_le_one_left (h0 k) (pow_le_one₀ (abs_nonneg c) hc1)
  have hev : ∀ {g : ℕ → ℝ}, Summable g → Summable fun j => g (2 * j) := fun hg =>
    hg.comp_injective (fun a b h => by simpa using h)
  have hod : ∀ {g : ℕ → ℝ}, Summable g → Summable fun j => g (2 * j + 1) := fun hg =>
    hg.comp_injective (fun a b h => by simpa using h)
  rw [← tsum_even_add_odd (hev hcs) (hod hcs), ← tsum_even_add_odd (hev hs) (hod hs),
    ← Summable.tsum_add (hev hcs) (hod hcs), ← Summable.tsum_add (hev hs) (hod hs),
    ← Summable.tsum_add ((hev hcs).add (hod hcs)) ((hev hs).add (hod hs))]
  refine Summable.tsum_le_tsum (fun j => ?_) ((hod hs).mul_left 2)
    (((hev hcs).add (hod hcs)).add ((hev hs).add (hod hs)))
  have := hanti (2 * j); have := h0 (2 * j); have := h0 (2 * j + 1)
  rcases hc with rfl | rfl | rfl
  · rw [show 2 * j + 1 = 2 * j + 1 from rfl, pow_succ, pow_mul, show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
      pow_mul]; norm_num; linarith
  · simp; linarith
  · simp; linarith

/-- Reindexing a sum supported on prime powers as a double sum over primes and exponents. -/
lemma tsum_primes_pow' {g : ℕ → ℝ} (hg : Summable g) (hsupp : ∀ n, ¬ IsPrimePow n → g n = 0) :
    (∀ p : Nat.Primes, Summable fun k => g ((p : ℕ) ^ (k + 1))) ∧
    Summable (fun p : Nat.Primes => ∑' k, g ((p : ℕ) ^ (k + 1))) ∧
    ∑' n, g n = ∑' (p : Nat.Primes) (k : ℕ), g ((p : ℕ) ^ (k + 1)) := by
  set φ : Nat.Primes × ℕ → ℕ := fun pk => ((Nat.Primes.prodNatEquiv pk : {n // IsPrimePow n}) : ℕ)
  have hφ : ∀ pk : Nat.Primes × ℕ, φ pk = (pk.1 : ℕ) ^ (pk.2 + 1) := fun pk => by
    obtain ⟨p, k⟩ := pk; exact Nat.Primes.coe_prodNatEquiv_apply p k
  have hinj : Function.Injective φ := Subtype.val_injective.comp Nat.Primes.prodNatEquiv.injective
  have hS : Summable (g ∘ φ) := hg.comp_injective hinj
  have hS' : Summable fun pk : Nat.Primes × ℕ => g ((pk.1 : ℕ) ^ (pk.2 + 1)) := by
    convert hS using 2 with pk; simp [hφ]
  refine ⟨fun p => hS'.prod_factor p, hS'.prod, ?_⟩
  rw [← hS'.tsum_prod' (fun p => hS'.prod_factor p)]
  have hsub : Function.support g ⊆ {n | IsPrimePow n} := fun n hn => by
    by_contra h; exact hn (hsupp n h)
  rw [← tsum_subtype_eq_of_support_subset hsub]
  have he := Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun x : {n // IsPrimePow n} => g x)
  exact he.symm.trans (tsum_congr fun pk => congrArg g (hφ pk))

end QRHLittlewood
end


section

open Finset LSeries

set_option autoImplicit false

namespace QRHLittlewood

lemma vonMangoldt_eq_zero_of_log {m : ℕ} (h : Real.log m = 0) : ArithmeticFunction.vonMangoldt m = 0 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> simp
  · exfalso
    have : (1 : ℝ) < m := by exact_mod_cast hm
    exact (Real.log_pos this).ne' h

lemma vonMangoldt_div_log_le (m : ℕ) :
    ArithmeticFunction.vonMangoldt m / Real.log m ≤ 1 := by
  rcases eq_or_ne (Real.log m) 0 with h | h
  · simp [h]
  · have hpos : 0 < Real.log m := by
      rcases (Real.log_nonneg (x := m) (by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at h
        · exact_mod_cast hm)).lt_or_eq with h' | h'
      · exact h'
      · exact absurd h'.symm h
    rw [div_le_one hpos]; exact ArithmeticFunction.vonMangoldt_le_log

/-- `cₙ(m) = f(m) Λ(m) (log m)ⁿ / (n! m² log m)`. -/
noncomputable def cterm (f : ℕ → ℝ) (n m : ℕ) : ℝ :=
  f m * ArithmeticFunction.vonMangoldt m * Real.log m ^ n / (n.factorial * (m : ℝ) ^ 2 * Real.log m)

/-- `τ(m) = f(m) Λ(m) E_N(log m) / (m² log m)`. -/
noncomputable def tauN (f : ℕ → ℝ) (N m : ℕ) : ℝ :=
  f m * ArithmeticFunction.vonMangoldt m * EN N (Real.log m) / ((m : ℝ) ^ 2 * Real.log m)

/-- `g(m) = Λ(m) E_N(2 log m) / (m⁴ log m)`. -/
noncomputable def gainN (N m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m * EN N (2 * Real.log m) / ((m : ℝ) ^ 4 * Real.log m)

lemma tauN_eq_sum (f : ℕ → ℝ) (N m : ℕ) : tauN f N m = ∑ n ∈ range (N + 1), cterm f n m := by
  simp only [tauN, cterm, EN, mul_sum, sum_div]
  refine sum_congr rfl fun n _ => ?_
  ring

lemma cterm_succ (f : ℕ → ℝ) (n m : ℕ) :
    cterm f (n + 1) m = f m * ArithmeticFunction.vonMangoldt m * Real.log m ^ n / (m : ℝ) ^ 2 /
      ((n + 1).factorial : ℝ) := by
  rcases eq_or_ne (Real.log m) 0 with h | h
  · simp [cterm, vonMangoldt_eq_zero_of_log h]
  · have hm : (m : ℝ) ≠ 0 := by rintro hm; rw [hm, Real.log_zero] at h; exact h rfl
    have := Nat.factorial_pos (n + 1)
    simp only [cterm]
    field_simp
    ring

lemma cterm_one_nonneg (n m : ℕ) : 0 ≤ cterm (fun _ => 1) n m := by
  have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cterm]
  · have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
    simp only [cterm]; positivity

lemma abs_cterm_le {f : ℕ → ℝ} (hf : ∀ m, |f m| ≤ 1) (n m : ℕ) :
    |cterm f n m| ≤ cterm (fun _ => 1) n m := by
  have h1 := cterm_one_nonneg n m
  have : cterm f n m = f m * cterm (fun _ => 1) n m := by simp only [cterm]; ring
  rw [this, abs_mul, abs_of_nonneg h1]
  exact mul_le_of_le_one_left h1 (hf m)

lemma summable_cterm_one_zero : Summable (cterm (fun _ => 1) 0) := by
  refine (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)).of_nonneg_of_le
    (cterm_one_nonneg 0) fun m => ?_
  have h := vonMangoldt_div_log_le m
  simp only [cterm, one_mul, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
  rw [show ArithmeticFunction.vonMangoldt m / ((m : ℝ) ^ 2 * Real.log m) =
      (ArithmeticFunction.vonMangoldt m / Real.log m) * (1 / (m : ℝ) ^ 2) by ring]
  exact mul_le_of_le_one_left (by positivity) h

lemma summable_vonMangoldt_logpow (n : ℕ) :
    Summable fun m : ℕ => ArithmeticFunction.vonMangoldt m * Real.log m ^ n / (m : ℝ) ^ 2 := by
  set g : ℕ → ℂ := LSeries.logMul^[n] (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
  have hgsum : LSeriesSummable g ((2 : ℝ) : ℂ) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    rw [LSeries.absicssaOfAbsConv_logPowMul]
    exact lt_of_le_of_lt abscissa_vonMangoldt_le_one
      (by simpa using (EReal.coe_lt_coe_iff.2 (by norm_num : (1 : ℝ) < 2)))
  refine hgsum.norm.congr fun m => ?_
  rw [term_logMul_vonMangoldt_real, Complex.norm_real,
    Real.norm_of_nonneg (term_logMul_vonMangoldt_nonneg n 2 m)]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [if_neg hm, Real.rpow_two]; ring

lemma summable_cterm_one (n : ℕ) : Summable (cterm (fun _ => 1) n) := by
  cases n with
  | zero => exact summable_cterm_one_zero
  | succ n =>
    refine ((summable_vonMangoldt_logpow n).div_const ((n + 1).factorial : ℝ)).congr fun m => ?_
    rw [cterm_succ]; ring

lemma summable_cterm {f : ℕ → ℝ} (hf : ∀ m, |f m| ≤ 1) (n : ℕ) : Summable (cterm f n) :=
  (summable_cterm_one n).of_norm_bounded fun m => by rw [Real.norm_eq_abs]; exact abs_cterm_le hf n m

lemma summable_tauN {f : ℕ → ℝ} (hf : ∀ m, |f m| ≤ 1) (N : ℕ) : Summable (tauN f N) := by
  have : tauN f N = fun m => ∑ n ∈ range (N + 1), cterm f n m := funext (tauN_eq_sum f N)
  rw [this]; exact summable_sum fun n _ => summable_cterm hf n

/-- `∑ τ = ∑ c₀ + ∑_{n < N} (∑ f Λ logⁿ / m²) / (n+1)!`. -/
lemma tsum_tauN {f : ℕ → ℝ} (hf : ∀ m, |f m| ≤ 1) (N : ℕ) :
    ∑' m, tauN f N m = ∑' m, cterm f 0 m + ∑ n ∈ range N,
      (∑' m, f m * ArithmeticFunction.vonMangoldt m * Real.log m ^ n / (m : ℝ) ^ 2) /
        ((n + 1).factorial : ℝ) := by
  rw [show (fun m => tauN f N m) = fun m => ∑ n ∈ range (N + 1), cterm f n m from funext (tauN_eq_sum f N),
    Summable.tsum_finsetSum fun n _ => summable_cterm hf n, sum_range_succ']
  rw [add_comm]; congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [← tsum_div_const]; exact tsum_congr fun m => (cterm_succ f n m)

lemma gainN_nonneg (N m : ℕ) : 0 ≤ gainN N m := by
  have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [gainN]
  · have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
    have := EN_nonneg N (u := 2 * Real.log m) (by positivity)
    simp only [gainN]; positivity

lemma gainN_le (N m : ℕ) : gainN N m ≤ cterm (fun _ => 1) 0 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [gainN, cterm]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hl : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hE : EN N (2 * Real.log m) ≤ (m : ℝ) ^ 2 := by
    calc EN N (2 * Real.log m) ≤ Real.exp (2 * Real.log m) := EN_le_exp N (by positivity)
      _ = (m : ℝ) ^ 2 := by
        rw [show 2 * Real.log m = (2 : ℕ) * Real.log m by norm_num, Real.exp_nat_mul, Real.exp_log hm']
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := m)
  simp only [gainN, cterm, one_mul, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
  rw [show (m : ℝ) ^ 4 = (m : ℝ) ^ 2 * (m : ℝ) ^ 2 by ring]
  rw [show ArithmeticFunction.vonMangoldt m * EN N (2 * Real.log m) / ((m : ℝ) ^ 2 * (m : ℝ) ^ 2 * Real.log m) =
      ArithmeticFunction.vonMangoldt m / ((m : ℝ) ^ 2 * Real.log m) * (EN N (2 * Real.log m) / (m : ℝ) ^ 2) by
    field_simp]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 hE)

lemma summable_gainN (N : ℕ) : Summable (gainN N) :=
  (summable_cterm_one 0).of_nonneg_of_le (gainN_nonneg N) (gainN_le N)

/-- Per-prime weights `t_p(k) = E_N((k+1) log p) / ((k+1) p^{2(k+1)})`. -/
noncomputable def tp (N : ℕ) (p : ℕ) (k : ℕ) : ℝ :=
  EN N ((k + 1) * Real.log p) / ((k + 1) * (p : ℝ) ^ (2 * (k + 1)))

lemma tauN_prime_pow (f : ℕ → ℝ) (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    tauN f N (p ^ (k + 1)) = f (p ^ (k + 1)) * tp N p k := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [tauN, tp, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  push_cast
  rw [← pow_mul, mul_comm 2 (k + 1)]
  field_simp

lemma gainN_prime_pow (N : ℕ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    gainN N (p ^ (j + 1)) = 2 * tp N p (2 * j + 1) := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  simp only [gainN, tp, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero j),
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  push_cast
  rw [show (2 : ℝ) * ((j + 1 : ℝ) * Real.log p) = (2 * j + 1 + 1) * Real.log p by ring,
    ← pow_mul, show 2 * (2 * j + 1 + 1) = (j + 1) * 4 by ring]
  field_simp
  ring

lemma tp_nonneg (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) : 0 ≤ tp N p k := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have := EN_nonneg N (u := (k + 1) * Real.log p) (by positivity)
  simp only [tp]; positivity

lemma tp_anti (N : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) : tp N p (k + 1) ≤ tp N p k := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  set L := Real.log p
  set E := EN N ((k + 1) * L)
  have hE : 0 ≤ E := EN_nonneg N (by positivity)
  have hadd : EN N (((k + 1 : ℕ) + 1 : ℝ) * L) ≤ p * E := by
    have := EN_add_le N (u := (k + 1) * L) (v := L) (by positivity) hl.le
    rw [Real.exp_log (by linarith)] at this
    convert this using 2; push_cast; ring
  set P : ℝ := (p : ℝ) ^ (2 * (k + 1))
  have hP : 0 < P := by positivity
  have hPs : (p : ℝ) ^ (2 * (k + 1 + 1)) = P * p ^ 2 := by
    rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 2 by ring, pow_add]
  simp only [tp]
  rw [hPs]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc EN N (((k + 1 : ℕ) + 1 : ℝ) * L) / (((k + 1 : ℕ) + 1 : ℝ) * (P * p ^ 2))
      ≤ p * E / (((k + 1 : ℕ) + 1 : ℝ) * (P * p ^ 2)) := by gcongr
    _ ≤ E / ((k + 1) * P) := by
        push_cast
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have key : (p : ℝ) * (k + 1) ≤ (k + 1 + 1) * p ^ 2 := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k + 1) (by nlinarith : (0 : ℝ) ≤ (p : ℝ) ^ 2 - p)]
        have := mul_le_mul_of_nonneg_left key (mul_nonneg hE hP.le)
        nlinarith

end QRHLittlewood
end


section

open Finset LSeries

set_option autoImplicit false

namespace QRHLittlewood

/-- **Sign inequality.** For `c` with `c(p) ∈ {-1, 0, 1}` on primes and `c(p^{k+1}) = c(p)^{k+1}`,
`∑ g ≤ ∑ τ_c + ∑ τ_1`. -/
theorem sign_ineq (c : ℕ → ℝ) (hcb : ∀ m, |c m| ≤ 1)
    (hcp : ∀ p : ℕ, p.Prime → c p = -1 ∨ c p = 0 ∨ c p = 1)
    (hmul : ∀ p k : ℕ, c (p ^ (k + 1)) = c p ^ (k + 1)) (N : ℕ) :
    ∑' m, gainN N m ≤ ∑' m, tauN c N m + ∑' m, tauN (fun _ => 1) N m := by
  have hsupp : ∀ {g : ℕ → ℝ}, (∀ m, ArithmeticFunction.vonMangoldt m = 0 → g m = 0) →
      ∀ n, ¬ IsPrimePow n → g n = 0 :=
    fun hg n hn => hg n (ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hn)
  have h1b : ∀ m, |(fun _ : ℕ => (1 : ℝ)) m| ≤ 1 := fun m => by simp
  obtain ⟨-, hgs, hge⟩ := tsum_primes_pow' (summable_gainN N) (hsupp fun m h => by simp [gainN, h])
  obtain ⟨-, hcs, hce⟩ := tsum_primes_pow' (summable_tauN hcb N) (hsupp fun m h => by simp [tauN, h])
  obtain ⟨h1f, h1s, h1e⟩ := tsum_primes_pow' (summable_tauN h1b N) (hsupp fun m h => by simp [tauN, h])
  rw [hge, hce, h1e, ← Summable.tsum_add hcs h1s]
  refine Summable.tsum_le_tsum (fun p => ?_) hgs (hcs.add h1s)
  have hp : (p : ℕ).Prime := p.prop
  have hts : Summable (tp N p) := by
    have := h1f p; simpa [tauN_prime_pow _ N hp] using this
  have e1 : ∀ j, gainN N ((p : ℕ) ^ (j + 1)) = 2 * tp N p (2 * j + 1) := gainN_prime_pow N hp
  have e2 : ∀ k, tauN c N ((p : ℕ) ^ (k + 1)) = c p ^ (k + 1) * tp N p k := fun k => by
    rw [tauN_prime_pow _ N hp, hmul]
  have e3 : ∀ k, tauN (fun _ => 1) N ((p : ℕ) ^ (k + 1)) = tp N p k := fun k => by
    rw [tauN_prime_pow _ N hp, one_mul]
  simp only [e1, e2, e3]
  exact pair_ineq (tp_nonneg N hp) (tp_anti N hp) hts (hcp p hp)

lemma log_natCast_nonneg' (m : ℕ) : 0 ≤ Real.log m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hm)

lemma log_zetaR_eq {s : ℝ} (hs : 1 < s) : Real.log (zetaR s) =
    ∑' m : ℕ, ArithmeticFunction.vonMangoldt m / ((m : ℝ) ^ s * Real.log m) := by
  rw [← riemannZeta_re_eq_zetaR hs, log_riemannZeta_eq hs]

lemma log_zetaR_two_eq : Real.log (zetaR 2) = ∑' m, cterm (fun _ => 1) 0 m := by
  rw [log_zetaR_eq (by norm_num)]
  refine tsum_congr fun m => ?_
  simp [cterm, Real.rpow_two]

/-- `log ζ(2) - ∑ g ≤ (4/5)^{N+1} log 3`. -/
theorem B_sub_gain_le (N : ℕ) :
    ∑' m, cterm (fun _ => 1) 0 m - ∑' m, gainN N m ≤ (4 / 5) ^ (N + 1) * Real.log 3 := by
  set h : ℕ → ℝ := fun m => ArithmeticFunction.vonMangoldt m / ((m : ℝ) ^ (3 / 2 : ℝ) * Real.log m)
  have hz : Real.log (zetaR (3 / 2)) = ∑' m, h m := log_zetaR_eq (by norm_num)
  have hhs : Summable h := by
    refine (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3 / 2)).of_nonneg_of_le
      (fun m => ?_) (fun m => ?_)
    · have := ArithmeticFunction.vonMangoldt_nonneg (n := m)
      have := log_natCast_nonneg' m
      simp only [h]; positivity
    · have h1 := vonMangoldt_div_log_le m
      simp only [h]
      rw [show ArithmeticFunction.vonMangoldt m / ((m : ℝ) ^ (3 / 2 : ℝ) * Real.log m) =
        (ArithmeticFunction.vonMangoldt m / Real.log m) * (1 / (m : ℝ) ^ (3 / 2 : ℝ)) by ring]
      exact mul_le_of_le_one_left (by positivity) h1
  have hterm : ∀ m, cterm (fun _ => 1) 0 m - gainN N m ≤ (4 / 5) ^ (N + 1) * h m := by
    intro m
    rcases eq_or_ne (Real.log m) 0 with hl | hl
    · simp [cterm, gainN, h, hl]
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hl
      · exact hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hlpos : 0 < Real.log m := lt_of_le_of_ne (log_natCast_nonneg' m) (Ne.symm hl)
    set ℓ := Real.log m
    set y := Real.exp (ℓ / 2)
    have hy : 0 < y := Real.exp_pos _
    have hpow : ∀ k : ℕ, Real.exp (k * (ℓ / 2)) = y ^ k := fun k => Real.exp_nat_mul _ k
    have hmy : (m : ℝ) = y ^ 2 := by
      rw [← hpow 2, show ((2 : ℕ) : ℝ) * (ℓ / 2) = ℓ by push_cast; ring, Real.exp_log hm']
    have h32 : (m : ℝ) ^ (3 / 2 : ℝ) = y ^ 3 := by
      rw [Real.rpow_def_of_pos hm', ← hpow 3]; congr 1; push_cast; ring
    have hE := exp_sub_EN_le N (u := 2 * ℓ) (by positivity)
    rw [show 2 * ℓ = ((4 : ℕ) : ℝ) * (ℓ / 2) by push_cast; ring, hpow,
      show 5 / 4 * (((4 : ℕ) : ℝ) * (ℓ / 2)) = ((5 : ℕ) : ℝ) * (ℓ / 2) by push_cast; ring, hpow] at hE
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    set E := EN N (((4 : ℕ) : ℝ) * (ℓ / 2))
    have hEeq : EN N (2 * ℓ) = E := by congr 1; push_cast; ring
    have h2 : (m : ℝ) ^ 2 = y ^ 4 := by rw [hmy]; ring
    have h4 : (m : ℝ) ^ 4 = y ^ 8 := by rw [hmy]; ring
    simp only [cterm, gainN, h, one_mul, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    rw [h2, h4, h32, hEeq]
    set Λm := ArithmeticFunction.vonMangoldt m
    have key : Λm / (y ^ 4 * ℓ) - Λm * E / (y ^ 8 * ℓ) - (4 / 5) ^ (N + 1) * (Λm / (y ^ 3 * ℓ)) =
        Λm / (y ^ 8 * ℓ) * (y ^ 4 - E - (4 / 5) ^ (N + 1) * y ^ 5) := by
      field_simp
    have : Λm / (y ^ 8 * ℓ) * (y ^ 4 - E - (4 / 5) ^ (N + 1) * y ^ 5) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hz3 : Real.log (zetaR (3 / 2)) ≤ Real.log 3 := by
    have hu := zetaR_upper (x := 3 / 2) (by norm_num)
    exact Real.log_le_log (zetaR_pos (by norm_num)) (by norm_num at hu; linarith)
  have hsub : Summable fun m => cterm (fun _ => 1) 0 m - gainN N m :=
    (summable_cterm_one 0).sub (summable_gainN N)
  calc ∑' m, cterm (fun _ => 1) 0 m - ∑' m, gainN N m = ∑' m, (cterm (fun _ => 1) 0 m - gainN N m) :=
        (Summable.tsum_sub (summable_cterm_one 0) (summable_gainN N)).symm
    _ ≤ ∑' m, (4 / 5) ^ (N + 1) * h m := Summable.tsum_le_tsum hterm hsub (hhs.mul_left _)
    _ = (4 / 5) ^ (N + 1) * Real.log (zetaR (3 / 2)) := by rw [tsum_mul_left, hz]
    _ ≤ (4 / 5) ^ (N + 1) * Real.log 3 := by gcongr

/-- Terms of `L(logⁿ · g, σ)` for real coefficients `g`. -/
lemma term_logMul_real (g : ℕ → ℝ) (n : ℕ) (σ : ℝ) (m : ℕ) :
    term (LSeries.logMul^[n] (fun m => (g m : ℂ))) (σ : ℂ) m =
      ((if m = 0 then 0 else Real.log m ^ n * g m / (m : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [term_of_ne_zero hm, logMul_iterate_apply, if_neg hm]
    have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [show (Complex.log (m : ℂ)) = ((Real.log m : ℝ) : ℂ) by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp, Complex.ofReal_log hm']]
    rw [show ((m : ℂ) ^ (σ : ℂ)) = (((m : ℝ) ^ σ : ℝ) : ℂ) by
      rw [show (m : ℂ) = ((m : ℝ) : ℂ) by simp, Complex.ofReal_cpow hm']]
    push_cast; ring

/-- `L(logⁿ · g, 2) = ∑ g(m) logⁿ m / m²` for real coefficients `g` (as a complex number). -/
lemma LSeries_logMul_two_real (g : ℕ → ℝ) (n : ℕ) :
    LSeries (LSeries.logMul^[n] (fun m => (g m : ℂ))) 2 =
      ((∑' m : ℕ, g m * Real.log m ^ n / (m : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun m => ?_
  rw [term_logMul_real]
  congr 1
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [if_neg hm, Real.rpow_two]; ring

/-- `∑_{n ≤ N} bₙ = ∑ τ₁`. -/
theorem sum_bseq_eq (N : ℕ) : ∑ n ∈ range (N + 1), bseq n = ∑' m, tauN (fun _ => 1) N m := by
  rw [tsum_tauN (fun m => by simp) N, sum_range_succ', add_comm, ← log_zetaR_two_eq]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [bseq, LSeries_logMul_two_real (fun m => ArithmeticFunction.vonMangoldt m) n, Complex.ofReal_re]
  congr 1; exact tsum_congr fun m => by ring

/-- For a real character: `log L(2, χ) = ∑ c₀`, with `c(m) = Re χ(m)`. -/
theorem log_LSeries_two_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (c : ℕ → ℝ)
    (hc : ∀ m : ℕ, χ m = (c m : ℂ)) :
    LSeries (fun m => χ m) 2 = ((Real.exp (∑' m, cterm c 0 m) : ℝ) : ℂ) := by
  have h := DirichletCharacter.LSeries_eq_exp_LSeries χ (s := 2) (by norm_num)
  have hf : (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) / (Real.log n : ℂ)) =
      LSeries.logMul^[0] (fun m => ((c m * ArithmeticFunction.vonMangoldt m / Real.log m : ℝ) : ℂ)) := by
    funext n; simp [hc n]
  rw [hf, LSeries_logMul_two_real] at h
  rw [← h, Complex.ofReal_exp]
  congr 2
  exact tsum_congr fun m => by simp [cterm]; ring

/-- For a real character: `L(logⁿ · χΛ, 2) = ∑ c Λ logⁿ / m²`. -/
theorem LSeries_logMul_twist_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (c : ℕ → ℝ)
    (hc : ∀ m : ℕ, χ m = (c m : ℂ)) (n : ℕ) :
    LSeries (LSeries.logMul^[n] (fun m => χ m * (ArithmeticFunction.vonMangoldt m : ℂ))) 2 =
      ((∑' m : ℕ, c m * ArithmeticFunction.vonMangoldt m * Real.log m ^ n / (m : ℝ) ^ 2 : ℝ) : ℂ) := by
  have hf : (fun m : ℕ => χ m * (ArithmeticFunction.vonMangoldt m : ℂ)) =
      fun m => ((c m * ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) := by
    funext m; simp [hc m]
  rw [hf, LSeries_logMul_two_real]

end QRHLittlewood
end


section

open Complex Metric Set LSeries Filter Topology

set_option autoImplicit false

namespace QRHLittlewood

/-- **One-sided explicit core.** For a primitive real character `χ` modulo `q ≥ 3` with `L(s,χ) ≠ 0` on
`Re s > 7/8`, `L(1, χ) = e^u` with
`-u ≤ ∑_{n ≤ N} bₙ - B + (4/5)^{N+1} log 3 + 18 (A + B) (8/9)^{N+1}` for every `N`, where
`A = log 12 + (log q)/8` and `B = log ζ(2)`. -/
theorem explicit_core_lower {q : ℕ} [NeZero q] (hq : 3 ≤ q) {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive)
    (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ u : ℝ, DirichletCharacter.LFunction χ 1 = (Real.exp u : ℂ) ∧ ∀ N : ℕ,
      -u ≤ ∑ n ∈ Finset.range (N + 1), bseq n - Real.log (zetaR 2) + (4 / 5) ^ (N + 1) * Real.log 3 +
        18 * (Real.log 12 + Real.log q / 8 + Real.log (zetaR 2)) * (8 / 9) ^ (N + 1) := by
  have hq2 : 2 ≤ q := by omega
  have hχ1 : χ ≠ 1 := by
    rintro rfl; rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hprim; omega
  set Lf := DirichletCharacter.LFunction χ
  have hLf : EqOn Lf (LSeries (fun m => χ m)) {s | 1 < s.re} := fun s hs =>
    DirichletCharacter.LFunction_eq_LSeries χ hs
  set f : ℂ → ℂ := fun z => Lf (2 - z)
  have hball : ∀ z ∈ ball (0 : ℂ) (9 / 8), 7 / 8 < (2 - z).re := fun z hz => by
    have h' : ‖z‖ < 9 / 8 := by simpa using hz
    simp only [sub_re]; norm_num; linarith [abs_le.1 (Complex.abs_re_le_norm z)]
  have hLdiff : Differentiable ℂ Lf := DirichletCharacter.differentiable_LFunction hχ1
  have hfdiff : DifferentiableOn ℂ f (ball 0 (9 / 8)) := fun z _ =>
    ((hLdiff (2 - z)).comp z (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 2 - w) z)).differentiableWithinAt
  have hfne : ∀ z ∈ ball (0 : ℂ) (9 / 8), f z ≠ 0 := fun z hz => hH _ (hball z hz)
  -- normalisation at s = 2: L(2) real in [1/ζ(2), ζ(2)]
  have hL2 : Lf 2 = LSeries (fun m => χ m) 2 := hLf (by norm_num : (1 : ℝ) < (2 : ℂ).re)
  have hL2im : (Lf 2).im = 0 := by
    rw [hL2, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact LSeries_im_eq_zero (fun m => hreal m) 2
  have hL2near : ‖Lf 2 - 1‖ ≤ zetaR 2 - 1 := hL2 ▸ norm_LSeries_two_sub_one_le χ
  have hz2 := zetaR_two_lt
  have hz2pos : 0 < zetaR 2 := zetaR_pos (by norm_num)
  have hL2pos : 0 < (Lf 2).re := by
    have := Complex.abs_re_le_norm (Lf 2 - 1); simp at this; linarith [abs_le.1 (this.trans hL2near)]
  have hL2eq : Lf 2 = ((Lf 2).re : ℂ) := Complex.ext (by simp) (by simp [hL2im])
  have hL2norm : ‖Lf 2‖ = (Lf 2).re := by rw [hL2eq, Complex.norm_real, Real.norm_of_nonneg hL2pos.le]; simp
  have hL2up : (Lf 2).re ≤ zetaR 2 := by
    rw [← hL2norm, hL2, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    exact norm_LSeries_le_zetaR (fun m => DirichletCharacter.norm_le_one χ _) (by norm_num)
  have hL2lo : 1 / zetaR 2 ≤ (Lf 2).re := by rw [← hL2norm, hL2]; exact norm_LSeries_two_ge χ
  set ℓ2 : ℝ := Real.log (Lf 2).re
  set B : ℝ := Real.log (zetaR 2)
  have hℓ2 : |ℓ2| ≤ B := by
    rw [abs_le]; constructor
    · have := Real.log_le_log (by positivity) hL2lo
      rw [one_div, Real.log_inv] at this; linarith
    · exact Real.log_le_log hL2pos hL2up
  have hw0 : exp (ℓ2 : ℂ) = f 0 := by
    simp only [f, sub_zero]; rw [← Complex.ofReal_exp, Real.exp_log hL2pos, ← hL2eq]
  obtain ⟨F, hF0, hFd, hFexp⟩ := exists_log_on_ball hfdiff hfne (ℓ2 : ℂ) hw0 (by norm_num)
  have hFdiff : DifferentiableOn ℂ F (ball 0 (9 / 8)) := fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt
  -- Re F ≤ A on the disk
  set A : ℝ := Real.log 12 + Real.log q / 8
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hRe : ∀ z ∈ ball (0 : ℂ) (9 / 8), (F z).re ≤ A := by
    intro z hz
    have he := hFexp z hz
    have hn : ‖f z‖ ≤ 12 * (q : ℝ) ^ (1 / 8 : ℝ) := norm_LFunction_le_q_eighth hq2 hχ1 (by
      have : ‖z‖ < 9 / 8 := by simpa using hz
      simp only [sub_sub_cancel_left, norm_neg]; linarith)
    have : Real.exp (F z).re = ‖f z‖ := by rw [← he, Complex.norm_exp]
    rw [← Real.log_exp (F z).re, this]
    calc Real.log ‖f z‖ ≤ Real.log (12 * (q : ℝ) ^ (1 / 8 : ℝ)) :=
          Real.log_le_log (norm_pos_iff.2 (hfne z hz)) hn
      _ = A := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hqpos]; ring
  -- coefficients
  set a : ℕ → ℂ := fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n F 0
  have h1ball : (1 : ℂ) ∈ ball (0 : ℂ) (9 / 8) := by simp; norm_num
  have hTay : HasSum a (F 1) := by
    have := Complex.hasSum_taylorSeries_on_ball hFdiff h1ball
    simpa [a, smul_eq_mul] using this
  have hcar : ∀ n, 1 ≤ n → ‖a n‖ ≤ 2 * (A + B) * (8 / 9) ^ n := by
    intro n hn
    have h := caratheodory_coeff (by norm_num) hFdiff hRe hn
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hRe0 : (F 0).re = ℓ2 := by rw [hF0]; simp
    simp only [a, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_eq_div]
    calc ‖iteratedDeriv n F 0‖ / n.factorial ≤ 2 * (A - (F 0).re) / (9 / 8) ^ n := h
      _ ≤ 2 * (A + B) * (8 / 9) ^ n := by
          rw [hRe0, div_eq_mul_inv, ← inv_pow, show ((9 : ℝ) / 8)⁻¹ = 8 / 9 by norm_num]
          gcongr; linarith [neg_abs_le ℓ2]
  have hdom : ∀ n, ‖a (n + 1)‖ ≤ bseq (n + 1) := by
    intro n
    have hf : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
    simp only [a, norm_mul, norm_inv, Complex.norm_natCast]
    rw [iteratedDeriv_succ_log χ (R := 9 / 8) (by norm_num) hLf hFd n, bseq, inv_mul_eq_div]
    gcongr
    have := norm_LSeries_logMul_twist_le χ n (s := 2) (by norm_num)
    simpa using this
  have hdom0 : ‖a 0‖ ≤ bseq 0 := by
    simp only [a, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero, hF0,
      Complex.norm_real, Real.norm_eq_abs, bseq]; exact hℓ2
  have hdomall : ∀ n, ‖a n‖ ≤ bseq n := fun n => by
    cases n with
    | zero => exact hdom0
    | succ n => exact hdom n
  -- reality of F(1)
  have hderivreal : ∀ t : ℝ, |t| < 1 → (deriv F t).im = 0 := by
    intro t ht
    have htb : (t : ℂ) ∈ ball (0 : ℂ) (9 / 8) := by simp; linarith [abs_lt.1 ht]
    have h1 : 1 < (2 - (t : ℂ)).re := by simp; linarith [abs_lt.1 ht]
    rw [(hFd t htb).deriv, logderiv_formula χ hLf h1,
      show (2 : ℂ) - (t : ℂ) = ((2 - t : ℝ) : ℂ) by push_cast; ring]
    exact LSeries_im_eq_zero (fun m => by simp [hreal m]) _
  have hreal01 := im_eq_zero_of_real_deriv (F := F) (R := 1)
    (fun t ht => (hFd t (by simp; linarith [abs_lt.1 ht])).differentiableAt.hasDerivAt)
    hderivreal (by simp [hF0])
  have hF1im : (F 1).im = 0 := by
    have hc : ContinuousAt (fun t : ℝ => (F t).im) 1 := by
      have : ContinuousAt F ((1 : ℝ) : ℂ) := (hFd 1 (by simpa using h1ball)).differentiableAt.continuousAt
      exact (Complex.continuous_im.continuousAt.comp this).comp Complex.continuous_ofReal.continuousAt
    have hlim : Tendsto (fun t : ℝ => (F t).im) (nhdsWithin 1 (Set.Iio 1)) (nhds ((F ((1 : ℝ) : ℂ)).im)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun t : ℝ => (F t).im) =ᶠ[nhdsWithin 1 (Set.Iio 1)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
      exact hreal01 t (abs_lt.2 ⟨by linarith [ht.1], ht.2⟩)
    have := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
    simpa using this
  refine ⟨(F 1).re, ?_, fun N => ?_⟩
  · have he := hFexp 1 h1ball
    have hf1 : f 1 = Lf 1 := by show Lf (2 - 1) = Lf 1; norm_num
    rw [show F 1 = ((F 1).re : ℂ) from Complex.ext (by simp) (by simp [hF1im]), ← Complex.ofReal_exp] at he
    show Lf 1 = _
    rw [← hf1, ← he]
  · -- |F(1)| ≤ partial + tail
    have hsumm := hTay.summable
    have hsplit := hsumm.sum_add_tsum_nat_add (N + 1)
    rw [hTay.tsum_eq] at hsplit
    have hgeo : Summable fun n : ℕ => 2 * (A + B) * (8 / 9 : ℝ) ^ (n + (N + 1)) :=
      ((summable_geometric_of_lt_one (r := (8 / 9 : ℝ)) (by norm_num) (by norm_num)).mul_left
        (2 * (A + B) * (8 / 9) ^ (N + 1))).congr fun n => by rw [pow_add]; ring
    have hle : ∀ n, ‖a (n + (N + 1))‖ ≤ 2 * (A + B) * (8 / 9 : ℝ) ^ (n + (N + 1)) := fun n =>
      hcar _ (by omega)
    have htail : ‖∑' n, a (n + (N + 1))‖ ≤ 18 * (A + B) * (8 / 9) ^ (N + 1) := by
      refine (norm_tsum_le_tsum_norm (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
        ((Summable.tsum_le_tsum hle (hgeo.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hgeo).trans (le_of_eq ?_))
      have : ∑' n : ℕ, 2 * (A + B) * (8 / 9 : ℝ) ^ (n + (N + 1)) =
          2 * (A + B) * (8 / 9) ^ (N + 1) * ∑' n : ℕ, (8 / 9 : ℝ) ^ n := by
        rw [← tsum_mul_left]; congr 1; funext n; rw [pow_add]; ring
      rw [this, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring
    -- real-character data
    set c : ℕ → ℝ := fun m => (χ m).re
    have hc : ∀ m : ℕ, χ m = (c m : ℂ) := fun m => Complex.ext (by simp [c]) (by simp [hreal m])
    have hcb : ∀ m, |c m| ≤ 1 := fun m =>
      (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
    have hcp : ∀ p : ℕ, p.Prime → c p = -1 ∨ c p = 0 ∨ c p = 1 := by
      intro p hp
      by_cases hu : IsUnit (p : ZMod q)
      · have h1 : ‖χ (p : ZMod q)‖ = 1 := by
          have := DirichletCharacter.unit_norm_eq_one χ hu.unit; simpa using this
        rw [hc p, Complex.norm_real, Real.norm_eq_abs] at h1
        rcases (abs_eq zero_le_one).1 h1 with h | h
        · right; right; exact h
        · left; exact h
      · right; left
        have : χ (p : ZMod q) = 0 := MulChar.map_nonunit χ hu
        simp [c, this]
    have hmul : ∀ p k : ℕ, c (p ^ (k + 1)) = c p ^ (k + 1) := fun p k => by
      have : χ ((p ^ (k + 1) : ℕ) : ZMod q) = χ (p : ZMod q) ^ (k + 1) := by rw [Nat.cast_pow, map_pow]
      rw [hc, hc, ← Complex.ofReal_pow] at this
      exact Complex.ofReal_injective this
    -- the partial sum as a sum over prime powers
    have hℓ2S : ℓ2 = ∑' m, cterm c 0 m := by
      have h := log_LSeries_two_eq χ c hc
      rw [← hL2] at h
      simp only [ℓ2, h, Complex.ofReal_re, Real.log_exp]
    have hpartre : (∑ n ∈ Finset.range (N + 1), a n).re = ∑' m, tauN c N m := by
      rw [tsum_tauN hcb N, Complex.re_sum, Finset.sum_range_succ', add_comm]
      congr 1
      · simp [a, hF0, hℓ2S]
      · refine Finset.sum_congr rfl fun n _ => ?_
        simp only [a]
        rw [iteratedDeriv_succ_log χ (R := 9 / 8) (by norm_num) hLf hFd n, LSeries_logMul_twist_eq χ c hc n,
          show ((((n + 1).factorial : ℕ) : ℂ))⁻¹ = ((((n + 1).factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
          ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
    have hsign := sign_ineq c hcb hcp hmul N
    have hBg := B_sub_gain_le N
    have hb := sum_bseq_eq N
    have hre_tail : -(∑' n, a (n + (N + 1))).re ≤ ‖∑' n, a (n + (N + 1))‖ := by
      have := Complex.abs_re_le_norm (∑' n, a (n + (N + 1)))
      linarith [neg_abs_le ((∑' n, a (n + (N + 1))).re)]
    have hF1re : (F 1).re = (∑ n ∈ Finset.range (N + 1), a n).re + (∑' n, a (n + (N + 1))).re := by
      rw [← hsplit, Complex.add_re]
    simp only [A, B] at htail ⊢
    have hBeq : Real.log (zetaR 2) = ∑' m, cterm (fun _ => 1) 0 m := log_zetaR_two_eq
    rw [hF1re, hpartre]
    linarith

end QRHLittlewood
end


section

open Real Finset

set_option autoImplicit false

namespace QRHLittlewood

lemma log_one_add_le2 : Real.log (1 + 2.89315 / 5.4391) ≤ 0.42655 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 12 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

lemma log_zetaR_two_ge : 0.4976 ≤ Real.log (zetaR 2) := by
  rw [zetaR_two, Real.le_log_iff_exp_le (by positivity)]
  have hp := Real.pi_gt_d4
  have h1 : Real.exp 0.4976 ≤ 1.64477 := by
    refine exp_le_small (by norm_num) (by norm_num) 9 (by norm_num) ?_
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num
  nlinarith

lemma exp_neg_278_ge : 0.0617 ≤ Real.exp (-2.78) := by
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  have h1 : Real.exp 2.78 = Real.exp 1 ^ 2 * Real.exp 0.78 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp 0.78 ≤ 2.181473 := by
    refine exp_le_small (by norm_num) (by norm_num) 10 (by norm_num) ?_
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num
  have h3 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := by gcongr
  rw [h1]
  calc Real.exp 1 ^ 2 * Real.exp 0.78 ≤ 2.7182818286 ^ 2 * 2.181473 := by gcongr
    _ ≤ 0.0617⁻¹ := by norm_num

lemma exp_neg_22_ge : 0.11 ≤ Real.exp (-2.2) := by
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  have h1 : Real.exp 2.2 = Real.exp 1 ^ 2 * Real.exp 0.2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp 0.2 ≤ 1.2215 := by
    refine exp_le_small (by norm_num) (by norm_num) 6 (by norm_num) ?_
    simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num
  have h3 : Real.exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := by gcongr
  rw [h1]
  calc Real.exp 1 ^ 2 * Real.exp 0.2 ≤ 2.7182818286 ^ 2 * 1.2215 := by gcongr
    _ ≤ 0.11⁻¹ := by norm_num

lemma log_three_le : Real.log 3 ≤ 1.1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine exp_ge_of_sum (by norm_num) 10 ?_
  simp only [sum_range_succ, sum_range_zero, Nat.factorial]; norm_num

end QRHLittlewood
end


section

open Complex Real

set_option autoImplicit false

namespace QRHLittlewood

set_option maxHeartbeats 1000000 in
theorem littlewood_lower_explicit (q : ℕ) [NeZero q] (hq : (10 : ℝ) ^ 100 ≤ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    (617 / 10000 : ℝ) / Real.log (Real.log q) ≤ (DirichletCharacter.LFunction χ 1).re := by
  have hq3 : 3 ≤ q := by
    have : (3 : ℝ) ≤ q := le_trans (by norm_num) hq
    exact_mod_cast this
  obtain ⟨u, hu, hub⟩ := explicit_core_lower hq3 hprim hreal hH
  rw [hu, Complex.ofReal_re]
  -- notation
  set L1 : ℝ := Real.log q with hL1def
  set t : ℝ := Real.log L1 with htdef
  set a : ℝ := Real.log (9 / 8) with hadef
  have hL1 : 230.25 ≤ L1 := log_q_ge hq
  have ht : 5.4391 ≤ t := t_ge hq
  have ha1 := log_nine_eighths_ge
  have ha2 := log_nine_eighths_le
  have hapos : 0 < a := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  set x : ℝ := (Real.log (2 * L1) + 2.2) / a with hxdef
  have hlog2L : Real.log (2 * L1) = Real.log 2 + t := Real.log_mul (by norm_num) (by linarith)
  set N : ℕ := ⌈x⌉₊ with hNdef
  have hNx : x ≤ N := Nat.le_ceil x
  have hNx1 : (N : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one (by rw [hxdef]; apply div_nonneg _ hapos.le; rw [hlog2L]; linarith)).le
  have hx70 : 70 ≤ x := by
    rw [hxdef, le_div_iff₀ hapos, hlog2L]; nlinarith
  have hN64 : 64 ≤ N := by
    have : (64 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by linarith
  -- the bound from explicit_core
  have h1 := hub N
  -- truncation
  have htr := sharp_truncation N
  have hH : ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  rw [hH] at htr
  have hHN := harmonic_sub_log_le hN64
  have htrunc : 11 * (1 / 1.35 : ℝ) ^ (N + 1) / (1 - 1 / 1.35) ≤ 1e-6 := by
    have : (1 / 1.35 : ℝ) ^ (N + 1) ≤ (1 / 1.35) ^ 65 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc 11 * (1 / 1.35 : ℝ) ^ (N + 1) / (1 - 1 / 1.35) ≤ 11 * (1 / 1.35) ^ 65 / (1 - 1 / 1.35) := by gcongr
      _ ≤ 1e-6 := by norm_num
  -- log x
  have hlogx : Real.log x ≤ Real.log t + 0.42655 + 2.1397 := by
    have hc1 : Real.log 2 + 2.2 ≤ 2.89315 := by linarith
    have hpos : 0 < t + (Real.log 2 + 2.2) := by linarith
    have hx' : x = (t + (Real.log 2 + 2.2)) / a := by rw [hxdef, hlog2L]; ring
    calc Real.log x = Real.log (t + (Real.log 2 + 2.2)) - Real.log a := by
          rw [hx', Real.log_div hpos.ne' hapos.ne']
      _ = Real.log t + Real.log (1 + (Real.log 2 + 2.2) / t) - Real.log a := by
          rw [← Real.log_mul (by linarith) (by positivity)]; congr 2; field_simp
      _ ≤ Real.log t + Real.log (1 + 2.89315 / 5.4391) + 2.1397 := by
          have hm : Real.log (1 + (Real.log 2 + 2.2) / t) ≤ Real.log (1 + 2.89315 / 5.4391) := by
            apply Real.log_le_log (by positivity)
            have : (Real.log 2 + 2.2) / t ≤ 2.89315 / 5.4391 := by
              rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
            linarith
          have := neg_log_a_le
          linarith
      _ ≤ Real.log t + 0.42655 + 2.1397 := by linarith [log_one_add_le2]
  -- joint rounding: N = x + θ
  set θ : ℝ := (N : ℝ) - x with hθdef
  have hθ0 : 0 ≤ θ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hxpos : 0 < x := by linarith
  have hlogN : Real.log N ≤ Real.log x + θ / 70 := by
    have h := Real.log_le_sub_one_of_pos (x := (N : ℝ) / x) (by positivity)
    rw [Real.log_div hNpos.ne' hxpos.ne'] at h
    have : (N : ℝ) / x - 1 = θ / x := by rw [hθdef]; field_simp
    have h2 : θ / x ≤ θ / 70 := div_le_div_of_nonneg_left hθ0 (by norm_num) hx70
    linarith
  set B : ℝ := Real.log (zetaR 2)
  have hB : B ≤ 0.5109 := by
    have := Real.log_le_log (zetaR_pos (by norm_num)) zetaR_two_lt.le
    linarith [log_five_thirds_le]
  have hBlo : 0.4976 ≤ B := log_zetaR_two_ge
  have hl12 := log_twelve_le
  have hl12' : 0 ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hexpa : Real.exp (-a) = 8 / 9 := by
    rw [hadef, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hconv : Real.exp (-a * θ) ≤ 1 - θ / 9 := by
    have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-a)) (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0
      (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, hexpa] at this
    calc Real.exp (-a * θ) = Real.exp (θ * -a) := by ring_nf
      _ ≤ 1 - θ + θ * (8 / 9) := this
      _ = 1 - θ / 9 := by ring
  set T : ℝ := Real.exp (-2.2) * (1 + 8 * (Real.log 12 + B) / L1)
  have hT1 : T ≤ 0.12245 := by
    have he := exp_neg_22_le
    have hfrac : 8 * (Real.log 12 + B) / L1 ≤ 8 * (2.4851 + 0.5109) / 230.25 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
    have hpos : 0 ≤ 1 + 8 * (Real.log 12 + B) / L1 := by
      have : 0 ≤ 8 * (Real.log 12 + B) / L1 := by apply div_nonneg _ (by linarith); linarith
      linarith
    calc T = Real.exp (-2.2) * (1 + 8 * (Real.log 12 + B) / L1) := rfl
      _ ≤ 0.1109 * (1 + 8 * (2.4851 + 0.5109) / 230.25) :=
          mul_le_mul he (by linarith) hpos (by norm_num)
      _ ≤ 0.12245 := by norm_num
  have hT0 : 0.11 ≤ T := by
    have he := exp_neg_22_ge
    have : 1 ≤ 1 + 8 * (Real.log 12 + B) / L1 := by
      have : 0 ≤ 8 * (Real.log 12 + B) / L1 := by apply div_nonneg _ (by linarith); linarith
      linarith
    calc (0.11 : ℝ) = 0.11 * 1 := by ring
      _ ≤ Real.exp (-2.2) * (1 + 8 * (Real.log 12 + B) / L1) := by gcongr
  have htailT : 18 * (Real.log 12 + L1 / 8 + B) * (8 / 9 : ℝ) ^ (N + 1) = T * Real.exp (-a * θ) := by
    have h89 : (8 / 9 : ℝ) ^ N = Real.exp (-(N : ℝ) * a) := by
      rw [show -(N : ℝ) * a = (N : ℝ) * Real.log (8 / 9) by
        rw [hadef, show (8 / 9 : ℝ) = (9 / 8)⁻¹ by norm_num, Real.log_inv]; ring,
        Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hsplit : Real.exp (-(N : ℝ) * a) = Real.exp (-2.2) * (2 * L1)⁻¹ * Real.exp (-a * θ) := by
      rw [show -(N : ℝ) * a = -2.2 + -Real.log (2 * L1) + -a * θ by
        rw [hθdef, hxdef]; field_simp; ring,
        Real.exp_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]
    rw [pow_succ, h89, hsplit]
    simp only [T]
    field_simp
    ring
  have hround : Real.log N + 18 * (Real.log 12 + L1 / 8 + B) * (8 / 9 : ℝ) ^ (N + 1) ≤
      Real.log x + 0.12245 + 0.0021 := by
    rw [htailT]
    have h1 : T * Real.exp (-a * θ) ≤ T * (1 - θ / 9) :=
      mul_le_mul_of_nonneg_left hconv (by linarith only [hT0])
    have hθT : 0.11 * θ ≤ T * θ := mul_le_mul_of_nonneg_right hT0 hθ0
    linarith only [hlogN, h1, hθT, hT1, hθ1, hθ0]
  have hdelta : (4 / 5 : ℝ) ^ (N + 1) * Real.log 3 ≤ 1e-6 := by
    have h3 := log_three_le
    have h3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have : (4 / 5 : ℝ) ^ (N + 1) ≤ (4 / 5) ^ 65 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc (4 / 5 : ℝ) ^ (N + 1) * Real.log 3 ≤ (4 / 5) ^ 65 * 1.1 := by gcongr
      _ ≤ 1e-6 := by norm_num
  have hHN' : (harmonic N : ℝ) ≤ Real.log N + 0.58504 := by linarith only [hHN]
  have h1' : -u ≤ ∑ n ∈ Finset.range (N + 1), bseq n - B + (4 / 5) ^ (N + 1) * Real.log 3 +
      18 * (Real.log 12 + L1 / 8 + B) * (8 / 9) ^ (N + 1) := h1
  clear_value T θ B N x L1 t a
  have s1 : ∑ n ∈ Finset.range (N + 1), bseq n ≤ (harmonic N : ℝ) + 1e-6 := by
    linarith only [htr, htrunc]
  have s2 : -u ≤ (harmonic N : ℝ) + 1e-6 - B + (4 / 5) ^ (N + 1) * Real.log 3 +
      18 * (Real.log 12 + L1 / 8 + B) * (8 / 9) ^ (N + 1) := by linarith only [h1', s1]
  have hfin : -u ≤ Real.log t + 2.78 := by
    linarith only [s2, hHN', hround, hdelta, hBlo, hlogx]
  -- conclude
  have htpos : 0 < t := by linarith
  have he := exp_neg_278_ge
  calc (617 / 10000 : ℝ) / t ≤ Real.exp (-2.78) / t := by gcongr; linarith only [he]
    _ = Real.exp (-2.78 - Real.log t) := by
        rw [Real.exp_sub, Real.exp_log htpos]
    _ ≤ Real.exp u := Real.exp_le_exp.2 (by linarith only [hfin])

end QRHLittlewood
end


theorem solution (q : ℕ) [NeZero q] (hq : (10 : ℝ) ^ 100 ≤ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    (hH : ∀ s : ℂ, 7 / 8 < s.re → DirichletCharacter.LFunction χ s ≠ 0) :
    (617 / 10000 : ℝ) / Real.log (Real.log q) ≤ (DirichletCharacter.LFunction χ 1).re :=
  QRHLittlewood.littlewood_lower_explicit q hq χ hprim hreal hH
