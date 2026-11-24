-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:26.317503+00:00
-- url     : https://prove2.me/submissions/8f94e65b-b873-4442-bef9-e09c1132a719

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqZeroOfForallIntegralCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
attribute [local instance] UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2
section Algebra
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
private theorem UpperTheory.Reformulated.B.Gwa7.deriv_zero (φ : A →L[ℂ] ℂ) {f : ℂ → A} {f' : A}
    (hf : HasDerivAt f f' 0) (h : ∀ t, φ (f t) = 0) : φ f' = 0 := by
  have h1 : HasDerivAt (fun t => φ (f t)) (φ f') 0 := φ.hasFDerivAt.comp_hasDerivAt 0 hf
  have h2 : (fun t => φ (f t)) = fun _ => (0 : ℂ) := funext h
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const 0 0)
private theorem UpperTheory.Reformulated.B.Gwa7.line_deriv (x y : A) :
    HasDerivAt (fun t : ℂ => x + t • y) y 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const y).const_add x
private theorem UpperTheory.Reformulated.B.Gwa7.step_one (φ : A →L[ℂ] ℂ) (x y c : A) (n : ℕ)
    (h : ∀ s : ℂ, φ ((x + s • y) ^ (n + 1) * c) = 0) : φ (x ^ n * y * c) = 0 := by
  have h1 := UpperTheory.Reformulated.B.Gwa7.deriv_zero φ
    (((UpperTheory.Reformulated.B.Gwa7.line_deriv x y).pow (n + 1)).mul_const c) h
  have h2 : ((n + 1 : ℕ) : A) * (x + (0 : ℂ) • y) ^ (n + 1 - 1) * y * c
      = ((n + 1 : ℕ) : ℂ) • (x ^ n * y * c) := by
    simp only [Algebra.smul_def, map_natCast, map_zero, zero_mul, add_zero, Nat.add_sub_cancel]
    ring
  rw [h2, map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
private theorem UpperTheory.Reformulated.B.Gwa7.step_two (φ : A →L[ℂ] ℂ) (x x' y y' c Δ : A) (κ : ℂ) (n : ℕ)
    (hΔ : x' * y = x * y' - κ • Δ)
    (h : ∀ t : ℂ, φ ((x + t • x') ^ (n + 1) * (y + t • y') * c) = 0)
    (h' : φ (x ^ n * Δ * c) = 0) : φ (x ^ (n + 1) * y' * c) = 0 := by
  have h1 := UpperTheory.Reformulated.B.Gwa7.deriv_zero φ
    ((((UpperTheory.Reformulated.B.Gwa7.line_deriv x x').pow (n + 1)).mul
      (UpperTheory.Reformulated.B.Gwa7.line_deriv y y')).mul_const c) h
  have h2 : (((n + 1 : ℕ) : A) * (x + (0 : ℂ) • x') ^ (n + 1 - 1) * x' * (y + (0 : ℂ) • y')
      + (x + (0 : ℂ) • x') ^ (n + 1) * y') * c
      = ((n + 2 : ℕ) : ℂ) • (x ^ (n + 1) * y' * c) - (((n + 1 : ℕ) : ℂ) * κ) • (x ^ n * Δ * c) := by
    simp only [Algebra.smul_def, map_natCast, map_zero, zero_mul, add_zero, Nat.add_sub_cancel,
      map_mul] at hΔ ⊢
    push_cast
    linear_combination ((n : A) + 1) * x ^ n * c * hΔ
  have h3 := h2 ▸ h1
  rw [map_sub, map_smul, map_smul, h', smul_zero, sub_zero, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))
private theorem UpperTheory.Reformulated.B.Gwa7.mul_lin (φ : A →L[ℂ] ℂ) (p q r s z : A) (D : ℤ → A)
    (hD : ∀ m, D (m + 1) = (p * s - q * r) * D m)
    (h : ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ), φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d ^ n * D m * z) = 0)
    (a' b' c' d' : ℂ) (n : ℕ) (m : ℤ) (a b c d : ℂ) :
    φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d ^ n * D m *
      (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c' d' * z)) = 0 := by
  cases n with
  | zero =>
    rw [← h 1 m a' b' c' d']
    congr 1
    ring
  | succ n =>
    have key := UpperTheory.Reformulated.B.Gwa7.step_two φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d)
      (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c' d') (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c d)
      (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c' d') (D m * z) (p * s - q * r)
      ((a * b' - b * a') * (c * d' - d * c')) n ?_ ?_ ?_
    · rw [← key]
      congr 1
      ring
    · simp only [UpperTheory.Reformulated.B.Gwa7.lin, Algebra.smul_def, map_mul, map_sub]
      ring
    · intro t
      refine UpperTheory.Reformulated.B.Gwa7.step_one φ _ _ _ _ fun u => ?_
      rw [← h (n + 1 + 1) m (a + u * a') (b + u * b') (c + t * c') (d + t * d'), ← mul_assoc]
      congr 4
      simp only [UpperTheory.Reformulated.B.Gwa7.lin, Algebra.smul_def, map_mul, map_add]
      ring
    · rw [← h n (m + 1) a b c d, hD]
      congr 1
      ring
end Algebra
private theorem UpperTheory.Reformulated.B.Gwa7.unit_vec (a b : ℂ) :
    ∃ r α β : ℂ, a = r * α ∧ b = r * β ∧
      α * (starRingEnd ℂ) α + β * (starRingEnd ℂ) β = 1 := by
  by_cases h0 : Complex.normSq a + Complex.normSq b = 0
  · have ha := Complex.normSq_nonneg a
    have hb := Complex.normSq_nonneg b
    have ha0 : a = 0 := Complex.normSq_eq_zero.1 (by linarith)
    have hb0 : b = 0 := Complex.normSq_eq_zero.1 (by linarith)
    exact ⟨0, 1, 0, by simp [ha0], by simp [hb0], by simp⟩
  · have hpos : 0 ≤ Complex.normSq a + Complex.normSq b :=
      add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)
    set r : ℝ := Real.sqrt (Complex.normSq a + Complex.normSq b) with hr
    have hrr : r * r = Complex.normSq a + Complex.normSq b := Real.mul_self_sqrt hpos
    have hr0 : (r : ℂ) ≠ 0 := by
      intro h
      rw [Complex.ofReal_eq_zero] at h
      rw [h] at hrr
      exact h0 (by linarith)
    have hc : (r : ℂ) * r = a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b := by
      rw [Complex.mul_conj, Complex.mul_conj]
      exact_mod_cast hrr
    refine ⟨r, a / r, b / r, by field_simp, by field_simp, ?_⟩
    rw [map_div₀, map_div₀, Complex.conj_ofReal]
    field_simp
    linear_combination -hc
private theorem UpperTheory.Reformulated.B.Gwa7.star_eq (k : UpperTheory.Reformulated.B.Gwa7.U2) :
    star k.1 = (k.1.det)⁻¹ • k.1.adjugate := by
  have h1 : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : star k.1 * (k.1 * k.1.adjugate) = k.1.adjugate := by
    rw [← mul_assoc, h1, one_mul]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one] at h2
  rw [← h2, smul_smul, inv_mul_cancel₀ (UpperTheory.Reformulated.B.Gwa7.det_ne k), one_smul]
open UpperTheory.Reformulated.B.Gwa7 in
private theorem UpperTheory.Reformulated.B.Gwa7.entry_lin [CompactSpace U2] (i j : Fin 2) : ∃ a b c d : ℂ,
    entry i j = lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d := by
  fin_cases i <;> fin_cases j
  · exact ⟨1, 0, 1, 0, by simp [lin]⟩
  · exact ⟨1, 0, 0, 1, by simp [lin]⟩
  · exact ⟨0, 1, 1, 0, by simp [lin]⟩
  · exact ⟨0, 1, 0, 1, by simp [lin]⟩
open UpperTheory.Reformulated.B.Gwa7 in
private theorem UpperTheory.Reformulated.B.Gwa7.star_entry_lin [CompactSpace U2] (i j : Fin 2) : ∃ a b c d : ℂ,
    star (entry i j) = detPow (-1) * lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d := by
  have h : ∀ k : U2, star (k.1 i j) = (k.1.det)⁻¹ * k.1.adjugate j i := fun k => by
    have := congrFun (congrFun (star_eq k) j) i
    simpa [Matrix.star_apply] using this
  fin_cases i <;> fin_cases j
  · refine ⟨0, 1, 0, 1, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
  · refine ⟨0, -1, 1, 0, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
  · refine ⟨-1, 0, 0, 1, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
  · refine ⟨1, 0, 1, 0, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
open UpperTheory.Reformulated.B.Gwa7 in
private theorem UpperTheory.Reformulated.B.Gwa7.lin_eq [CompactSpace U2] (a b c d : ℂ) :
    ∃ (r : ℂ) (l₁ l₂ : U2), ∀ k : U2,
    lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d k = r * (l₁ * k * l₂).1 0 0 := by
  obtain ⟨r, α, β, rfl, rfl, h⟩ := unit_vec a b
  obtain ⟨s, γ, δ, rfl, rfl, h'⟩ := unit_vec c d
  refine ⟨r * s, ⟨!![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α], ?_⟩,
    ⟨!![γ, -(starRingEnd ℂ) δ; δ, (starRingEnd ℂ) γ], ?_⟩, fun k => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      first | linear_combination h | ring
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      first | linear_combination h' | ring
  · simp [lin, entry, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    ring
open UpperTheory.Reformulated.B.Gwa7 in
private theorem UpperTheory.Reformulated.B.Gwa7.functional_zero [CompactSpace U2] (φ : C(U2, ℂ) →L[ℂ] ℂ)
    (h : ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ),
      φ (lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d ^ n * detPow m * 1) = 0)
    (f : C(U2, ℂ)) : φ f = 0 := by
  let P : C(U2, ℂ) → Prop := fun z => ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ),
    φ (lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d ^ n * detPow m * z) = 0
  have hD : ∀ m, detPow (m + 1) = (entry 0 0 * entry 1 1 - entry 0 1 * entry 1 0) * detPow m := by
    intro m
    ext k
    change k.1.det ^ (m + 1) = (k.1 0 0 * k.1 1 1 - k.1 0 1 * k.1 1 0) * k.1.det ^ m
    rw [zpow_add_one₀ (det_ne k), ← Matrix.det_fin_two, mul_comm]
  have hD' : ∀ m, detPow m * detPow (-1) = detPow (m + -1) := by
    intro m
    ext k
    exact (zpow_add₀ (det_ne k) m (-1)).symm
  have hD0 : detPow 0 = 1 := by
    ext k
    exact zpow_zero _
  let S : Set C(U2, ℂ) := Set.range fun ij : Fin 2 × Fin 2 => entry ij.1 ij.2
  have hmul : ∀ f ∈ Algebra.adjoin ℂ (S ∪ star S), ∀ z, P z → P (f * z) := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨ij, rfl⟩ | ⟨ij, hx⟩
      · obtain ⟨a, b, c, d, e⟩ := entry_lin ij.1 ij.2
        dsimp only
        rw [e]
        exact mul_lin φ _ _ _ _ z detPow hD hz a b c d
      · obtain ⟨a, b, c, d, e⟩ := star_entry_lin ij.1 ij.2
        have hx' : x = star (entry ij.1 ij.2) := by
          rw [← star_star x, ← hx]
        rw [hx', e]
        intro n m a' b' c' d'
        rw [← mul_lin φ _ _ _ _ z detPow hD hz a b c d n (m + -1) a' b' c' d', ← hD']
        congr 1
        ring
    | algebraMap r =>
      intro z hz n m a b c d
      rw [← Algebra.smul_def, mul_smul_comm, map_smul, hz, smul_zero]
    | add x y _ _ hx hy =>
      intro z hz n m a b c d
      rw [add_mul, mul_add, map_add, hx z hz, hy z hz, add_zero]
    | mul x y _ _ hx hy =>
      intro z hz
      rw [mul_assoc]
      exact hx _ (hy z hz)
  have hsep : (StarAlgebra.adjoin ℂ S).SeparatesPoints := by
    intro x y hxy
    by_contra hcon
    refine hxy (Subtype.ext (Matrix.ext fun i j => ?_))
    by_contra hne
    exact hcon ⟨entry i j, ⟨entry i j, StarAlgebra.subset_adjoin ℂ S ⟨(i, j), rfl⟩, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hf : f ∈ closure (StarAlgebra.adjoin ℂ S : Set C(U2, ℂ)) := by
    have : f ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure := by
      rw [htop]
      trivial
    exact this
  refine closure_minimal (t := {f | φ f = 0}) ?_ (isClosed_eq φ.continuous continuous_const) hf
  intro x hx
  have := hmul x hx 1 h 0 0 0 0 0 0
  simpa [hD0] using this
open UpperTheory.Reformulated.B.Gwa7 MeasureTheory in
private theorem UpperTheory.Reformulated.B.Gwa7.main [CompactSpace U2] [BorelSpace U2] (μ : Measure U2)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {g : U2 → ℂ} (hg : Continuous g)
    (h : ∀ (n : ℕ) (q : ℤ) (l₁ l₂ : U2),
      ∫ k, (l₁ * k * l₂).1 0 0 ^ n * k.1.det ^ q * g k ∂μ = 0) : g = 0 := by
  let G : C(U2, ℂ) := star ⟨g, hg⟩
  let φ : C(U2, ℂ) →L[ℂ] ℂ :=
    (innerSL ℂ (ContinuousMap.toLp 2 μ ℂ G)).comp (ContinuousMap.toLp 2 μ ℂ)
  have hφ : ∀ f, φ f = ∫ k, f k * g k ∂μ := by
    intro f
    have := MeasureTheory.ContinuousMap.inner_toLp (𝕜 := ℂ) μ G f
    refine this.trans ?_
    simp [G]
  have h0 : φ G = 0 := by
    refine functional_zero φ (fun n m a b c d => ?_) G
    obtain ⟨r, l₁, l₂, e⟩ := lin_eq a b c d
    rw [hφ, ← mul_zero (r ^ n), ← h n m l₁ l₂, ← integral_const_mul]
    congr 1
    ext k
    rw [mul_one, ContinuousMap.mul_apply, ContinuousMap.pow_apply, e]
    change _ * k.1.det ^ m * _ = _
    ring
  have h1 : ContinuousMap.toLp 2 μ ℂ G = 0 := inner_self_eq_zero.1 h0
  have h2 : G = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ (by rw [h1, map_zero])
  ext k
  simpa [G] using congrArg (fun F : C(U2, ℂ) => F k) h2
end

set_option autoImplicit false
attribute [local instance] UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2
namespace UpperTheory.Reformulated.B.Gwa7
theorem _root_.solution :
    ∀ {g : UpperTheory.Reformulated.B.Gwa7.U2 → Complex},
      @Continuous UpperTheory.Reformulated.B.Gwa7.U2 Complex
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
          g →
        (∀ (n : Nat) (q : Int) (l₁ l₂ : UpperTheory.Reformulated.B.Gwa7.U2),
            @Eq Complex
              (@MeasureTheory.integral UpperTheory.Reformulated.B.Gwa7.U2 Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 UpperTheory.Reformulated.B.Gwa7.μK fun (k : UpperTheory.Reformulated.B.Gwa7.U2) ↦
                @HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                    (@HPow.hPow Complex Nat Complex
                      (@instHPow Complex Nat
                        (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))
                      (@Subtype.val
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (fun
                            (x :
                              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
                          @Membership.mem
                            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                            (@Submonoid
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@MulZeroOneClass.toMulOneClass
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@instMulZeroOneClassOfSemiring
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                            (@SetLike.instMembership
                              (@Submonoid
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@Submonoid.instSetLike
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                              Complex.commRing Complex.instStarRing)
                            x)
                        (@HMul.hMul UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2
                          (@instHMul UpperTheory.Reformulated.B.Gwa7.U2
                            (@Submonoid.mul
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@MulZeroOneClass.toMulOneClass
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@instMulZeroOneClassOfSemiring
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                              (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                Complex.commRing Complex.instStarRing)))
                          (@HMul.hMul UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2
                            (@instHMul UpperTheory.Reformulated.B.Gwa7.U2
                              (@Submonoid.mul
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                  Complex.commRing Complex.instStarRing)))
                            l₁ k)
                          l₂)
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                      n)
                    (@HPow.hPow Complex Int Complex
                      (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))
                      (@Matrix.det (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                        (@Subtype.val
                          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                          (fun
                              (x :
                                Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
                            @Membership.mem
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@Submonoid
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                              (@SetLike.instMembership
                                (@Submonoid
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@MulZeroOneClass.toMulOneClass
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@instMulZeroOneClassOfSemiring
                                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@Submonoid.instSetLike
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@MulZeroOneClass.toMulOneClass
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@instMulZeroOneClassOfSemiring
                                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                              (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                Complex.commRing Complex.instStarRing)
                              x)
                          k))
                      q))
                  (g k))
              (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))) →
          @Eq (UpperTheory.Reformulated.B.Gwa7.U2 → Complex) g
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Gwa7.U2 → Complex) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Gwa7.U2 → Complex)
                (@Pi.instZero UpperTheory.Reformulated.B.Gwa7.U2 (fun (a : UpperTheory.Reformulated.B.Gwa7.U2) ↦ Complex) fun (i : UpperTheory.Reformulated.B.Gwa7.U2) ↦
                  Complex.instZero))) := by
  intro g hg h
  haveI : CompactSpace UpperTheory.Reformulated.B.Gwa7.U2 := UpperTheory.Reformulated.B.Gwa7.aux5
  haveI : BorelSpace UpperTheory.Reformulated.B.Gwa7.U2 := UpperTheory.Reformulated.B.Gwa7.aux4
  haveI : UpperTheory.Reformulated.B.Gwa7.μK.IsHaarMeasure :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure _
  exact UpperTheory.Reformulated.B.Gwa7.main UpperTheory.Reformulated.B.Gwa7.μK hg h
end UpperTheory.Reformulated.B.Gwa7
