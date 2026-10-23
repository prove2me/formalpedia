-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P19.psd_small_degrees
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:25:08.707041+00:00
-- url     : https://prove2.me/submissions/075ff3f2-f900-4d16-8be8-22402ee33bd4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

open scoped BigOperators

namespace X7SmallDeg
open QAlgorithms.Papers.Independent.Information100.P19

def P1 : Part 1 := ⟨[1], by decide⟩
def P2 : Part 2 := ⟨[2], by decide⟩
def P11 : Part 2 := ⟨[1, 1], by decide⟩
def P3 : Part 3 := ⟨[3], by decide⟩
def P21 : Part 3 := ⟨[2, 1], by decide⟩
def P111 : Part 3 := ⟨[1, 1, 1], by decide⟩

lemma part1 (p : Part 1) : p = P1 := by
  obtain ⟨l, h1, h2, h3⟩ := p
  apply Subtype.ext
  simp only [P1]
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at h3
  · simp at h3; simp [h3]
  · exfalso; simp at h2 h3; omega

lemma part2 (p : Part 2) : p = P2 ∨ p = P11 := by
  have : p.val = [2] ∨ p.val = [1, 1] := by
    obtain ⟨l, h1, h2, h3⟩ := p
    simp only
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · simp at h3
    · simp at h3; simp [h3]
    · simp at h2 h3; right; simp; omega
    · exfalso; simp at h2 h3; omega
  rcases this with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

lemma part3 (p : Part 3) : p = P3 ∨ p = P21 ∨ p = P111 := by
  have : p.val = [3] ∨ p.val = [2, 1] ∨ p.val = [1, 1, 1] := by
    obtain ⟨l, h1, h2, h3⟩ := p
    simp only
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, t⟩⟩⟩⟩
    · simp at h3
    · simp at h3; simp [h3]
    · simp at h1 h2 h3; right; left; simp; omega
    · simp at h2 h3; right; right; simp; omega
    · exfalso; simp at h2 h3; omega
  rcases this with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

lemma P2_ne : P2 ≠ P11 := by
  intro h; have := congrArg Subtype.val h; simp [P2,P11] at this
lemma P3_ne1 : P3 ≠ P21 := by
  intro h; have := congrArg Subtype.val h; simp [P3,P21] at this
lemma P3_ne2 : P3 ≠ P111 := by
  intro h; have := congrArg Subtype.val h; simp [P3,P111] at this
lemma P3_ne3 : P21 ≠ P111 := by
  intro h; have := congrArg Subtype.val h; simp [P21,P111] at this

lemma b1_eq : b1 = Finsupp.single P1 1 := rfl
lemma b2_eq : b2 = Finsupp.single P2 1 := rfl
lemma b11_eq : b11 = Finsupp.single P11 1 := rfl

lemma pairing1 (f : Coeff 1) (y : Part 1 → ℝ) : pairing f y = f P1 * y P1 := by
  classical
  unfold pairing
  rw [Finsupp.sum_of_support_subset f (s := {P1}) (fun p _ => by simp [part1 p]) _
    (fun _ _ => by ring)]
  simp

lemma pairing2 (f : Coeff 2) (y : Part 2 → ℝ) :
    pairing f y = f P2 * y P2 + f P11 * y P11 := by
  classical
  unfold pairing
  rw [Finsupp.sum_of_support_subset f (s := {P2, P11})
    (fun p _ => by rcases part2 p with rfl | rfl <;> simp) _ (fun _ _ => by ring)]
  rw [Finset.sum_pair P2_ne]

lemma pairing3 (f : Coeff 3) (y : Part 3 → ℝ) :
    pairing f y = f P3 * y P3 + f P21 * y P21 + f P111 * y P111 := by
  classical
  unfold pairing
  rw [Finsupp.sum_of_support_subset f (s := {P3, P21, P111})
    (fun p _ => by rcases part3 p with rfl | rfl | rfl <;> simp) _ (fun _ _ => by ring)]
  rw [Finset.sum_insert (by simp [P3_ne1, P3_ne2]), Finset.sum_pair P3_ne3]; ring

lemma sm1 {d : ℕ} (x : Fin d → ℝ) : spectralMoments x P1 = ∑ i, x i := by
  simp [spectralMoments, P1]
lemma sm2 {d : ℕ} (x : Fin d → ℝ) : spectralMoments x P2 = ∑ i, x i ^ 2 := by
  simp [spectralMoments, P2]
lemma sm11 {d : ℕ} (x : Fin d → ℝ) : spectralMoments x P11 = (∑ i, x i) ^ 2 := by
  simp [spectralMoments, P11, sq]
lemma sm3 {d : ℕ} (x : Fin d → ℝ) : spectralMoments x P3 = ∑ i, x i ^ 3 := by
  simp [spectralMoments, P3]
lemma sm21 {d : ℕ} (x : Fin d → ℝ) :
    spectralMoments x P21 = (∑ i, x i ^ 2) * ∑ i, x i := by
  simp [spectralMoments, P21]
lemma sm111 {d : ℕ} (x : Fin d → ℝ) : spectralMoments x P111 = (∑ i, x i) ^ 3 := by
  simp [spectralMoments, P111]; ring

lemma ext2 (f : Coeff 2) : f = f P2 • b2 + f P11 • b11 := by
  ext p
  rcases part2 p with rfl | rfl <;> simp [b2_eq, b11_eq, Finsupp.single_apply, P2_ne, P2_ne.symm]

end X7SmallDeg


open scoped BigOperators

namespace X7SmallDeg
open QAlgorithms.Papers.Independent.Information100.P19

section Generic
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma ray_smul (u : V) {c : ℝ} (hc : 0 < c) : ray (c • u) = ray u := by
  ext w; constructor
  · rintro ⟨d, hd, rfl⟩; exact ⟨d * c, mul_nonneg hd hc.le, by rw [smul_smul]⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d / c, div_nonneg hd hc.le, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']⟩

/-- Cone cut out by two functionals with a dual pair of generators. -/
lemma extreme_two (φ ψ : V →ₗ[ℝ] ℝ) (u v : V) (hφu : φ u = 1) (hψu : ψ u = 0)
    (hφv : φ v = 0) (hψv : ψ v = 1) (hdec : ∀ f, f = φ f • u + ψ f • v)
    (C : Set V) (hC : C = {f | 0 ≤ φ f ∧ 0 ≤ ψ f}) (w : V) :
    Extreme C w ↔ ∃ c : ℝ, 0 < c ∧ (w = c • u ∨ w = c • v) := by
  subst hC
  constructor
  · rintro ⟨hw0, ⟨hφ, hψ⟩, hext⟩
    have hu' : φ w • u ∈ {f : V | 0 ≤ φ f ∧ 0 ≤ ψ f} := by
      simp [hφu, hψu, hφ]
    have hv' : ψ w • v ∈ {f : V | 0 ≤ φ f ∧ 0 ≤ ψ f} := by
      simp [hφv, hψv, hψ]
    obtain ⟨a, b, ha, hb, h1, h2⟩ := hext _ hu' _ hv' (hdec w).symm
    have e1 := congrArg ψ h1
    have e2 := congrArg φ h1
    simp [hψu, hφu] at e1 e2
    rcases e1 with e1 | e1
    · subst e1
      simp at e2
      refine ⟨ψ w, ?_, Or.inr ?_⟩
      · rcases hψ.lt_or_eq with h | h
        · exact h
        · exfalso; apply hw0; rw [hdec w, e2, ← h]; simp
      · rw [hdec w, e2]; simp [hψv]
    · refine ⟨φ w, ?_, Or.inl ?_⟩
      · rcases hφ.lt_or_eq with h | h
        · exact h
        · exfalso; apply hw0; rw [hdec w, e1, ← h]; simp
      · rw [hdec w, e1]; simp [hφu]
  · rintro ⟨c, hc, h | h⟩
    · subst h
      refine ⟨?_, ⟨by simp [hφu, hc.le], by simp [hψu]⟩, ?_⟩
      · intro h0; have := congrArg φ h0; simp [hφu] at this; linarith
      · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ hxy
        have e1 := congrArg ψ hxy; simp [hψu] at e1
        have hx0 : ψ x = 0 := by linarith
        have hy0 : ψ y = 0 := by linarith
        refine ⟨φ x / c, φ y / c, div_nonneg hx1 hc.le, div_nonneg hy1 hc.le, ?_, ?_⟩
        · rw [smul_smul, div_mul_cancel₀ _ hc.ne', hdec x, hx0]; simp [hφu, hψu, hφv, hψv]
        · rw [smul_smul, div_mul_cancel₀ _ hc.ne', hdec y, hy0]; simp [hφu, hψu, hφv, hψv]
    · subst h
      refine ⟨?_, ⟨by simp [hφv], by simp [hψv, hc.le]⟩, ?_⟩
      · intro h0; have := congrArg ψ h0; simp [hψv] at this; linarith
      · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ hxy
        have e1 := congrArg φ hxy; simp [hφv] at e1
        have hx0 : φ x = 0 := by linarith
        have hy0 : φ y = 0 := by linarith
        refine ⟨ψ x / c, ψ y / c, div_nonneg hx2 hc.le, div_nonneg hy2 hc.le, ?_, ?_⟩
        · rw [smul_smul, div_mul_cancel₀ _ hc.ne', hdec x, hx0]; simp [hψv]
        · rw [smul_smul, div_mul_cancel₀ _ hc.ne', hdec y, hy0]; simp [hψv]

lemma extremeRays_two (φ ψ : V →ₗ[ℝ] ℝ) (u v : V) (hφu : φ u = 1) (hψu : ψ u = 0)
    (hφv : φ v = 0) (hψv : ψ v = 1) (hdec : ∀ f, f = φ f • u + ψ f • v)
    (C : Set V) (hC : C = {f | 0 ≤ φ f ∧ 0 ≤ ψ f}) :
    extremeRays C = {ray u, ray v} := by
  have hE := extreme_two φ ψ u v hφu hψu hφv hψv hdec C hC
  ext R; constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨c, hc, h | h⟩ := (hE w).mp hw
    · left; rw [h, ray_smul u hc]
    · right; rw [h, ray_smul v hc]
  · rintro (rfl | rfl)
    · exact ⟨u, (hE u).mpr ⟨1, one_pos, Or.inl (one_smul _ _).symm⟩, rfl⟩
    · exact ⟨v, (hE v).mpr ⟨1, one_pos, Or.inr (one_smul _ _).symm⟩, rfl⟩

lemma finiteCone_two (φ ψ : V →ₗ[ℝ] ℝ) (u v : V) (hφu : φ u = 1) (hψu : ψ u = 0)
    (hφv : φ v = 0) (hψv : ψ v = 1) (hdec : ∀ f, f = φ f • u + ψ f • v) :
    finiteCone ({u, v} : Set V) = {f | 0 ≤ φ f ∧ 0 ≤ ψ f} := by
  ext f; constructor
  · rintro ⟨N, c, w, hcw, rfl⟩
    have key : ∀ i, 0 ≤ φ (c i • w i) ∧ 0 ≤ ψ (c i • w i) := by
      intro i
      obtain ⟨hc, hw⟩ := hcw i
      rcases hw with rfl | rfl
      · simp [hφu, hψu, hc]
      · simp [hφv, hψv, hc]
    simp only [Set.mem_setOf_eq, map_sum]
    exact ⟨Finset.sum_nonneg (fun i _ => (key i).1), Finset.sum_nonneg (fun i _ => (key i).2)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨2, ![φ f, ψ f], ![u, v], ?_, ?_⟩
    · intro i; fin_cases i
      · exact ⟨h1, by simp⟩
      · exact ⟨h2, by simp⟩
    · rw [Fin.sum_univ_two]; simpa using hdec f

end Generic

/-- Coordinates of `Coeff 2`. -/
def e2 : Coeff 2 →ₗ[ℝ] ℝ := Finsupp.lapply P2
def e11 : Coeff 2 →ₗ[ℝ] ℝ := Finsupp.lapply P11

lemma e2_apply (f : Coeff 2) : e2 f = f P2 := rfl
lemma e11_apply (f : Coeff 2) : e11 f = f P11 := rfl

/-- If `a d + b d² ≥ 0` for all positive naturals `d`, then `b ≥ 0`. -/
lemma quad_nonneg_coeff (a b : ℝ) (h : ∀ d : ℕ, 0 < d → 0 ≤ a * d + b * (d : ℝ) ^ 2) : 0 ≤ b := by
  by_contra hb
  push_neg at hb
  obtain ⟨d, hd⟩ := exists_nat_gt (|a / (-b)| + 1)
  have habs := le_abs_self (a / (-b))
  have habs0 := abs_nonneg (a / (-b))
  have hd0 : (0 : ℝ) < d := by linarith
  have hd1 : 0 < d := by exact_mod_cast hd0
  have := h d hd1
  have hab : a < -b * d := by
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < -b)).mp (by linarith : a / (-b) < d)
    linarith
  nlinarith

lemma ones_moments (d : ℕ) :
    (∑ _i : Fin d, (1 : ℝ) ^ 2) = d ∧ (∑ _i : Fin d, (1 : ℝ)) = d := by
  simp

end X7SmallDeg


open scoped BigOperators

namespace X7SmallDeg
open QAlgorithms.Papers.Independent.Information100.P19

lemma b2_P2 : b2 P2 = 1 := by simp [b2_eq]
lemma b2_P11 : b2 P11 = 0 := by simp [b2_eq, Finsupp.single_apply, P2_ne]
lemma b11_P2 : b11 P2 = 0 := by simp [b11_eq, Finsupp.single_apply, P2_ne.symm]
lemma b11_P11 : b11 P11 = 1 := by simp [b11_eq]

lemma value2 {d : ℕ} (f : Coeff 2) (x : Fin d → ℝ) :
    pairing f (spectralMoments x) = f P2 * ∑ i, x i ^ 2 + f P11 * (∑ i, x i) ^ 2 := by
  rw [pairing2, sm2, sm11]

lemma ones_value2 (f : Coeff 2) (d : ℕ) :
    pairing f (spectralMoments (fun _ : Fin d => (1 : ℝ))) = f P2 * d + f P11 * (d : ℝ) ^ 2 := by
  rw [value2]; simp

lemma allCone2_char : allCone 2 = {f : Coeff 2 | 0 ≤ e2 f ∧ 0 ≤ e11 f} := by
  ext f
  simp only [Set.mem_setOf_eq, e2_apply, e11_apply]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 2 (by norm_num) ![1, -1]
      rw [value2] at this; norm_num [Fin.sum_univ_two] at this; linarith
    · apply quad_nonneg_coeff (f P2)
      intro d hd
      have := h d hd (fun _ => 1)
      rwa [ones_value2] at this
  · rintro ⟨h1, h2⟩ d _ x
    rw [value2]
    have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity

lemma psdCone2_char :
    psdCone 2 = {f : Coeff 2 | 0 ≤ (e2 + e11) f ∧ 0 ≤ e11 f} := by
  ext f
  simp only [Set.mem_setOf_eq, LinearMap.add_apply, e2_apply, e11_apply]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 1 (by norm_num) ![1] (fun _ => by simp)
      rw [value2] at this; simpa using this
    · apply quad_nonneg_coeff (f P2)
      intro d hd
      have := h d hd (fun _ => 1) (fun _ => zero_le_one)
      rwa [ones_value2] at this
  · rintro ⟨h1, h2⟩ d _ x hx
    rw [value2]
    have hp2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hp := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := x) (fun i _ => hx i)
    have e : f P2 * ∑ i, x i ^ 2 + f P11 * (∑ i, x i) ^ 2 =
        (f P2 + f P11) * ∑ i, x i ^ 2 + f P11 * ((∑ i, x i) ^ 2 - ∑ i, x i ^ 2) := by ring
    rw [e]
    have : 0 ≤ (∑ i, x i) ^ 2 - ∑ i, x i ^ 2 := by linarith
    positivity

lemma dec_all (f : Coeff 2) : f = e2 f • b2 + e11 f • b11 := ext2 f

lemma dec_psd (f : Coeff 2) : f = (e2 + e11) f • b2 + e11 f • (b11 - b2) := by
  conv_lhs => rw [ext2 f]
  simp only [LinearMap.add_apply, e2_apply, e11_apply]
  module

lemma value1 {d : ℕ} (f : Coeff 1) (x : Fin d → ℝ) :
    pairing f (spectralMoments x) = f P1 * ∑ i, x i := by
  rw [pairing1, sm1]

lemma ext1 (f : Coeff 1) : f = f P1 • b1 := by
  ext p; rw [part1 p]; simp [b1_eq]

lemma value3 {d : ℕ} (f : Coeff 3) (x : Fin d → ℝ) :
    pairing f (spectralMoments x) = f P3 * ∑ i, x i ^ 3 +
      f P21 * ((∑ i, x i ^ 2) * ∑ i, x i) + f P111 * (∑ i, x i) ^ 3 := by
  rw [pairing3, sm3, sm21, sm111]

lemma pairing_zero {n : ℕ} (y : Part n → ℝ) : pairing (0 : Coeff n) y = 0 := by
  simp [pairing]

end X7SmallDeg

open QAlgorithms.Papers.Independent.Information100.P19 X7SmallDeg in
theorem solution :
    psdCone 1 = ray b1 ∧ extremeRays (psdCone 1) = {ray b1} ∧
    psdCone 2 = finiteCone ({b2,b11-b2} : Set (Coeff 2)) ∧
    extremeRays (psdCone 2) = {ray b2, ray (b11-b2)} := by
  have hφu : (e2 + e11) b2 = 1 := by simp [e2_apply, e11_apply, b2_P2, b2_P11]
  have hψu : e11 b2 = 0 := b2_P11
  have hφv : (e2 + e11) (b11 - b2) = 0 := by
    simp [e2_apply, e11_apply, b2_P2, b2_P11, b11_P2, b11_P11]
  have hψv : e11 (b11 - b2) = 1 := by simp [e11_apply, b2_P11, b11_P11]
  have hb1 : b1 P1 = 1 := by simp [b1_eq]
  have hC1 : psdCone 1 = {f : Coeff 1 | 0 ≤ f P1} := by
    ext f; simp only [Set.mem_setOf_eq]; constructor
    · intro h
      have := h 1 (by norm_num) ![1] (fun _ => by simp)
      rw [value1] at this; simpa using this
    · intro h d _ x hx
      rw [value1]; exact mul_nonneg h (Finset.sum_nonneg (fun i _ => hx i))
  have hray : ray b1 = {f : Coeff 1 | 0 ≤ f P1} := by
    ext f; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨c, hc, rfl⟩; simpa [hb1] using hc
    · intro h; exact ⟨f P1, h, ext1 f⟩
  refine ⟨hC1.trans hray.symm, ?_, ?_, ?_⟩
  · ext R
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨hw0, hwC, _⟩, rfl⟩
      rw [hC1] at hwC
      have hpos : 0 < w P1 := by
        rcases (show (0:ℝ) ≤ w P1 from hwC).lt_or_eq with h | h
        · exact h
        · exfalso; apply hw0; rw [ext1 w, ← h]; simp
      rw [ext1 w, ray_smul b1 hpos]
    · rintro rfl
      refine ⟨b1, ⟨?_, ?_, ?_⟩, rfl⟩
      · intro h; have := congrArg (fun g : Coeff 1 => g P1) h; simp [hb1] at this
      · rw [hC1]; simp [hb1]
      · rintro x hx y hy hxy
        rw [hC1] at hx hy
        exact ⟨x P1, y P1, hx, hy, ext1 x, ext1 y⟩
  · rw [finiteCone_two (e2 + e11) e11 b2 (b11 - b2) hφu hψu hφv hψv dec_psd, psdCone2_char]
  · exact extremeRays_two (e2 + e11) e11 b2 (b11 - b2) hφu hψu hφv hψv dec_psd _ psdCone2_char
