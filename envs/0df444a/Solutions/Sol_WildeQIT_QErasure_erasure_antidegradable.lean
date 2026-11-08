-- Prove2me | solution 1 for WildeQIT.QErasure.erasure_antidegradable
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:18:05.696435+00:00
-- url     : https://prove2.me/submissions/444b0d32-f956-4b72-8961-093105a44b1b

import Definitions.Def_WildeQIT_QErasure_IsAntidegradable
import Definitions.Def_WildeQIT_QErasure_erasureChannel

namespace Aux_Erasure_anti
open WildeQIT WildeQIT.Degradable WildeQIT.QErasure Matrix

variable {a : Type} [Fintype a] [DecidableEq a]

theorem sq_sqrt_c (r : ℝ) (hr : 0 ≤ r) : ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]

noncomputable def K0 (ε : ℝ) : Matrix (Option a) a ℂ :=
  Matrix.of fun y x => if y = some x then ((Real.sqrt (1 - ε) : ℝ) : ℂ) else 0
noncomputable def K1 (ε : ℝ) (i : a) : Matrix (Option a) a ℂ :=
  Matrix.of fun y x => if y = none ∧ x = i then ((Real.sqrt ε : ℝ) : ℂ) else 0

theorem N_eq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (X : Matrix a a ℂ) :
    (erasureChannel a ε h0 h1).apply X =
      K0 ε * X * (K0 ε)ᴴ + ∑ i, K1 ε i * X * (K1 ε i)ᴴ := by
  unfold QChannel.apply
  dsimp only [erasureChannel]
  first
    | (erw [Fintype.sum_option]; done)
    | (erw [Fintype.sum_option]; rfl)
    | (simp only [Fintype.sum_option]; done)
    | (simp only [Fintype.sum_option]; rfl)
    | exact Fintype.sum_option (fun k : Option a => _)

theorem N_ss (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) (x x' : a) :
    (erasureChannel a ε h0 h1).apply ρ (some x) (some x') = ((1 - ε : ℝ) : ℂ) * ρ x x' := by
  rw [N_eq]
  simp [K0, K1, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite star,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.conj_ofReal]
  have e := sq_sqrt_c (1 - ε) (by linarith)
  push_cast at e ⊢
  linear_combination ρ x x' * e

theorem N_nn (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) :
    (erasureChannel a ε h0 h1).apply ρ none none = (ε : ℂ) * ρ.trace := by
  rw [N_eq]
  simp [K0, K1, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite star,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.conj_ofReal, Matrix.trace]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sq_sqrt_c ε h0]; ring

theorem N_ns (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) (x : a) :
    (erasureChannel a ε h0 h1).apply ρ none (some x) = 0 := by
  rw [N_eq]
  simp [K0, K1, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite star,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem N_sn (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) (x : a) :
    (erasureChannel a ε h0 h1).apply ρ (some x) none = 0 := by
  rw [N_eq]
  simp [K0, K1, Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite star,
    Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem Nc_entry (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ)
    (k l : (erasureChannel a ε h0 h1).ι) :
    complementaryApply (erasureChannel a ε h0 h1) ρ k l =
      ∑ y, ∑ x', (∑ x, (erasureChannel a ε h0 h1).K k y x * ρ x x') *
        star ((erasureChannel a ε h0 h1).K l y x') := by
  simp [complementaryApply, partialTraceLeft, isometricExtension, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

theorem Nc_ss (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) (i j : a) :
    complementaryApply (erasureChannel a ε h0 h1) ρ (some i) (some j) = (ε : ℂ) * ρ i j := by
  dsimp only [complementaryApply, partialTraceLeft, isometricExtension, erasureChannel]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_option, apply_ite star,
    apply_ite (starRingEnd ℂ), mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Complex.conj_ofReal]
  have e := sq_sqrt_c ε h0
  linear_combination ρ i j * e

theorem Nc_nn (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) :
    complementaryApply (erasureChannel a ε h0 h1) ρ none none = ((1 - ε : ℝ) : ℂ) * ρ.trace := by
  dsimp only [complementaryApply, partialTraceLeft, isometricExtension, erasureChannel]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_option, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq',
    apply_ite (starRingEnd ℂ), mul_ite, ite_mul, mul_zero, zero_mul,
    Complex.conj_ofReal, Matrix.trace]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have e := sq_sqrt_c (1 - ε) (by linarith)
  push_cast at e ⊢
  linear_combination ρ i i * e

theorem Nc_ns (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) (j : a) :
    complementaryApply (erasureChannel a ε h0 h1) ρ none (some j) = 0 := by
  dsimp only [complementaryApply, partialTraceLeft, isometricExtension, erasureChannel]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_option, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem Nc_sn (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix a a ℂ) (j : a) :
    complementaryApply (erasureChannel a ε h0 h1) ρ (some j) none = 0 := by
  dsimp only [complementaryApply, partialTraceLeft, isometricExtension, erasureChannel]
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_option, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq']

noncomputable def D0 (p : ℝ) : Matrix (Option a) (Option a) ℂ :=
  Matrix.of fun y z => if y = z ∧ y ≠ none then ((Real.sqrt p : ℝ) : ℂ) else 0
noncomputable def D1 : Matrix (Option a) (Option a) ℂ :=
  Matrix.of fun y z => if y = none ∧ z = none then 1 else 0
noncomputable def D2 (p : ℝ) (i : a) : Matrix (Option a) (Option a) ℂ :=
  Matrix.of fun y z => if y = none ∧ z = some i then ((Real.sqrt (1 - p) : ℝ) : ℂ) else 0

noncomputable def Dk (p : ℝ) : Option (Option a) → Matrix (Option a) (Option a) ℂ
  | none => D0 p
  | some none => D1
  | some (some i) => D2 p i

theorem Dk_sum (p : ℝ) (f : Matrix (Option a) (Option a) ℂ → Matrix (Option a) (Option a) ℂ) :
    ∑ k : Option (Option a), f (Dk p k) = f (D0 p) + (f D1 + ∑ i, f (D2 p i)) := by
  rw [Fintype.sum_option, Fintype.sum_option]; rfl

noncomputable def Dch (inst : DecidableEq (Option a)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    @QChannel (Option a) (Option a) _ _ inst where
  ι := Option (Option a)
  K := Dk p
  complete := by
    have hs1 := sq_sqrt_c p hp0
    have hs2 := sq_sqrt_c (1 - p) (by linarith)
    rw [Dk_sum p (fun K => Kᴴ * K)]
    ext z z'
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      D0, D1, D2, Matrix.of_apply]
    rcases z with _ | i <;> rcases z' with _ | j
    · simp [Fintype.sum_option, Matrix.one_apply]
    · simp [Fintype.sum_option, Matrix.one_apply]
    · simp [Fintype.sum_option, Matrix.one_apply]
    · by_cases hij : i = j
      · subst hij
        simp [Fintype.sum_option, Matrix.one_apply, hs1, hs2, apply_ite star, Finset.sum_ite_eq',
          Finset.sum_ite_eq, Complex.conj_ofReal]
        try (rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt hp0,
          Real.mul_self_sqrt (by linarith)]
             push_cast; ring)
      · simp [Fintype.sum_option, Matrix.one_apply, hij, apply_ite star, Finset.sum_ite_eq',
          Finset.sum_ite_eq, Complex.conj_ofReal]
        intro h; exact absurd h.symm hij

theorem D_eq (inst : DecidableEq (Option a)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Option a) (Option a) ℂ) :
    (Dch inst p hp0 hp1).apply σ = D0 p * σ * (D0 p)ᴴ + (D1 * σ * D1ᴴ + ∑ i, D2 p i * σ * (D2 p i)ᴴ) := by
  unfold QChannel.apply
  exact Dk_sum p (fun K => K * σ * Kᴴ)

theorem D_ss (inst : DecidableEq (Option a)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Option a) (Option a) ℂ) (i j : a) :
    (Dch inst p hp0 hp1).apply σ (some i) (some j) = (p : ℂ) * σ (some i) (some j) := by
  rw [D_eq]
  simp [D0, D1, D2, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_option,
    Matrix.conjTranspose_apply, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Complex.conj_ofReal]
  rw [← sq_sqrt_c p hp0]; ring

theorem D_nn (inst : DecidableEq (Option a)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Option a) (Option a) ℂ) :
    (Dch inst p hp0 hp1).apply σ none none =
      σ none none + ((1 - p : ℝ) : ℂ) * ∑ i, σ (some i) (some i) := by
  rw [D_eq]
  simp [D0, D1, D2, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_option,
    Matrix.conjTranspose_apply, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Complex.conj_ofReal]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have := sq_sqrt_c (1 - p) (by linarith)
  push_cast at this ⊢
  linear_combination (σ (some i) (some i)) * this

theorem D_ns (inst : DecidableEq (Option a)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Option a) (Option a) ℂ) (j : a) :
    (Dch inst p hp0 hp1).apply σ none (some j) = 0 := by
  rw [D_eq]
  simp [D0, D1, D2, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_option,
    Matrix.conjTranspose_apply, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem D_sn (inst : DecidableEq (Option a)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : Matrix (Option a) (Option a) ℂ) (j : a) :
    (Dch inst p hp0 hp1).apply σ (some j) none = 0 := by
  rw [D_eq]
  simp [D0, D1, D2, Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_option,
    Matrix.conjTranspose_apply, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq']

end Aux_Erasure_anti

open WildeQIT WildeQIT.Degradable WildeQIT.QErasure Aux_Erasure_anti in
theorem solution (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (hε : 1 / 2 ≤ ε) :
    IsAntidegradable (erasureChannel a ε h0 h1) := by
  have hεpos : 0 < ε := by linarith
  set p := (1 - ε) / ε with hp
  have hp0 : 0 ≤ p := div_nonneg (by linarith) hεpos.le
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hεpos]; linarith
  refine ⟨Dch (fun x y => Classical.propDecidable (x = y)) p hp0 hp1, fun ρ _ => ?_⟩
  have hpe : (p : ℂ) * (ε : ℂ) = ((1 - ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hp, div_mul_cancel₀ _ hεpos.ne']
  ext y y'
  rcases y with _ | i <;> rcases y' with _ | j
  · erw [D_nn, Nc_nn, N_nn]
    simp only [Nc_ss]
    rw [← Finset.mul_sum]
    have htr : ∑ i, ρ i i = ρ.trace := rfl
    rw [htr]
    have : ((1 - p : ℝ) : ℂ) * (ε : ℂ) = ((2 * ε - 1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1; rw [hp]; field_simp; ring
    push_cast at this ⊢
    linear_combination (ρ.trace) * this
  · erw [D_ns, N_ns]
  · erw [D_sn, N_sn]
  · erw [D_ss, Nc_ss, N_ss]
    rw [← mul_assoc, hpe]
