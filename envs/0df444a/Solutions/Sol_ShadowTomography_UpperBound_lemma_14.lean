-- Prove2me | solution 1 for ShadowTomography.UpperBound.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T12:26:25.33324+00:00
-- url     : https://prove2.me/submissions/636c061f-a5b9-46a0-94e0-bb6b6121b678

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

set_option autoImplicit false

open scoped ComplexOrder
open Matrix

namespace QOR14

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Conjugated diagonals (spectral calculus by hand) -/

noncomputable def cD {X : Matrix n n ℂ} (hX : X.IsHermitian) (d : n → ℝ) : Matrix n n ℂ :=
  (hX.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun j => ((d j : ℝ) : ℂ)) *
    (star hX.eigenvectorUnitary : Matrix n n ℂ)

section cDsec
variable {X : Matrix n n ℂ} (hX : X.IsHermitian)

lemma cD_eig : X = cD hX hX.eigenvalues := by
  conv_lhs => rw [hX.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp [cD, Function.comp_def]

lemma cD_mul (a b : n → ℝ) : cD hX a * cD hX b = cD hX (a * b) := by
  have hU : (star hX.eigenvectorUnitary : Matrix n n ℂ) * (hX.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_star_mul_self _
  unfold cD
  calc _ = (hX.eigenvectorUnitary : Matrix n n ℂ) * (diagonal (fun j => ((a j : ℝ) : ℂ)) *
        ((star hX.eigenvectorUnitary : Matrix n n ℂ) * (hX.eigenvectorUnitary : Matrix n n ℂ)) *
        diagonal (fun j => ((b j : ℝ) : ℂ))) * (star hX.eigenvectorUnitary : Matrix n n ℂ) := by
          simp only [mul_assoc]
    _ = _ := by
          rw [hU, mul_one, diagonal_mul_diagonal]
          congr 3
          ext j
          simp

lemma cD_sub (a b : n → ℝ) : cD hX a - cD hX b = cD hX (a - b) := by
  unfold cD
  rw [← sub_mul, ← mul_sub, diagonal_sub]
  congr 3
  ext j
  simp

lemma cD_const (t : ℝ) : cD hX (fun _ => t) = (t : ℂ) • (1 : Matrix n n ℂ) := by
  unfold cD
  have hU : (hX.eigenvectorUnitary : Matrix n n ℂ) * (star hX.eigenvectorUnitary : Matrix n n ℂ)
      = 1 := Unitary.coe_mul_star_self _
  rw [show diagonal (fun _ : n => ((t : ℝ) : ℂ)) = (t : ℂ) • (1 : Matrix n n ℂ) by
    ext i j; simp [diagonal, one_apply]]
  rw [mul_smul_comm, mul_one, smul_mul_assoc, hU]

lemma cD_smul (t : ℝ) (d : n → ℝ) : (t : ℂ) • cD hX d = cD hX (t • d) := by
  have e : t • d = (fun _ => t) * d := by ext j; simp
  rw [e, ← cD_mul, cD_const, smul_mul_assoc, one_mul]

lemma cD_mul_X (a : n → ℝ) : cD hX a * X = cD hX (a * hX.eigenvalues) := by
  conv_lhs => arg 2; rw [cD_eig hX]
  exact cD_mul hX _ _

lemma cD_psd (d : n → ℝ) (hd : ∀ j, 0 ≤ d j) : (cD hX d).PosSemidef := by
  unfold cD
  have h := (PosSemidef.diagonal (R := ℂ) (n := n) (d := fun j => ((d j : ℝ) : ℂ))
    (fun j => by simpa using hd j)).mul_mul_conjTranspose_same
    (hX.eigenvectorUnitary : Matrix n n ℂ)
  simpa [star_eq_conjTranspose] using h

lemma psd_factor {A : Matrix n n ℂ} (hA : A.PosSemidef) : ∃ B : Matrix n n ℂ, A = Bᴴ * B := by
  have hX := hA.isHermitian
  refine ⟨cD hX (fun j => Real.sqrt (hX.eigenvalues j)), ?_⟩
  have hH : (cD hX (fun j => Real.sqrt (hX.eigenvalues j)))ᴴ =
      cD hX (fun j => Real.sqrt (hX.eigenvalues j)) :=
    (cD_psd hX _ (fun j => Real.sqrt_nonneg _)).isHermitian
  rw [hH, cD_mul]
  conv_lhs => rw [cD_eig hX]
  congr 1
  ext j
  simp [Real.mul_self_sqrt (hA.eigenvalues_nonneg j)]

end cDsec

/-- The spectral cut of a PSD matrix at level `θ`. -/
lemma spec_cut {X : Matrix n n ℂ} (hX : X.PosSemidef) (θ : ℝ) (hθ : 0 < θ) :
    ∃ Q : Matrix n n ℂ, Q.PosSemidef ∧ (1 - Q).PosSemidef ∧ Q * Q = Q ∧
      ((θ : ℂ) • 1 - Q * X * Q).PosSemidef ∧ (X - (θ : ℂ) • (1 - Q)).PosSemidef := by
  have hH := hX.isHermitian
  set q : n → ℝ := fun j => if hH.eigenvalues j < θ then 1 else 0 with hq
  have h1 : (1 : Matrix n n ℂ) = cD hH (fun _ => 1) := by rw [cD_const]; simp
  refine ⟨cD hH q, cD_psd hH q (fun j => by simp only [hq]; split_ifs <;> norm_num), ?_, ?_, ?_, ?_⟩
  · rw [h1, cD_sub]
    exact cD_psd hH _ (fun j => by simp only [Pi.sub_apply, hq]; split_ifs <;> norm_num)
  · rw [cD_mul]
    congr 1
    ext j
    simp only [Pi.mul_apply, hq]
    split_ifs <;> norm_num
  · rw [cD_mul_X, cD_mul, ← cD_const, cD_sub]
    refine cD_psd hH _ (fun j => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply, hq]
    split_ifs with h
    · nlinarith
    · linarith
  · have e : X - (θ : ℂ) • (1 - cD hH q) = cD hH (hH.eigenvalues - θ • ((fun _ => 1) - q)) := by
      rw [h1, cD_sub, cD_smul, ← cD_sub]
      conv_lhs => arg 1; rw [cD_eig hH]
    rw [e]
    refine cD_psd hH _ (fun j => ?_)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq]
    have := hX.eigenvalues_nonneg j
    split_ifs with h
    · linarith
    · push_neg at h; linarith

/-! ### Trace toolkit -/

lemma tr_nonneg {Y σ : Matrix n n ℂ} (hY : Y.PosSemidef) (hσ : σ.PosSemidef) :
    0 ≤ (Y * σ).trace := by
  obtain ⟨B, rfl⟩ := psd_factor hY
  rw [mul_assoc, trace_mul_comm, mul_assoc]
  have := (hσ.mul_mul_conjTranspose_same B).trace_nonneg
  simpa [mul_assoc] using this

lemma tr_re_nonneg {Y σ : Matrix n n ℂ} (hY : Y.PosSemidef) (hσ : σ.PosSemidef) :
    0 ≤ (Y * σ).trace.re := (Complex.nonneg_iff.mp (tr_nonneg hY hσ)).1

lemma tr_re_mono {Y Y' σ : Matrix n n ℂ} (h : (Y' - Y).PosSemidef) (hσ : σ.PosSemidef) :
    (Y * σ).trace.re ≤ (Y' * σ).trace.re := by
  have := tr_re_nonneg h hσ
  rw [sub_mul, trace_sub, Complex.sub_re] at this
  linarith

/-- `Y - Y²` is PSD for an effect `Y`. -/
lemma eff_sq {Y : Matrix n n ℂ} (h0 : Y.PosSemidef) (h1 : (1 - Y).PosSemidef) :
    (Y - Y * Y).PosSemidef := by
  have e : Y - Y * Y = (1 - Y)ᴴ * Y * (1 - Y) + Yᴴ * (1 - Y) * Y := by
    rw [h1.isHermitian.eq, h0.isHermitian.eq]
    noncomm_ring
  rw [e]
  exact (h0.conjTranspose_mul_mul_same _).add (h1.conjTranspose_mul_mul_same _)

/-- If `θ Z - Z²` is PSD for Hermitian `Z` and `θ > 0`, then `θ - Z` is PSD. -/
lemma sq_le_bound {Z : Matrix n n ℂ} (hZ : Z.IsHermitian) (θ : ℝ) (hθ : 0 < θ)
    (h : ((θ : ℂ) • Z - Z * Z).PosSemidef) : ((θ : ℂ) • 1 - Z).PosSemidef := by
  have hW : ((θ : ℂ) • 1 - Z).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hZ.eq]
    simp
  have key : (θ : ℂ) • ((θ : ℂ) • 1 - Z) =
      ((θ : ℂ) • 1 - Z)ᴴ * 1 * ((θ : ℂ) • 1 - Z) + ((θ : ℂ) • Z - Z * Z) := by
    rw [hW.eq, mul_one]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
      smul_smul]
    abel
  have hpos : ((θ : ℂ) • ((θ : ℂ) • 1 - Z)).PosSemidef := by
    rw [key]
    exact (PosSemidef.one.conjTranspose_mul_mul_same _).add h
  have := hpos.smul (a := ((θ⁻¹ : ℝ) : ℂ)) (by
    rw [Complex.nonneg_iff]; simp [hθ.le])
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hθ.ne', Complex.ofReal_one,
    one_smul] at this
  exact this

/-- **The OR combination step.** -/
lemma or_case1 {X T Q σ : Matrix n n ℂ} (θ η : ℝ) (hθ : 0 < θ)
    (hT0 : T.PosSemidef) (hT1 : (1 - T).PosSemidef) (hXT : (X - T).PosSemidef)
    (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef) (hQQ : Q * Q = Q)
    (hQX : ((θ : ℂ) • 1 - Q * X * Q).PosSemidef)
    (hσ : σ.PosSemidef) (hσ1 : σ.trace = 1) (hη : ((1 - T) * σ).trace.re ≤ η) :
    (Q * σ).trace.re ≤ 2 * θ + 2 * η := by
  have hQH : Qᴴ = Q := hQ0.isHermitian.eq
  have hTH : Tᴴ = T := hT0.isHermitian.eq
  set a := Q * T with ha
  set b := Q * (1 - T) with hb
  -- a aᴴ ≤ θ
  have haa : ((θ : ℂ) • 1 - a * aᴴ).PosSemidef := by
    have e : (θ : ℂ) • 1 - a * aᴴ = ((θ : ℂ) • 1 - Q * X * Q) + Qᴴ * (X - T) * Q +
        Qᴴ * (T - T * T) * Q := by
      rw [ha, conjTranspose_mul, hQH, hTH]
      noncomm_ring
    rw [e]
    exact (hQX.add (hXT.conjTranspose_mul_mul_same Q)).add
      ((eff_sq hT0 hT1).conjTranspose_mul_mul_same Q)
  -- aᴴ a ≤ θ
  have hZ : ((θ : ℂ) • 1 - aᴴ * a).PosSemidef := by
    refine sq_le_bound (isHermitian_conjTranspose_mul_self a) θ hθ ?_
    have e : (θ : ℂ) • (aᴴ * a) - aᴴ * a * (aᴴ * a) = aᴴ * ((θ : ℂ) • 1 - a * aᴴ) * a := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, mul_assoc]
    rw [e]
    have := haa.conjTranspose_mul_mul_same a
    simpa using this
  -- bᴴ b ≤ 1 - T
  have hbb : ((1 - T) - bᴴ * b).PosSemidef := by
    have hb2 : bᴴ * b = (1 - T) * (Q * Q) * (1 - T) := by
      rw [hb, conjTranspose_mul, hQH, conjTranspose_sub, conjTranspose_one, hTH]
      noncomm_ring
    have e : (1 - T) - bᴴ * b = (1 - T)ᴴ * (1 - Q) * (1 - T) + ((1 - T) - (1 - T) * (1 - T)) := by
      rw [hb2, hQQ, conjTranspose_sub, conjTranspose_one, hTH]
      noncomm_ring
    rw [e]
    refine (hQ1.conjTranspose_mul_mul_same _).add ?_
    have h := eff_sq hT1 (by simpa using hT0)
    exact h
  -- the 2a2b inequality
  have hsplit : (aᴴ * a + aᴴ * a + bᴴ * b + bᴴ * b - Q).PosSemidef := by
    have hQ' : Q = a + b := by rw [ha, hb]; noncomm_ring
    have e : aᴴ * a + aᴴ * a + bᴴ * b + bᴴ * b - Q = (a - b)ᴴ * (a - b) := by
      have hQQ' : Q = (a + b)ᴴ * (a + b) := by
        rw [← hQ', hQH, hQQ]
      rw [conjTranspose_sub]
      conv_lhs => rw [hQQ']
      rw [conjTranspose_add]
      noncomm_ring
    rw [e]
    exact posSemidef_conjTranspose_mul_self _
  have h1 := tr_re_mono hsplit hσ
  have h2 := tr_re_mono hZ hσ
  have h3 := tr_re_mono hbb hσ
  have e1 : ((aᴴ * a + aᴴ * a + bᴴ * b + bᴴ * b) * σ).trace.re =
      2 * ((aᴴ * a) * σ).trace.re + 2 * ((bᴴ * b) * σ).trace.re := by
    simp only [add_mul, trace_add, Complex.add_re]
    ring
  have e2 : (((θ : ℂ) • 1) * σ).trace.re = θ := by
    rw [smul_mul_assoc, one_mul, trace_smul, hσ1]; simp
  linarith

/-! ### Product operators on `k` copies -/

section ProdOps
variable {k : ℕ}

def prodOp (F : Fin k → Matrix n n ℂ) : Matrix (Fin k → n) (Fin k → n) ℂ :=
  fun x y => ∏ j, F j (x j) (y j)

lemma prodOp_apply (F : Fin k → Matrix n n ℂ) (x y : Fin k → n) :
    prodOp F x y = ∏ j, F j (x j) (y j) := rfl

lemma prodOp_mul (F G : Fin k → Matrix n n ℂ) :
    prodOp F * prodOp G = prodOp (fun j => F j * G j) := by
  ext x y
  simp only [prodOp, mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma prodOp_trace (F : Fin k → Matrix n n ℂ) : (prodOp F).trace = ∏ j, (F j).trace := by
  simp only [Matrix.trace, Matrix.diag, prodOp]
  rw [Fintype.prod_sum]

lemma prodOp_conjTranspose (F : Fin k → Matrix n n ℂ) :
    (prodOp F)ᴴ = prodOp (fun j => (F j)ᴴ) := by
  ext x y
  simp [prodOp, conjTranspose_apply, star_prod]

lemma prodOp_psd (F : Fin k → Matrix n n ℂ) (h : ∀ j, (F j).PosSemidef) :
    (prodOp F).PosSemidef := by
  choose B hB using fun j => psd_factor (h j)
  have e : prodOp F = (prodOp B)ᴴ * prodOp B := by
    rw [prodOp_conjTranspose, prodOp_mul]
    congr 1
    funext j
    exact hB j
  rw [e]
  exact posSemidef_conjTranspose_mul_self _

def sel (E : Matrix n n ℂ) (S : Finset (Fin k)) : Fin k → Matrix n n ℂ :=
  fun j => if j ∈ S then E else 1 - E

lemma prod_ite_pow {R : Type*} [CommMonoid R] (S : Finset (Fin k)) (a b : R) :
    ∏ j, (if j ∈ S then a else b) = a ^ S.card * b ^ (k - S.card) := by
  rw [← Finset.prod_mul_prod_compl S,
    Finset.prod_congr rfl (fun j hj => if_pos hj),
    Finset.prod_congr rfl (fun j hj => if_neg (Finset.mem_compl.mp hj)),
    Finset.prod_const, Finset.prod_const, Finset.card_compl, Fintype.card_fin]

lemma sum_sel (E : Matrix n n ℂ) : ∑ S : Finset (Fin k), prodOp (sel E S) = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  have h : ∀ S : Finset (Fin k), prodOp (sel E S) x y =
      (∏ j ∈ S, E (x j) (y j)) * ∏ j ∈ Sᶜ, (1 - E) (x j) (y j) := by
    intro S
    rw [prodOp_apply, ← Finset.prod_mul_prod_compl S]
    congr 1
    · exact Finset.prod_congr rfl (fun j hj => by simp [sel, hj])
    · exact Finset.prod_congr rfl (fun j hj => by simp [sel, Finset.mem_compl.mp hj])
  simp_rw [h]
  have h2 := Fintype.prod_add (fun j => E (x j) (y j)) (fun j => (1 - E) (x j) (y j))
  rw [← h2]
  have h3 : ∀ j, E (x j) (y j) + (1 - E) (x j) (y j) = (1 : Matrix n n ℂ) (x j) (y j) :=
    fun j => by rw [Matrix.sub_apply]; ring
  rw [Finset.prod_congr rfl (fun j _ => h3 j)]
  by_cases hxy : x = y
  · subst hxy; simp [one_apply]
  · obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra hc; push_neg at hc; exact hxy (funext hc)
    rw [one_apply_ne hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (one_apply_ne hj)

lemma tr_sel (E ρ : Matrix n n ℂ) (p : ℝ) (hp : (E * ρ).trace = p) (hρ : ρ.trace = 1)
    (S : Finset (Fin k)) :
    (prodOp (sel E S) * prodOp (fun _ => ρ)).trace =
      ((p ^ S.card * (1 - p) ^ (k - S.card) : ℝ) : ℂ) := by
  rw [prodOp_mul, prodOp_trace]
  have : ∀ j, (sel E S j * ρ).trace = if j ∈ S then (p : ℂ) else 1 - p := by
    intro j
    unfold sel
    split_ifs
    · exact hp
    · rw [sub_mul, one_mul, trace_sub, hρ, hp]
  simp only [this]
  rw [prod_ite_pow]
  push_cast
  ring

lemma tr_sum_sel (E ρ : Matrix n n ℂ) (p : ℝ) (hp : (E * ρ).trace = p) (hρ : ρ.trace = 1)
    (P : Finset (Fin k) → Prop) [DecidablePred P] :
    ((∑ S ∈ Finset.univ.filter P, prodOp (sel E S)) * prodOp (fun _ => ρ)).trace.re =
      ∑ S ∈ Finset.univ.filter P, p ^ S.card * (1 - p) ^ (k - S.card) := by
  rw [Finset.sum_mul, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [tr_sel E ρ p hp hρ S, Complex.ofReal_re]

noncomputable def Tthr (E : Matrix n n ℂ) (b : ℝ) (k : ℕ) : Matrix (Fin k → n) (Fin k → n) ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => b * k ≤ S.card), prodOp (sel E S)

lemma Tthr_compl (E : Matrix n n ℂ) (b : ℝ) :
    1 - Tthr E b k =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => ¬ (b * k ≤ S.card)), prodOp (sel E S) := by
  rw [← sum_sel E (k := k), Tthr,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset (Fin k) => b * k ≤ S.card)]
  abel

lemma sel_psd {E : Matrix n n ℂ} (hE : ShadowTomography.UpperBound.IsEffect E)
    (S : Finset (Fin k)) : (prodOp (sel E S)).PosSemidef :=
  prodOp_psd _ (fun j => by unfold sel; split_ifs; exacts [hE.1, hE.2])

lemma Tthr_psd {E : Matrix n n ℂ} (hE : ShadowTomography.UpperBound.IsEffect E) (b : ℝ) :
    (Tthr E b k).PosSemidef :=
  posSemidef_sum _ (fun S _ => sel_psd hE S)

lemma Tthr_compl_psd {E : Matrix n n ℂ} (hE : ShadowTomography.UpperBound.IsEffect E) (b : ℝ) :
    (1 - Tthr E b k).PosSemidef := by
  rw [Tthr_compl]
  exact posSemidef_sum _ (fun S _ => sel_psd hE S)

end ProdOps

/-! ### Chernoff bounds -/

lemma binom_mgf (p s : ℝ) (k : ℕ) :
    ∑ S : Finset (Fin k), p ^ S.card * (1 - p) ^ (k - S.card) * Real.exp (s * S.card) =
      (p * Real.exp s + (1 - p)) ^ k := by
  have h := Finset.sum_pow_mul_eq_add_pow (p * Real.exp s) (1 - p) (Finset.univ : Finset (Fin k))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [mul_pow, ← Real.exp_nat_mul, mul_comm (S.card : ℝ) s]
  ring

lemma mgf_le (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : |s| ≤ 1) (k : ℕ) :
    ∑ S : Finset (Fin k), p ^ S.card * (1 - p) ^ (k - S.card) * Real.exp (s * S.card) ≤
      Real.exp (k * (p * s + s ^ 2)) := by
  rw [binom_mgf]
  have hb : Real.exp s - 1 - s ≤ s ^ 2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hs)).2
  have h1 : p * Real.exp s + (1 - p) ≤ Real.exp (p * s + s ^ 2) := by
    have h2 := Real.add_one_le_exp (p * (Real.exp s - 1))
    have h3 : p * (Real.exp s - 1) ≤ p * s + s ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hb hp0, mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg s)]
    calc p * Real.exp s + (1 - p) = p * (Real.exp s - 1) + 1 := by ring
      _ ≤ Real.exp (p * (Real.exp s - 1)) := h2
      _ ≤ _ := Real.exp_le_exp.mpr h3
  have h0 : 0 ≤ p * Real.exp s + (1 - p) := by nlinarith [Real.exp_pos s]
  calc (p * Real.exp s + (1 - p)) ^ k ≤ (Real.exp (p * s + s ^ 2)) ^ k :=
        pow_le_pow_left₀ h0 h1 k
    _ = _ := by rw [← Real.exp_nat_mul]

lemma tail (p b s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : |s| ≤ 1) (k : ℕ)
    (P : Finset (Fin k) → Prop) [DecidablePred P]
    (hP : ∀ S, P S → 0 ≤ s * (S.card - b * k)) :
    ∑ S ∈ Finset.univ.filter P, p ^ S.card * (1 - p) ^ (k - S.card) ≤
      Real.exp (k * (s * (p - b) + s ^ 2)) := by
  have ht : ∀ S : Finset (Fin k), 0 ≤ p ^ S.card * (1 - p) ^ (k - S.card) := fun S =>
    mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  calc ∑ S ∈ Finset.univ.filter P, p ^ S.card * (1 - p) ^ (k - S.card)
      ≤ ∑ S ∈ Finset.univ.filter P, Real.exp (-(s * b * k)) *
          (p ^ S.card * (1 - p) ^ (k - S.card) * Real.exp (s * S.card)) := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        have hS' := hP S (Finset.mem_filter.mp hS).2
        have h1 : 1 ≤ Real.exp (-(s * b * k)) * Real.exp (s * S.card) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
        nlinarith [mul_le_mul_of_nonneg_right h1 (ht S)]
    _ ≤ ∑ S : Finset (Fin k), Real.exp (-(s * b * k)) *
          (p ^ S.card * (1 - p) ^ (k - S.card) * Real.exp (s * S.card)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S _ _ => mul_nonneg (Real.exp_pos _).le (mul_nonneg (ht S) (Real.exp_pos _).le))
    _ = Real.exp (-(s * b * k)) * ∑ S : Finset (Fin k),
          p ^ S.card * (1 - p) ^ (k - S.card) * Real.exp (s * S.card) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(s * b * k)) * Real.exp (k * (p * s + s ^ 2)) :=
        mul_le_mul_of_nonneg_left (mgf_le p s hp0 hp1 hs k) (Real.exp_pos _).le
    _ = Real.exp (k * (s * (p - b) + s ^ 2)) := by rw [← Real.exp_add]; congr 1; ring

lemma eff_tr_bounds {E ρ : Matrix n n ℂ} (hE : ShadowTomography.UpperBound.IsEffect E)
    (hρ : WildeQIT.IsDensityOperator ρ) :
    (E * ρ).trace = (((E * ρ).trace.re : ℝ) : ℂ) ∧ 0 ≤ (E * ρ).trace.re ∧
      (E * ρ).trace.re ≤ 1 := by
  refine ⟨?_, tr_re_nonneg hE.1 hρ.1, ?_⟩
  · have := Complex.nonneg_iff.mp (tr_nonneg hE.1 hρ.1)
    exact Complex.ext (by simp) (by simp [this.2.symm])
  · have := tr_re_nonneg hE.2 hρ.1
    rw [sub_mul, one_mul, trace_sub, hρ.2] at this
    simp at this
    linarith

lemma k0 (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ShadowTomography.UpperBound.IsEffect ((a : ℂ) • (1 : Matrix (Fin 0 → n) (Fin 0 → n) ℂ)) ∧
      ∀ ρ : Matrix n n ℂ,
        (((a : ℂ) • (1 : Matrix (Fin 0 → n) (Fin 0 → n) ℂ)) *
          ShadowTomography.UpperBound.tensorPow ρ 0).trace.re = a := by
  refine ⟨⟨PosSemidef.one.smul (Complex.zero_le_real.mpr ha0), ?_⟩, fun ρ => ?_⟩
  · rw [show (1 : Matrix (Fin 0 → n) (Fin 0 → n) ℂ) - (a : ℂ) • 1 = ((1 - a : ℝ) : ℂ) • 1 by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]]
    exact PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith))
  · simp [Matrix.trace, Matrix.mul_apply, ShadowTomography.UpperBound.tensorPow,
      Fintype.sum_unique]

end QOR14

set_option maxHeartbeats 1000000 in
open QOR14 in
open ShadowTomography.UpperBound in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (M : ℕ) (E : Fin M → Matrix n n ℂ) (c ε δ : ℝ),
        2 ≤ M → (∀ i, IsEffect (E i)) → 0 < ε → 0 < δ → δ < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C * (Real.log (1 / δ) / ε ^ 2) * Real.log M ∧
          ∃ A : Matrix (Fin k → n) (Fin k → n) ℂ, IsEffect A ∧
            ∀ ρ : Matrix n n ℂ, WildeQIT.IsDensityOperator ρ →
              ((∃ i, c ≤ ((E i) * ρ).trace.re) → 1 - δ ≤ (A * tensorPow ρ k).trace.re) ∧
              ((∀ i, ((E i) * ρ).trace.re ≤ c - ε) → (A * tensorPow ρ k).trace.re ≤ δ) := by
  refine ⟨200, by norm_num, ?_⟩
  intro n _ _ M E c ε δ hM hE hε hδ0 hδ1
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have hB0 : (0 : ℝ) ≤ 200 * (Real.log (1 / δ) / ε ^ 2) * Real.log M := by positivity
  by_cases hδh : 1 / 2 ≤ δ
  · obtain ⟨hA, htr⟩ := k0 (n := n) (1 / 2) (by norm_num) (by norm_num)
    refine ⟨0, by simpa using hB0, _, hA, fun ρ _ => ⟨fun _ => ?_, fun _ => ?_⟩⟩ <;>
      rw [htr] <;> linarith
  by_cases hc1 : 1 < c
  · obtain ⟨hA, htr⟩ := k0 (n := n) 0 le_rfl (by norm_num)
    refine ⟨0, by simpa using hB0, _, hA, fun ρ hρ => ⟨fun ⟨i, hi⟩ => ?_, fun _ => ?_⟩⟩
    · have := (eff_tr_bounds (hE i) hρ).2.2; linarith
    · rw [htr]; linarith
  by_cases hc0 : c - ε < 0
  · obtain ⟨hA, htr⟩ := k0 (n := n) 1 (by norm_num) le_rfl
    refine ⟨0, by simpa using hB0, _, hA, fun ρ hρ => ⟨fun _ => ?_, fun h => ?_⟩⟩
    · rw [htr]; linarith
    · have h1 := (eff_tr_bounds (hE ⟨0, by omega⟩) hρ).2.1
      have h2 := h ⟨0, by omega⟩
      linarith
  push_neg at hδh hc1 hc0
  have hε1 : ε ≤ 1 := by linarith
  -- parameters
  set a := Real.log (1 / δ) with ha
  set m := Real.log (M : ℝ) with hm
  have hl2 := Real.log_two_gt_d9
  have hm2 : Real.log 2 ≤ m := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have ha2 : Real.log 2 ≤ a := Real.log_le_log (by norm_num)
    (by rw [le_div_iff₀ hδ0]; linarith)
  set L := Real.log (4 * M / δ ^ 2) with hL
  have hLeq : L = 2 * Real.log 2 + m + 2 * a := by
    rw [hL, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, ha, one_div, Real.log_inv,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hL0 : 0 ≤ L := by rw [hLeq]; linarith
  set k := ⌈16 * L / ε ^ 2⌉₊ with hk
  have hε2 : 0 < ε ^ 2 := by positivity
  have hkup : (k : ℝ) < 16 * L / ε ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hklo : 16 * L / ε ^ 2 ≤ k := Nat.le_ceil _
  have hkB : (k : ℝ) ≤ 200 * (a / ε ^ 2) * m := by
    have key : 16 * L + ε ^ 2 ≤ 200 * a * m := by
      rw [hLeq]
      nlinarith [mul_le_mul_of_nonneg_left hm2 (by linarith : (0 : ℝ) ≤ a),
        mul_le_mul_of_nonneg_left ha2 (by linarith : (0 : ℝ) ≤ m)]
    have : 16 * L / ε ^ 2 + 1 = (16 * L + ε ^ 2) / ε ^ 2 := by field_simp
    rw [this] at hkup
    have h2 : (16 * L + ε ^ 2) / ε ^ 2 ≤ 200 * a * m / ε ^ 2 :=
      div_le_div_of_nonneg_right key hε2.le
    calc (k : ℝ) ≤ 200 * a * m / ε ^ 2 := by linarith
      _ = 200 * (a / ε ^ 2) * m := by ring
  set η := Real.exp (-(k * ε ^ 2 / 16)) with hη
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hη4 : η * (4 * M) ≤ δ ^ 2 := by
    have h1 : η ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by
      have := (div_le_iff₀ hε2).mp hklo
      nlinarith)
    have h2 : Real.exp (-L) = δ ^ 2 / (4 * M) := by
      rw [Real.exp_neg, hL, Real.exp_log (by positivity), inv_div]
    rw [h2] at h1
    rwa [le_div_iff₀ (by positivity)] at h1
  -- operators
  set b := c - ε / 2 with hb
  set T : Fin M → Matrix (Fin k → n) (Fin k → n) ℂ := fun i => Tthr (E i) b k with hT
  set X := ∑ i, T i with hX
  have hXpsd : X.PosSemidef := posSemidef_sum _ (fun i _ => Tthr_psd (hE i) b)
  obtain ⟨Q, hQ0, hQ1, hQQ, hQX, hXQ⟩ := spec_cut hXpsd (δ / 4) (by positivity)
  refine ⟨k, hkB, 1 - Q, ⟨hQ1, by simpa using hQ0⟩, fun ρ hρ => ?_⟩
  have hσ : (tensorPow ρ k).PosSemidef := prodOp_psd _ (fun _ => hρ.1)
  have hσ1 : (tensorPow ρ k).trace = 1 := by
    show (prodOp (fun _ : Fin k => ρ)).trace = 1
    rw [prodOp_trace]; simp [hρ.2]
  have hA : ((1 - Q) * tensorPow ρ k).trace.re = 1 - (Q * tensorPow ρ k).trace.re := by
    rw [sub_mul, one_mul, trace_sub, hσ1]; simp
  have hTi : ∀ i, (T i * tensorPow ρ k).trace.re =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => b * k ≤ S.card),
        ((E i) * ρ).trace.re ^ S.card * (1 - ((E i) * ρ).trace.re) ^ (k - S.card) := fun i =>
    tr_sum_sel (E i) ρ _ (eff_tr_bounds (hE i) hρ).1 hρ.2 _
  have hTc : ∀ i, ((1 - T i) * tensorPow ρ k).trace.re =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin k) => ¬ (b * k ≤ S.card)),
        ((E i) * ρ).trace.re ^ S.card * (1 - ((E i) * ρ).trace.re) ^ (k - S.card) := by
    intro i
    simp only [hT]
    rw [Tthr_compl]
    exact tr_sum_sel (E i) ρ _ (eff_tr_bounds (hE i) hρ).1 hρ.2 _
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨-, hp0, hp1⟩ := eff_tr_bounds (hE i) hρ
    have hs : |(-(ε / 4))| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have htail := tail _ b (-(ε / 4)) hp0 hp1 hs k
      (fun S : Finset (Fin k) => ¬ (b * k ≤ S.card))
      (fun S hS => by push_neg at hS; nlinarith)
    have hη1 : ((1 - T i) * tensorPow ρ k).trace.re ≤ η := by
      rw [hTc i]
      refine htail.trans (Real.exp_le_exp.mpr ?_)
      have : -(ε / 4) * (((E i) * ρ).trace.re - b) + (-(ε / 4)) ^ 2 ≤ -(ε ^ 2 / 16) := by
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg k)]
    have hXT : (X - T i).PosSemidef := by
      rw [hX, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
      exact posSemidef_sum _ (fun j _ => Tthr_psd (hE j) b)
    have hT0 : (T i).PosSemidef := Tthr_psd (hE i) b
    have hT1 : (1 - T i).PosSemidef := Tthr_compl_psd (hE i) b
    have hθ : (0 : ℝ) < δ / 4 := by positivity
    have := or_case1 (X := X) (T := T i) (Q := Q) (σ := tensorPow ρ k) (δ / 4) η hθ hT0 hT1 hXT
      hQ0 hQ1 hQQ hQX hσ hσ1 hη1
    have h8 : η * 8 ≤ η * (4 * M) := mul_le_mul_of_nonneg_left (by linarith [hM2]) hη0
    have hδδ : δ ^ 2 ≤ δ := by nlinarith
    have hηδ : η ≤ δ / 4 := by linarith
    rw [hA]
    linarith
  · intro hall
    have hTη : ∀ i, (T i * tensorPow ρ k).trace.re ≤ η := by
      intro i
      obtain ⟨-, hp0, hp1⟩ := eff_tr_bounds (hE i) hρ
      have hs : |ε / 4| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have htail := tail _ b (ε / 4) hp0 hp1 hs k
        (fun S : Finset (Fin k) => b * k ≤ S.card) (fun S hS => by nlinarith)
      rw [hTi i]
      refine htail.trans (Real.exp_le_exp.mpr ?_)
      have hi := hall i
      have : ε / 4 * (((E i) * ρ).trace.re - b) + (ε / 4) ^ 2 ≤ -(ε ^ 2 / 16) := by
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg k)]
    have hXs : (X * tensorPow ρ k).trace.re ≤ M * η := by
      rw [hX, Finset.sum_mul, trace_sum, Complex.re_sum]
      calc ∑ i, (T i * tensorPow ρ k).trace.re ≤ ∑ _i : Fin M, η :=
            Finset.sum_le_sum (fun i _ => hTη i)
        _ = M * η := by simp
    have hmono := tr_re_mono hXQ hσ
    rw [smul_mul_assoc, trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at hmono
    rw [hA] at hmono ⊢
    have hd : δ / 4 * (1 - (Q * tensorPow ρ k).trace.re) ≤ δ ^ 2 / 4 := by nlinarith
    nlinarith
