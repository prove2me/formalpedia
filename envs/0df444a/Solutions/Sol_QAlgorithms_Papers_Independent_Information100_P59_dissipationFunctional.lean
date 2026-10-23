-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.dissipationFunctional
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:28:23.132017+00:00
-- url     : https://prove2.me/submissions/1d984693-c280-4c0c-9ac2-3e26d2de8c76

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59.DF890

open QAlgorithms.Papers.Independent.Information100.P59

lemma st_add {d : ℕ} (f g : Operator d → Operator d) :
    superoperatorTrace (fun X => f X + g X) = superoperatorTrace f + superoperatorTrace g := by
  unfold superoperatorTrace
  simp [Matrix.add_apply, Finset.sum_add_distrib]

lemma st_sub {d : ℕ} (f g : Operator d → Operator d) :
    superoperatorTrace (fun X => f X - g X) = superoperatorTrace f - superoperatorTrace g := by
  unfold superoperatorTrace
  simp [Matrix.sub_apply, Finset.sum_sub_distrib]

lemma st_smul {d : ℕ} (c : ℂ) (f : Operator d → Operator d) :
    superoperatorTrace (fun X => c • f X) = c * superoperatorTrace f := by
  unfold superoperatorTrace
  simp [Matrix.smul_apply, Finset.mul_sum]

lemma st_neg {d : ℕ} (f : Operator d → Operator d) :
    superoperatorTrace (-f) = - superoperatorTrace f := by
  unfold superoperatorTrace
  simp [Finset.sum_neg_distrib]

lemma st_rsmul {d : ℕ} (c : ℝ) (f : Operator d → Operator d) :
    superoperatorTrace (c • f) = (c : ℂ) * superoperatorTrace f := by
  unfold superoperatorTrace
  simp [Finset.mul_sum, Complex.real_smul]

lemma st_padd {d : ℕ} (f g : Operator d → Operator d) :
    superoperatorTrace (f + g) = superoperatorTrace f + superoperatorTrace g := by
  unfold superoperatorTrace
  simp [Finset.sum_add_distrib]

lemma st_sum {d : ℕ} {ι : Type} (s : Finset ι) (f : ι → Operator d → Operator d) :
    superoperatorTrace (fun X => ∑ j ∈ s, f j X) = ∑ j ∈ s, superoperatorTrace (f j) := by
  unfold superoperatorTrace
  simp only [Matrix.sum_apply]
  conv_rhs => rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm (s := s)]

lemma st_lmr {d : ℕ} (A B : Operator d) :
    superoperatorTrace (fun X => A * X * B) = A.trace * B.trace := by
  unfold superoperatorTrace
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.trace, Matrix.diag]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [ite_and]

lemma st_lm {d : ℕ} (A : Operator d) :
    superoperatorTrace (fun X => A * X) = A.trace * d := by
  have h := st_lmr A (1 : Operator d)
  simp only [mul_one, Matrix.trace_one, Fintype.card_fin] at h
  exact h

lemma st_rm {d : ℕ} (A : Operator d) :
    superoperatorTrace (fun X => X * A) = d * A.trace := by
  have h := st_lmr (1 : Operator d) A
  simp only [one_mul, Matrix.trace_one, Fintype.card_fin] at h
  exact h

lemma st_coherent {d : ℕ} (H : Operator d) : superoperatorTrace (coherent H) = 0 := by
  have : coherent H = fun X => -Complex.I • (H * X - X * H) := rfl
  rw [this, st_smul, st_sub, st_lm, st_rm]
  ring

lemma st_koss {d : ℕ} (F : Fin (d^2-1) → Operator d) (H : Operator d)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) :
    superoperatorTrace (kossakowskiAction F H K) =
      ∑ j, ∑ k, K j k * ((F j).trace * ((F k)ᴴ).trace -
        (2⁻¹ : ℂ) * (((F k)ᴴ * F j).trace * d + d * ((F k)ᴴ * F j).trace)) := by
  have : kossakowskiAction F H K = fun X => coherent H X + ∑ j, ∑ k, K j k •
      (F j * X * (F k)ᴴ - (2⁻¹ : ℂ) • ((F k)ᴴ * F j * X + X * ((F k)ᴴ * F j))) := by
    funext X; simp only [kossakowskiAction, mul_assoc]
  rw [this, st_add, st_coherent, zero_add, st_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [st_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [st_smul, st_sub, st_lmr, st_smul, st_add, st_lm, st_rm]

theorem conj1 {d : ℕ} (F : Fin (d^2-1) → Operator d) (hF : IsTracelessHermitianBasis F)
    (H : Operator d) (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) :
    superoperatorTrace (kossakowskiAction F H K) = -(d : ℂ) * (K * gramMatrix F).trace := by
  have hR : (K * gramMatrix F).trace = ∑ j, ∑ k, K j k * (F j * F k).trace := by
    show ∑ j, (K * gramMatrix F) j j = _
    simp only [Matrix.mul_apply, gramMatrix]
  rw [st_koss, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hj : (F j).trace = 0 := (hF.1 j).2
  have hk : (F k)ᴴ = F k := (hF.1 k).1
  rw [hk, hj, Matrix.trace_mul_comm (F k) (F j)]
  ring

lemma herm_comm {d : ℕ} (A : Module.End ℂ (Operator d))
    (hA : ∀ X : Operator d, X.IsHermitian → (A X).IsHermitian) (X : Operator d) :
    A Xᴴ = (A X)ᴴ := by
  set P : Operator d := X + Xᴴ with hPdef
  set Q : Operator d := Complex.I • (X - Xᴴ) with hQdef
  have hP : P.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hPdef, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  have hQ : Q.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hQdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have : star Complex.I = -Complex.I := by simp
    rw [this, neg_smul, ← smul_neg, neg_sub]
  have e1 : (2 : ℂ) • X = P - Complex.I • Q := by
    rw [hPdef, hQdef, smul_smul, Complex.I_mul_I]
    rw [neg_one_smul, sub_neg_eq_add, two_smul]
    abel
  have e2 : (2 : ℂ) • Xᴴ = P + Complex.I • Q := by
    rw [hPdef, hQdef, smul_smul, Complex.I_mul_I, neg_one_smul, two_smul]
    abel
  have hAP : (A P)ᴴ = A P := hA P hP
  have hAQ : (A Q)ᴴ = A Q := hA Q hQ
  have key : (2 : ℂ) • A Xᴴ = (2 : ℂ) • (A X)ᴴ := by
    rw [← map_smul, e2]
    have h2 : (2 : ℂ) • (A X)ᴴ = (A ((2 : ℂ) • X))ᴴ := by
      rw [map_smul, Matrix.conjTranspose_smul]
      congr 1
      simp
    rw [h2, e1, map_sub, map_smul, map_add, map_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, hAP, hAQ]
    have : star Complex.I = -Complex.I := by simp
    rw [this, neg_smul, sub_neg_eq_add]
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) key

theorem conj4 {d : ℕ} (L : Operator d → Operator d) (hL : IsLKAction L) :
    (superoperatorTrace L).im = 0 := by
  obtain ⟨⟨A, rfl⟩, hH, -⟩ := hL
  have hA : ∀ X : Operator d, X.IsHermitian → (A X).IsHermitian := hH
  have hc : star (superoperatorTrace (fun X => A X)) = superoperatorTrace (fun X => A X) := by
    unfold superoperatorTrace
    simp only [star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 := herm_comm A hA (Matrix.single j i 1)
    rw [Matrix.conjTranspose_single, star_one] at h1
    rw [h1, Matrix.conjTranspose_apply]
  exact Complex.conj_eq_iff_im.mp hc

theorem conj5 {d : ℕ} (L M : Operator d → Operator d) :
    dissipationStrength (L + M) = dissipationStrength L + dissipationStrength M ∧
      ∀ c : ℝ, dissipationStrength (c • L) = c * dissipationStrength L := by
  refine ⟨?_, fun c => ?_⟩
  · unfold dissipationStrength
    rw [st_padd, Complex.add_re]
    ring
  · unfold dissipationStrength
    rw [st_rsmul, Complex.re_ofReal_mul]
    ring

lemma koss_zero {d : ℕ} (F : Fin (d^2-1) → Operator d) (H : Operator d) :
    kossakowskiAction F H 0 = coherent H := by
  funext X; simp [kossakowskiAction]

lemma neg_coherent {d : ℕ} (H : Operator d) : -coherent H = coherent (-H) := by
  funext X
  simp only [Pi.neg_apply, coherent, neg_mul, mul_neg, smul_sub, smul_neg]
  abel

lemma ds_neg {d : ℕ} (L : Operator d → Operator d) :
    dissipationStrength (-L) = - dissipationStrength L := by
  unfold dissipationStrength
  rw [st_neg, Complex.neg_re]
  ring

lemma ds_koss_one {d : ℕ} (hd : 0 < d) (F : Fin (d^2-1) → Operator d)
    (hF : IsTracelessHermitianBasis F) (hG : gramMatrix F = 1)
    (H : Operator d) (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) :
    dissipationStrength (kossakowskiAction F H K) = K.trace.re := by
  unfold dissipationStrength
  rw [conj1 F hF H K, hG, Matrix.mul_one]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [neg_mul, Complex.neg_re, neg_neg, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero]
  field_simp

lemma psd_trace {n : Type} [Fintype n] [DecidableEq n] (K : Matrix n n ℂ) (hK : K.PosSemidef) :
    0 ≤ K.trace.re ∧ (K.trace.re = 0 ↔ K = 0) := by
  have h0 : 0 ≤ K.trace := hK.trace_nonneg
  have hre : 0 ≤ K.trace.re := (Complex.nonneg_iff.mp h0).1
  have him : K.trace.im = 0 := ((Complex.nonneg_iff.mp h0).2).symm
  refine ⟨hre, ?_, ?_⟩
  · intro h
    apply hK.trace_eq_zero_iff.mp
    exact Complex.ext h him
  · rintro rfl
    simp

lemma hamiltonian_of_coherent {d : ℕ} (hd : 0 < d) (H : Operator d) (hH : H.IsHermitian) :
    IsHamiltonianAction (coherent H) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have htr : star H.trace = H.trace := by
    rw [← Matrix.trace_conjTranspose, hH.eq]
  refine ⟨H - (H.trace / d) • 1, ?_, ?_, ?_⟩
  · apply hH.sub
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_div₀, htr]
    simp
  · rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp
    ring
  · funext X
    simp only [coherent, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    congr 1
    abel

theorem conj6 {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → Operator d) (hF : IsTracelessHermitianBasis F) (hG : gramMatrix F = 1)
    (H : Operator d) (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) :
    dissipationStrength (kossakowskiAction F H K) = K.trace.re ∧
      (K.PosSemidef → 0 ≤ dissipationStrength (kossakowskiAction F H K) ∧
        (dissipationStrength (kossakowskiAction F H K) = 0 ↔ K = 0)) ∧
      ∀ L : Operator d → Operator d, IsPhysicalAction F L →
        0 ≤ dissipationStrength L ∧
        (dissipationStrength L = 0 ↔ IsHamiltonianAction L) ∧
        (dissipationStrength L = 0 ↔ IsPhysicalAction F (-L)) := by
  refine ⟨ds_koss_one hd F hF hG H K, fun hK => ?_, fun L hL => ?_⟩
  · rw [ds_koss_one hd F hF hG H K]
    exact psd_trace K hK
  · obtain ⟨H', K', hH', hK', rfl⟩ := hL
    have hds := ds_koss_one hd F hF hG H' K'
    have hp := psd_trace K' hK'
    rw [hds]
    refine ⟨hp.1, ⟨fun h0 => ?_, fun hham => ?_⟩, ⟨fun h0 => ?_, fun hphys => ?_⟩⟩
    · rw [hp.2.mp h0, koss_zero]
      exact hamiltonian_of_coherent hd H' hH'
    · obtain ⟨H'', -, -, hL⟩ := hham
      rw [← hds, hL]
      unfold dissipationStrength
      rw [st_coherent]
      simp
    · rw [hp.2.mp h0, koss_zero, neg_coherent]
      exact ⟨-H', 0, hH'.neg, Matrix.PosSemidef.zero, (koss_zero F (-H')).symm⟩
    · obtain ⟨H'', K'', hH'', hK'', hneg⟩ := hphys
      have h1 : 0 ≤ dissipationStrength (-kossakowskiAction F H' K') := by
        rw [hneg, ds_koss_one hd F hF hG H'' K'']
        exact (psd_trace K'' hK'').1
      rw [ds_neg, hds] at h1
      linarith [hp.1]

end QAlgorithms.Papers.Independent.Information100.P59.DF890

open scoped Matrix ComplexOrder in open QAlgorithms.Papers.Independent.Information100.P59 in
theorem solution {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → Operator d) (hF : IsTracelessHermitianBasis F)
    (H : Operator d) (hH : H.IsHermitian)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) (hK : K.IsHermitian) :
    superoperatorTrace (kossakowskiAction F H K) = -(d : ℂ) * (K * gramMatrix F).trace ∧
    (gramMatrix F = 1 →
      superoperatorTrace (kossakowskiAction F H K) = -(d : ℂ) * K.trace) ∧
    (gramMatrix F = 2 • (1 : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) →
      superoperatorTrace (kossakowskiAction F H K) = -2 * (d : ℂ) * K.trace) ∧
    (∀ L : Operator d → Operator d, IsLKAction L → (superoperatorTrace L).im = 0) ∧
    (∀ L M : Operator d → Operator d, IsLKAction L → IsLKAction M →
      dissipationStrength (L + M) = dissipationStrength L + dissipationStrength M ∧
      ∀ c : ℝ, dissipationStrength (c • L) = c * dissipationStrength L) ∧
    (gramMatrix F = 1 →
      dissipationStrength (kossakowskiAction F H K) = K.trace.re ∧
      (K.PosSemidef → 0 ≤ dissipationStrength (kossakowskiAction F H K) ∧
        (dissipationStrength (kossakowskiAction F H K) = 0 ↔ K = 0)) ∧
      ∀ L : Operator d → Operator d, IsPhysicalAction F L →
        0 ≤ dissipationStrength L ∧
        (dissipationStrength L = 0 ↔ IsHamiltonianAction L) ∧
        (dissipationStrength L = 0 ↔ IsPhysicalAction F (-L))) := by
  refine ⟨DF890.conj1 F hF H K, fun hG => ?_, fun hG => ?_, fun L hL => DF890.conj4 L hL,
    fun L M _ _ => DF890.conj5 L M, fun hG => DF890.conj6 hd F hF hG H K⟩
  · rw [DF890.conj1 F hF H K, hG, Matrix.mul_one]
  · rw [DF890.conj1 F hF H K, hG, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, nsmul_eq_mul]
    push_cast
    ring
