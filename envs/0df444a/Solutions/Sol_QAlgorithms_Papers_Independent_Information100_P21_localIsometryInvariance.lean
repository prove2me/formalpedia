-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P21.localIsometryInvariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:37:21.776108+00:00
-- url     : https://prove2.me/submissions/fa44a81f-9e7b-492e-8e91-688f90f3d664

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X6LocalIso

open QAlgorithms QAlgorithms.Entanglement QAlgorithms.Papers.Independent.Information100.P21

lemma conj_density {I K : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Nonempty K]
    (M : Matrix K I ℂ) (A : Matrix I I ℂ) (hA : IsDensityMatrix A) :
    ∃ t : ℝ, 0 ≤ t ∧ ∃ D : Matrix K K ℂ, IsDensityMatrix D ∧ M * A * Mᴴ = (t : ℂ) • D := by
  have hP : (M * A * Mᴴ).PosSemidef := hA.1.mul_mul_conjTranspose_same M
  have htr := hP.trace_nonneg
  rw [Complex.nonneg_iff] at htr
  set t := (M * A * Mᴴ).trace.re
  have ht : (M * A * Mᴴ).trace = (t : ℂ) := Complex.ext rfl (by simp [htr.2])
  refine ⟨t, htr.1, ?_⟩
  by_cases h0 : t = 0
  · have hz : M * A * Mᴴ = 0 := by
      rw [← hP.trace_eq_zero_iff, ht, h0]; simp
    refine ⟨((Fintype.card K : ℂ))⁻¹ • 1, ⟨?_, ?_⟩, ?_⟩
    · apply Matrix.PosSemidef.one.smul
      rw [inv_nonneg]; exact_mod_cast Nat.zero_le _
    · rw [Matrix.trace_smul, Matrix.trace_one]
      have : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [this]
    · rw [hz, h0]; simp
  · refine ⟨((t : ℂ))⁻¹ • (M * A * Mᴴ), ⟨?_, ?_⟩, ?_⟩
    · apply hP.smul
      rw [← Complex.ofReal_inv]; exact_mod_cast inv_nonneg.mpr htr.1
    · rw [Matrix.trace_smul, ht]; simp [h0]
    · rw [smul_smul]; simp [h0]

lemma sep_conj {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty K] [Nonempty L] (M : Matrix K I ℂ) (N : Matrix L J ℂ)
    (X : Matrix (I × J) (I × J) ℂ) (hX : IsSeparablePositive X) :
    IsSeparablePositive (Matrix.kronecker M N * X * (Matrix.kronecker M N)ᴴ) := by
  obtain ⟨q, w, A, B, hw, hd, rfl⟩ := hX
  unfold Matrix.kronecker
  choose tA htA DA hDA hEA using fun j => conj_density M (A j) (hd j).1
  choose tB htB DB hDB hEB using fun j => conj_density N (B j) (hd j).2
  refine ⟨q, fun j => w j * tA j * tB j, DA, DB, fun j => ?_, fun j => ⟨hDA j, hDB j⟩, ?_⟩
  · exact mul_nonneg (mul_nonneg (hw j) (htA j)) (htB j)
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hEA, hEB,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, smul_smul]
  push_cast; ring_nf; try rfl

lemma sep_add {I J : Type*} [Fintype I] [Fintype J] (X Y : Matrix (I × J) (I × J) ℂ)
    (hX : IsSeparablePositive X) (hY : IsSeparablePositive Y) :
    IsSeparablePositive (X + Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hd1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hd2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append w1 w2, Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hw1, hw2]
  · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hd1, hd2]
  · rw [Fin.sum_univ_add]; simp

lemma sep_smul {I J : Type*} [Fintype I] [Fintype J] (X : Matrix (I × J) (I × J) ℂ)
    (c : ℝ) (hc : 0 ≤ c) (hX : IsSeparablePositive X) :
    IsSeparablePositive ((c : ℂ) • X) := by
  obtain ⟨q, w, A, B, hw, hd, rfl⟩ := hX
  refine ⟨q, fun j => c * w j, A, B, fun j => mul_nonneg hc (hw j), hd, ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]; push_cast; rfl

lemma maxMixed (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    IsDensityMatrix (((Fintype.card I : ℂ))⁻¹ • (1 : Matrix I I ℂ)) := by
  refine ⟨?_, ?_⟩
  · apply Matrix.PosSemidef.one.smul
    rw [inv_nonneg]; exact_mod_cast Nat.zero_le _
  · rw [Matrix.trace_smul, Matrix.trace_one]
    have : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [this]

lemma trace_conj {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] (V : Matrix K I ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix I I ℂ) : (V * X * Vᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

lemma trace_mix {I : Type*} [Fintype I] (rho omega : Matrix I I ℂ) (s : ℝ) (hs : 0 ≤ s)
    (h1 : rho.trace = 1) (h2 : omega.trace = 1) : (mix rho omega s).trace = 1 := by
  unfold mix
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, h1, h2]
  have : (1 + s : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + s) ≠ 0)
  push_cast; simp only [smul_eq_mul, mul_one]; exact inv_mul_cancel₀ this

theorem robust_eq {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    (VA : Matrix K I ℂ) (VB : Matrix L J ℂ) (hA : VAᴴ * VA = 1) (hB : VBᴴ * VB = 1)
    (rho : Op (I × J)) (h : IsDensityMatrix rho) (std : Bool) :
    robust {X | sep X} std (Matrix.kronecker VA VB * rho * (Matrix.kronecker VA VB)ᴴ) =
      robust {X | sep X} std rho := by
  set V := Matrix.kronecker VA VB with hVdef
  have hV : Vᴴ * V = 1 := by
    rw [hVdef]; unfold Matrix.kronecker
    rw [ Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB,
      Matrix.one_kronecker_one]
  have hVh : Vᴴ = Matrix.kronecker VAᴴ VBᴴ := Matrix.conjTranspose_kronecker VA VB
  -- separable states are preserved by conjugation with V
  have sepV : ∀ X : Op (I × J), sep X → sep (V * X * Vᴴ) := fun X hX =>
    ⟨sep_conj VA VB X hX.1, by rw [trace_conj V hV]; exact hX.2⟩
  unfold robust
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs, omega', hd', hstd', hmix'⟩
    set om0 := Vᴴ * omega' * V with hom0
    have hom0' : om0 = Matrix.kronecker VAᴴ VBᴴ * omega' * (Matrix.kronecker VAᴴ VBᴴ)ᴴ := by
      rw [hom0, ← hVh, Matrix.conjTranspose_conjTranspose]
    have hP0 : om0.PosSemidef := by
      have := hd'.1.conjTranspose_mul_mul_same V; simpa [hom0] using this
    -- trace bound
    have htr0 := hP0.trace_nonneg
    have hle : om0.trace ≤ 1 := by
      set P := V * Vᴴ
      have hPP : (1 - P) * (1 - P)ᴴ = 1 - P := by
        have hPh : Pᴴ = P := by simp [P, Matrix.conjTranspose_mul]
        have hP2 : P * P = P := by
          simp only [P]; rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPh, Matrix.sub_mul,
          Matrix.mul_sub, Matrix.mul_sub, hP2]; simp
      have hpos := (hd'.1.conjTranspose_mul_mul_same (1 - P)).trace_nonneg
      have e1 : ((1 - P)ᴴ * omega' * (1 - P)).trace = 1 - om0.trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hPP, Matrix.sub_mul, Matrix.one_mul,
          Matrix.trace_sub, hd'.2, hom0, Matrix.trace_mul_comm (Vᴴ * omega') V,
          ← Matrix.mul_assoc]
      rw [e1] at hpos
      exact sub_nonneg.mp hpos
    rw [Complex.nonneg_iff] at htr0
    set t := om0.trace.re
    have ht : om0.trace = (t : ℂ) := Complex.ext rfl (by simp [htr0.2])
    rw [ht] at hle
    have ht1 : t ≤ 1 := by exact_mod_cast hle
    set sig : Op (I × J) := Matrix.kroneckerMap (· * ·) (((Fintype.card I : ℂ))⁻¹ • (1 : Matrix I I ℂ))
      (((Fintype.card J : ℂ))⁻¹ • (1 : Matrix J J ℂ))
    have hsig : IsSeparablePositive sig := by
      refine ⟨1, fun _ => 1, fun _ => _, fun _ => _, fun _ => zero_le_one,
        fun _ => ⟨maxMixed I, maxMixed J⟩, ?_⟩
      simp [sig]
    have hsigd : IsDensityMatrix sig := by
      refine ⟨(maxMixed I).1.kronecker (maxMixed J).1, ?_⟩
      rw [Matrix.trace_kronecker, (maxMixed I).2, (maxMixed J).2, mul_one]
    refine ⟨hs, om0 + ((1 - t : ℝ) : ℂ) • sig, ⟨?_, ?_⟩, ?_, ?_⟩
    · apply hP0.add
      apply hsigd.1.smul
      exact_mod_cast sub_nonneg.mpr ht1
    · rw [Matrix.trace_add, Matrix.trace_smul, hsigd.2, ht]; push_cast; simp
    · intro hstd
      refine ⟨sep_add _ _ ?_ (sep_smul _ _ (sub_nonneg.mpr ht1) hsig), ?_⟩
      · rw [hom0']; exact sep_conj _ _ _ (hstd' hstd).1
      · rw [Matrix.trace_add, Matrix.trace_smul, hsigd.2, ht]; push_cast; simp
    · have heq : mix rho (om0 + ((1 - t : ℝ) : ℂ) • sig) s =
          Vᴴ * mix (V * rho * Vᴴ) omega' s * V +
            (((1 + s)⁻¹ * s * (1 - t) : ℝ) : ℂ) • sig := by
        have hr : Vᴴ * (V * rho * Vᴴ) * V = rho := by
          simp only [← Matrix.mul_assoc, hV, Matrix.one_mul]
          rw [Matrix.mul_assoc, hV, Matrix.mul_one]
        unfold mix
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hr,
          Matrix.mul_smul, Matrix.smul_mul, ← hom0]
        push_cast
        simp only [smul_add, smul_smul]
        abel_nf
        congr 1
        · ring_nf
      refine ⟨?_, trace_mix _ _ _ hs h.2 ?_⟩
      · rw [heq]
        refine sep_add _ _ ?_ (sep_smul _ _ ?_ hsig)
        · have := sep_conj VAᴴ VBᴴ _ hmix'.1
          rwa [← hVh, Matrix.conjTranspose_conjTranspose] at this
        · have : 0 ≤ (1 + s)⁻¹ := inv_nonneg.mpr (by linarith)
          exact mul_nonneg (mul_nonneg this hs) (sub_nonneg.mpr ht1)
      · rw [Matrix.trace_add, Matrix.trace_smul, hsigd.2, ht]; push_cast; simp
  · rintro ⟨hs, omega, hd, hstd, hmix⟩
    refine ⟨hs, V * omega * Vᴴ, ⟨hd.1.mul_mul_conjTranspose_same V, by
      rw [trace_conj V hV]; exact hd.2⟩, fun hh => sepV _ (hstd hh), ?_⟩
    have : mix (V * rho * Vᴴ) (V * omega * Vᴴ) s = V * mix rho omega s * Vᴴ := by
      unfold mix
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    rw [this]
    exact sepV _ hmix

end X6LocalIso

open QAlgorithms.Papers.Independent.Information100.P21 in
theorem solution {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
  (VA : Matrix K I ℂ) (VB : Matrix L J ℂ) (hA : VAᴴ*VA=1) (hB : VBᴴ*VB=1)
  (rho : Op (I × J)) (h : QAlgorithms.IsDensityMatrix rho) :
  let V := Matrix.kronecker VA VB
  rs (V*rho*Vᴴ)=rs rho ∧ rg (V*rho*Vᴴ)=rg rho := by
  intro V
  exact ⟨X6LocalIso.robust_eq VA VB hA hB rho h true,
    X6LocalIso.robust_eq VA VB hA hB rho h false⟩
