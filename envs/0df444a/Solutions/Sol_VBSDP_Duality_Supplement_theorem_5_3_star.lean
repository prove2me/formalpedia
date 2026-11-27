-- Prove2me | solution 1 for VBSDP.Duality.Supplement.theorem_5_3_star
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:51.278513+00:00
-- url     : https://prove2.me/submissions/7edddff0-ed96-40ca-b8eb-5af002a5d7a1

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsDualSearchDirection
import Definitions.Def_VBSDP_Duality_Supplement_IsPlaneSearchMinimizer

open VBSDP
open VBSDP.Duality
open VBSDP.Duality.Supplement

theorem solution {m n : ℕ} (hn : 0 < n) (ν : ℝ) (hν : 1 ≤ ν)
    (c : Fin m → ℝ) (F₀ : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hF₀ : F₀.IsHermitian) (hF : ∀ i, (F i).IsHermitian)
    (hlin : LinearIndependent ℝ F)
    (x : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ)
    (hxZ : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F x Z)
    (δx : Fin m → ℝ) (δZ : Matrix (Fin n) (Fin n) ℝ)
    (hdir : IsDualSearchDirection ν c F₀ F x Z δx δZ)
    (p q : ℝ) (hpq : IsPlaneSearchMinimizer ν c F₀ F x Z δx δZ p q) :
    VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
      VBSDP.Potential.phi ν F₀ F x Z - 0.05 := by
        open Matrix in (
        classical
        have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        have Spec : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsHermitian → ∃ U : Matrix (Fin n) (Fin n) ℝ, star U * U = 1 ∧ U * star U = 1 ∧ ∃ d : Fin n → ℝ, M = U * diagonal d * star U := by
          intro M hM
          refine ⟨(hM.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ), hM.eigenvectorUnitary.2.1, hM.eigenvectorUnitary.2.2, hM.eigenvalues, ?_⟩
          have h := hM.spectral_theorem
          rw [Unitary.conjStarAlgAut_apply] at h
          simpa using h
        have scal : ∀ s u : ℝ, 0 ≤ s → s < 1 → |u| ≤ s → u - (1/2 + s/3 + s^2/(1-s)) * u^2 ≤ Real.log (1+u) := by
          intro s u hs0 hs1 hu
          have hu1 : |(-u)| < 1 := by rw [abs_neg]; linarith
          have h := Real.abs_log_sub_add_sum_range_le hu1 3
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
          have h' := (abs_le.mp h).1
          norm_num at h'
          have hau : 0 ≤ |u| := abs_nonneg u
          have h1s : 0 < 1 - s := by linarith
          have h1u : 0 < 1 - |u| := by linarith
          have hu2 : u^2 = |u|^2 := (sq_abs u).symm
          have hcube : -(s * u^2) ≤ u^3 := by
            have : |u^3| ≤ s * u^2 := by rw [abs_pow, hu2]; nlinarith [sq_nonneg |u|]
            linarith [neg_abs_le (u^3)]
          have hq : |u|^4 / (1 - |u|) ≤ s^2 * u^2 / (1 - s) := by
            rw [div_le_div_iff₀ h1u h1s]
            have h2 : |u|^2 ≤ s^2 := pow_le_pow_left₀ hau hu 2
            have h5 : |u|^2 * (1-s) ≤ s^2 * (1-|u|) := by nlinarith
            have h6 : |u|^4 = |u|^2 * u^2 := by rw [hu2]; ring
            rw [h6]; nlinarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg u)]
          have : s^2/(1-s) * u^2 = s^2*u^2/(1-s) := by ring
          nlinarith
        have conjTr : ∀ U : Matrix (Fin n) (Fin n) ℝ, star U * U = 1 → ∀ X, (U * X * star U).trace = X.trace := by
          intro U hU X; rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
        have conjDet : ∀ U : Matrix (Fin n) (Fin n) ℝ, U * star U = 1 → ∀ X, (U * X * star U).det = X.det := by
          intro U hU X; rw [det_mul, det_mul, mul_comm (det U), mul_assoc, ← det_mul, hU, det_one, mul_one]
        have E1 : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsHermitian → ∀ s : ℝ, 0 ≤ s → s < 1 → (M*M).trace ≤ s^2 →
            (1+M).PosDef ∧ M.trace - (1/2 + s/3 + s^2/(1-s)) * (M*M).trace ≤ Real.log (1+M).det := by
          intro M hM s hs0 hs1 hR
          obtain ⟨U, hU1, hU2, d, hMd⟩ := Spec M hM
          have htr : M.trace = ∑ i, d i := by rw [hMd, conjTr U hU1, trace_diagonal]
          have hMM : M * M = U * diagonal (fun i => d i ^ 2) * star U := by
            rw [hMd]
            calc U * diagonal d * star U * (U * diagonal d * star U)
                = U * diagonal d * (star U * U) * diagonal d * star U := by simp only [Matrix.mul_assoc]
              _ = U * diagonal (fun i => d i ^ 2) * star U := by
                rw [hU1, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; congr 3; ext i; ring
          have hRd : (M*M).trace = ∑ i, d i ^ 2 := by rw [hMM, conjTr U hU1, trace_diagonal]
          have h1M : 1 + M = U * diagonal (fun i => 1 + d i) * star U := by
            rw [hMd, ← diagonal_add, diagonal_one] at *
            rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU2]
          have hdet : (1+M).det = ∏ i, (1 + d i) := by rw [h1M, conjDet U hU2, det_diagonal]
          have hdi : ∀ i, |d i| ≤ s := by
            intro i
            have : d i ^ 2 ≤ s ^ 2 := le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ i)) (hRd ▸ hR)
            have := sq_le_sq.mp this
            rwa [abs_of_nonneg hs0] at this
          have hpos : ∀ i, 0 < 1 + d i := fun i => by linarith [neg_abs_le (d i), hdi i]
          constructor
          · rw [h1M]
            have hu : IsUnit (star U) := ⟨⟨star U, U, hU1, hU2⟩, rfl⟩
            have := (IsUnit.posDef_star_left_conjugate_iff (x := diagonal (fun i => 1 + d i)) hu).mpr (posDef_diagonal_iff.mpr hpos)
            rwa [star_star] at this
          · rw [hdet, Real.log_prod (fun i _ => (hpos i).ne'), htr, hRd, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_le_sum (fun i _ => scal s (d i) hs0 hs1 (hdi i))
        have E0 : ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosDef → ∃ C : Matrix (Fin n) (Fin n) ℝ, IsUnit C ∧ Y = Cᴴ * C := by
          intro Y hY
          obtain ⟨U, hU1, hU2, d, hYd⟩ := Spec Y hY.1
          have hd : ∀ i, 0 ≤ d i := by
            intro i
            have h := hY.posSemidef
            rw [hYd] at h
            have h2 : (star U * (U * diagonal d * star U) * U).PosSemidef := by
              have := h.conjTranspose_mul_mul_same U
              simpa [star_eq_conjTranspose] using this
            have h3 : star U * (U * diagonal d * star U) * U = diagonal d := by
              simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]; rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
            rw [h3] at h2
            exact (posSemidef_diagonal_iff.mp h2) i
          set C := diagonal (fun i => Real.sqrt (d i)) * star U
          have hYC : Y = Cᴴ * C := by
            have hCt : Cᴴ = U * diagonal (fun i => Real.sqrt (d i)) := by
              simp only [C, conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose]
              rfl
            rw [hCt, hYd]
            calc U * diagonal d * star U = U * (diagonal (fun i => Real.sqrt (d i)) * diagonal (fun i => Real.sqrt (d i))) * star U := by
                  rw [diagonal_mul_diagonal]; congr 3; ext i; rw [Real.mul_self_sqrt (hd i)]
              _ = _ := by simp only [C, Matrix.mul_assoc]
          refine ⟨C, ?_, hYC⟩
          rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
          intro h0
          have := hY.det_pos
          rw [hYC, det_mul, h0, mul_zero] at this
          exact lt_irrefl _ this
        have E3 : ∀ A Y : Matrix (Fin n) (Fin n) ℝ, A.PosDef → Y.PosDef → 0 < (A * Y).trace := by
          intro A Y hA hY
          obtain ⟨C, hC, hYC⟩ := E0 Y hY
          have : (C * A * Cᴴ).PosDef := by
            have hu : IsUnit Cᴴ := by rw [isUnit_iff_isUnit_det, det_conjTranspose] at *; simpa using hC
            have := (IsUnit.posDef_star_left_conjugate_iff (x := A) hu).mpr hA
            simpa [star_eq_conjTranspose] using this
          have h2 := this.trace_pos
          rwa [hYC, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
        have E2 : ∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef → Real.log P.det ≤ n * Real.log (P.trace / n) := by
          intro P hP
          obtain ⟨U, hU1, hU2, d, hPd⟩ := Spec P hP.1
          have hd : ∀ i, 0 < d i := by
            intro i
            have h2 : (star U * (U * diagonal d * star U) * U).PosDef := by
              have hu : IsUnit U := ⟨⟨U, star U, hU2, hU1⟩, rfl⟩
              rw [← hPd]; exact (IsUnit.posDef_star_left_conjugate_iff hu).mpr hP
            have h3 : star U * (U * diagonal d * star U) * U = diagonal d := by
              simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]; rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
            rw [h3] at h2
            exact (posDef_diagonal_iff.mp h2) i
          have htr : P.trace = ∑ i, d i := by rw [hPd, conjTr U hU1, trace_diagonal]
          have hdet : P.det = ∏ i, d i := by rw [hPd, conjDet U hU2, det_diagonal]
          have hnpos : (0:ℝ) < n := by exact_mod_cast hn
          have hTp : 0 < P.trace := by rw [htr]; exact Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
          set c := P.trace / n with hc
          have hcpos : 0 < c := div_pos hTp hnpos
          rw [hdet, Real.log_prod (fun i _ => (hd i).ne')]
          have hb : ∀ i, Real.log (d i) ≤ Real.log c + (d i / c - 1) := by
            intro i
            have := Real.log_le_sub_one_of_pos (div_pos (hd i) hcpos)
            rw [Real.log_div (hd i).ne' hcpos.ne'] at this; linarith
          calc ∑ i, Real.log (d i) ≤ ∑ i, (Real.log c + (d i / c - 1)) := Finset.sum_le_sum (fun i _ => hb i)
            _ = n * Real.log c + ((∑ i, d i) / c - n) := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]; simp
            _ = n * Real.log c := by
                rw [← htr]; have : P.trace / c = n := by rw [hc]; field_simp
                rw [this]; ring
        have Espec : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsHermitian → M.trace ^ 2 ≤ n * (M*M).trace ∧ 0 ≤ (M*M).trace := by
          intro M hM
          obtain ⟨U, hU1, hU2, d, hMd⟩ := Spec M hM
          have htr : M.trace = ∑ i, d i := by rw [hMd, conjTr U hU1, trace_diagonal]
          have hMM : M * M = U * diagonal (fun i => d i ^ 2) * star U := by
            rw [hMd]
            calc U * diagonal d * star U * (U * diagonal d * star U)
                = U * diagonal d * (star U * U) * diagonal d * star U := by simp only [Matrix.mul_assoc]
              _ = U * diagonal (fun i => d i ^ 2) * star U := by
                rw [hU1, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]; congr 3; ext i; ring
          have hRd : (M*M).trace = ∑ i, d i ^ 2 := by rw [hMM, conjTr U hU1, trace_diagonal]
          rw [htr, hRd]
          refine ⟨?_, Finset.sum_nonneg (fun i _ => sq_nonneg _)⟩
          have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := d)
          simpa using this
        obtain ⟨hFx, hZ, hcZ⟩ := hxZ
        obtain ⟨hδZ, hEq, hTr0⟩ := hdir
        obtain ⟨hfeas, hmin⟩ := hpq
        have hlmi : ∀ p : ℝ, VBSDP.Duality.lmi F₀ F (x + p • δx) = VBSDP.Duality.lmi F₀ F x + p • ∑ i, δx i • F i := by
          intro p
          simp only [VBSDP.Duality.lmi, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul, smul_eq_mul]
          abel
        set Fx := VBSDP.Duality.lmi F₀ F x with hFxdef
        set δF := ∑ i, δx i • F i with hδF
        set T := (Fx * Z).trace with hTdef
        have hgap : c ⬝ᵥ x + (F₀ * Z).trace = T := by
          simp only [hTdef, hFxdef, VBSDP.Duality.lmi, Matrix.add_mul, Finset.sum_mul, trace_add, trace_sum, smul_mul, trace_smul, hcZ, dotProduct, smul_eq_mul]
          rw [add_comm]; congr 1; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
        rw [hgap] at hEq
        have hTpos : 0 < T := E3 Fx Z hFx hZ
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn
        set w := Real.sqrt (n:ℝ) with hw
        have hw2 : w ^ 2 = n := Real.sq_sqrt hnpos.le
        have hw1 : 1 ≤ w := by rw [hw, Real.one_le_sqrt]; exact_mod_cast hn
        set ρ := ((n:ℝ) + ν * w) / T with hρ
        have hSpos : 0 < (n:ℝ) + ν * w := by nlinarith
        have hρpos : 0 < ρ := div_pos hSpos hTpos
        obtain ⟨B, hBu, hZB⟩ := E0 Z hZ
        have hBdet : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hBu
        set Bi := B⁻¹ with hBi
        have hBBi : B * Bi = 1 := mul_nonsing_inv B hBdet
        have hBiB : Bi * B = 1 := nonsing_inv_mul B hBdet
        have hBiH : Biᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBBi, conjTranspose_one]
        have hBHBiH : Bᴴ * Biᴴ = 1 := by rw [← conjTranspose_mul, hBiB, conjTranspose_one]
        have hZinv : Z⁻¹ = Bi * Biᴴ := by rw [hZB, Matrix.mul_inv_rev, conjTranspose_nonsing_inv]
        set M := Biᴴ * δZ * Bi with hM
        have hδZB : δZ = Bᴴ * M * B := by
          rw [hM]
          calc δZ = (Bᴴ * Biᴴ) * δZ * (Bi * B) := by rw [hBHBiH, hBiB, Matrix.one_mul, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
        have hMherm : M.IsHermitian := by
          rw [hM]; exact isHermitian_conjTranspose_mul_mul Bi hδZ
        set P := B * Fx * Bᴴ with hP
        set N := B * δF * Bᴴ with hN
        have hBunitH : IsUnit Bᴴ := by
          rw [isUnit_iff_isUnit_det, det_conjTranspose]; simpa using hBdet
        have conjB : ∀ X, (B * X * Bᴴ).PosDef ↔ X.PosDef := by
          intro X; have := IsUnit.posDef_star_left_conjugate_iff (x := X) hBunitH
          simpa [star_eq_conjTranspose] using this
        have conjB' : ∀ X, (Bᴴ * X * B).PosDef ↔ X.PosDef := by
          intro X; have := IsUnit.posDef_star_left_conjugate_iff (x := X) hBu
          simpa [star_eq_conjTranspose] using this
        have hPpd : P.PosDef := (conjB Fx).mpr hFx
        have trZ : ∀ X, (X * Z).trace = (B * X * Bᴴ).trace := by
          intro X; rw [hZB, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
        have detZ : ∀ X, (X * Z).det = (B * X * Bᴴ).det := by
          intro X; rw [hZB]; simp only [det_mul]; ring
        have hMN : M + N = 1 - ρ • P := by
          have h := congrArg (fun X => B * X * Bᴴ) hEq
          have h1 : B * (Z⁻¹ * δZ * Z⁻¹ + δF) * Bᴴ = M + N := by
            rw [Matrix.mul_add, Matrix.add_mul, hZinv]
            congr 1
            calc B * (Bi * Biᴴ * δZ * (Bi * Biᴴ)) * Bᴴ = (B * Bi) * (Biᴴ * δZ * Bi) * (Biᴴ * Bᴴ) := by simp only [Matrix.mul_assoc]
              _ = M := by rw [hBBi, hBiH, Matrix.one_mul, Matrix.mul_one]
          have h2 : B * (-ρ • Fx + Z⁻¹) * Bᴴ = 1 - ρ • P := by
            rw [Matrix.mul_add, Matrix.add_mul, hZinv]
            have e1 : B * (-ρ • Fx) * Bᴴ = -ρ • P := by simp only [Matrix.mul_smul, Matrix.smul_mul, hP]
            have e2 : B * (Bi * Biᴴ) * Bᴴ = 1 := by
              calc B * (Bi * Biᴴ) * Bᴴ = (B * Bi) * (Biᴴ * Bᴴ) := by simp only [Matrix.mul_assoc]
                _ = 1 := by rw [hBBi, hBiH, Matrix.one_mul]
            rw [e1, e2, neg_smul]; abel
          rw [← h1, ← h2]; exact h
        have hFδZ : (δF * δZ).trace = 0 := by
          simp only [hδF, Finset.sum_mul, trace_sum, smul_mul, trace_smul, hTr0, smul_zero, Finset.sum_const_zero]
        have hNM : (N * M).trace = 0 := by
          have : N * M = B * (δF * δZ) * Bi := by
            calc N * M = B * δF * (Bᴴ * Biᴴ) * δZ * Bi := by simp only [hN, hM, Matrix.mul_assoc]
              _ = _ := by rw [hBHBiH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          rw [this, trace_mul_comm, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, hFδZ]
        have hρP : ρ • P = 1 - M - N := by
          have h := hMN; rw [eq_sub_iff_add_eq] at h; rw [← h]; abel
        have hPM : ρ * (P*M).trace = M.trace - (M*M).trace := by
          have : ((ρ • P) * M).trace = ρ * (P*M).trace := by rw [smul_mul, trace_smul, smul_eq_mul]
          rw [← this, hρP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, trace_sub, trace_sub, hNM, sub_zero]
        have hT : T = P.trace := trZ Fx
        have hD : (Fx * Z).det = P.det := detZ Fx
        have hDpos : 0 < P.det := hPpd.det_pos
        have hlogD := E2 P hPpd
        obtain ⟨htR, hR0⟩ := Espec M hMherm
        have hphi : ∀ x' Z', VBSDP.Potential.phi ν F₀ F x' Z' = ν * w * Real.log (VBSDP.Duality.lmi F₀ F x' * Z').trace + (-Real.log (VBSDP.Duality.lmi F₀ F x' * Z').det + n * Real.log (VBSDP.Duality.lmi F₀ F x' * Z').trace - n * Real.log n) := by
          intro x' Z'; rfl
        have hlog2 := Real.log_two_gt_d9
        by_cases hcase : (M*M).trace ≤ 0.42^2
        · set p₁ := 1 / ρ with hp₁
          have hppos : 0 < p₁ := by positivity
          have hpρ : p₁ * ρ = 1 := by rw [hp₁]; field_simp
          have hNeg := E1 (-M) hMherm.neg 0.42 (by norm_num) (by norm_num) (by rw [neg_mul_neg]; exact hcase)
          rw [neg_mul_neg, trace_neg] at hNeg
          obtain ⟨h1M, hlog1M⟩ := hNeg
          have hF' : B * (Fx + p₁ • δF) * Bᴴ = p₁ • (1 + -M) := by
            have e : B * (Fx + p₁ • δF) * Bᴴ = P + p₁ • N := by
              simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hP, hN]
            have hN' : N = 1 - M - ρ • P := by
              have h := hMN; rw [eq_sub_iff_add_eq] at h; rw [← h]; abel
            rw [e, hN', smul_sub, smul_sub, smul_smul, hpρ, one_smul, smul_add, smul_neg]; abel
          have hF'pd : (Fx + p₁ • δF).PosDef := (conjB _).mp (by rw [hF']; exact h1M.smul hppos)
          have hfeas1 : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + p₁ • δx) (Z + (0:ℝ) • δZ) := by
            refine ⟨by rw [hlmi]; exact hF'pd, by simpa using hZ, by simpa using hcZ⟩
          refine le_trans (hmin p₁ 0 hfeas1) ?_
          rw [hphi, hphi, hlmi p₁, zero_smul, add_zero, ← hFxdef]
          have hT' : ((Fx + p₁ • δF) * Z).trace = p₁ * (n - M.trace) := by
            rw [trZ, hF', trace_smul, trace_add, trace_one, trace_neg, Fintype.card_fin, smul_eq_mul]; ring
          have hD' : ((Fx + p₁ • δF) * Z).det = p₁ ^ n * (1 + -M).det := by
            rw [detZ, hF', det_smul, Fintype.card_fin]
          have hT'pos : 0 < ((Fx + p₁ • δF) * Z).trace := E3 _ Z hF'pd hZ
          have hnt : 0 < (n:ℝ) - M.trace := by
            rw [hT'] at hT'pos; exact pos_of_mul_pos_right hT'pos hppos.le
          have hd1 : 0 < (1 + -M).det := h1M.det_pos
          have hTp : T = p₁ * (n + ν * w) := by rw [hp₁, hρ]; field_simp
          rw [hT', hD', ← hTdef, hD, Real.log_mul hppos.ne' hnt.ne', Real.log_mul (pow_ne_zero _ hppos.ne') hd1.ne', Real.log_pow]
          rw [← hT, hTp, Real.log_div (by positivity) hnpos.ne', Real.log_mul hppos.ne' hSpos.ne'] at hlogD
          rw [hTp, Real.log_mul hppos.ne' hSpos.ne']
          have hA : Real.log ((n:ℝ) - M.trace) - Real.log n ≤ -(M.trace / n) := by
            rw [← Real.log_div hnt.ne' hnpos.ne']
            have := Real.log_le_sub_one_of_pos (div_pos hnt hnpos)
            have e : ((n:ℝ) - M.trace) / n - 1 = -(M.trace / n) := by field_simp; ring
            linarith
          have hνw : 0 ≤ ν * w + n := by positivity
          have hAm := mul_le_mul_of_nonneg_left hA hνw
          have hX : (ν * w + n) * (-(M.trace / n)) = -(ν * (M.trace / w)) - M.trace := by
            rw [← hw2]; field_simp; ring
          have hwpos : 0 < w := by linarith
          have hC0 : -0.42 ≤ M.trace / w := by
            rw [le_div_iff₀ hwpos]
            have : M.trace ^ 2 ≤ (0.42 * w) ^ 2 := by
              have := le_trans htR (mul_le_mul_of_nonneg_left hcase hnpos.le)
              rw [mul_pow, hw2]; linarith
            have h5 := sq_le_sq.mp this
            rw [abs_of_pos (by positivity : (0:ℝ) < 0.42 * w)] at h5
            linarith [neg_abs_le M.trace]
          have hC := mul_le_mul_of_nonneg_left hC0 (by linarith : (0:ℝ) ≤ ν)
          have hB : ν * Real.log 2 ≤ ν * w * (Real.log ((n:ℝ) + ν * w) - Real.log n) := by
            rw [← Real.log_div hSpos.ne' hnpos.ne']
            have e : ((n:ℝ) + ν * w) / n = 1 + ν / w := by rw [← hw2]; field_simp
            rw [e, mul_assoc]
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            have hs1 : -1 ≤ 1 / w := by
              have : 0 < 1/w := by positivity
              linarith
            have hb := one_add_mul_self_le_rpow_one_add hs1 hw1
            have e2 : 1 + w * (1 / w) = 2 := by field_simp; ring
            rw [e2] at hb
            have h3 := Real.log_le_log (by norm_num) hb
            rw [Real.log_rpow (by positivity)] at h3
            have h4 : Real.log (1 + 1 / w) ≤ Real.log (1 + ν / w) :=
              Real.log_le_log (by positivity) (by gcongr)
            exact le_trans h3 (mul_le_mul_of_nonneg_left h4 (by linarith))
          have hk : (1 / 2 + 0.42 / 3 + 0.42 ^ 2 / (1 - 0.42)) * (M * M).trace ≤ (1 / 2 + 0.42 / 3 + 0.42 ^ 2 / (1 - 0.42)) * 0.42^2 :=
            mul_le_mul_of_nonneg_left hcase (by norm_num)
          have hν' : 0 ≤ (ν - 1) * (Real.log 2 - 0.42) := mul_nonneg (by linarith) (by linarith)
          linarith only [hAm, hX, hC, hB, hk, hlogD, hlog1M, hlog2, hν']
        · push Not at hcase
          set R := (M*M).trace with hRdef
          set r := Real.sqrt R with hr
          have hr2 : r^2 = R := Real.sq_sqrt hR0
          have hr0 : 0.42 < r := by
            have : Real.sqrt (0.42^2) < r := Real.sqrt_lt_sqrt (by norm_num) hcase
            rwa [Real.sqrt_sq (by norm_num)] at this
          set q₁ := (1/4) / r with hq₁
          have hrpos : 0 < r := by linarith
          have hqpos : 0 < q₁ := by positivity
          have hqR : q₁ * q₁ * R = 1/16 := by rw [hq₁, ← hr2]; field_simp; ring
          have hqR' : q₁ * R = r / 4 := by rw [hq₁, ← hr2]; field_simp
          have hqMherm : (q₁ • M).IsHermitian := by
            unfold Matrix.IsHermitian; rw [conjTranspose_smul, hMherm.eq]; simp
          have hqq : (q₁ • M) * (q₁ • M) = (q₁ * q₁) • (M * M) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          have hE := E1 (q₁ • M) hqMherm (1/4) (by norm_num) (by norm_num) (by rw [hqq, trace_smul, smul_eq_mul, hqR]; norm_num)
          rw [hqq, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul, hqR] at hE
          obtain ⟨h1q, hlogq⟩ := hE
          have hZ' : Z + q₁ • δZ = Bᴴ * (1 + q₁ • M) * B := by
            rw [hδZB, hZB]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
          have hZ'pd : (Z + q₁ • δZ).PosDef := by rw [hZ']; exact (conjB' _).mpr h1q
          have hfeas2 : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + (0:ℝ) • δx) (Z + q₁ • δZ) := by
            refine ⟨by simpa using hFx, hZ'pd, fun i => ?_⟩
            rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, hcZ, hTr0, smul_zero, add_zero]
          refine le_trans (hmin 0 q₁ hfeas2) ?_
          rw [hphi, hphi, zero_smul, add_zero, ← hFxdef]
          have hFδZ' : (Fx * δZ).trace = (P * M).trace := by
            rw [hδZB, hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]; simp only [Matrix.mul_assoc]
          have hT' : (Fx * (Z + q₁ • δZ)).trace = T + q₁ * (P*M).trace := by
            rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, hFδZ', smul_eq_mul]
          have hD' : (Fx * (Z + q₁ • δZ)).det = P.det * (1 + q₁ • M).det := by
            rw [hZ', ← hD, hZB]; simp only [det_mul]; ring
          have hT'pos := E3 Fx _ hFx hZ'pd
          have hdq := h1q.det_pos
          rw [hD', ← hTdef, hD, Real.log_mul hDpos.ne' hdq.ne']
          rw [hT'] at hT'pos ⊢
          have hL : Real.log (T + q₁ * (P*M).trace) - Real.log T ≤ q₁ * (P*M).trace / T := by
            rw [← Real.log_div hT'pos.ne' hTpos.ne']
            have := Real.log_le_sub_one_of_pos (div_pos hT'pos hTpos)
            have e : (T + q₁ * (P*M).trace) / T - 1 = q₁ * (P*M).trace / T := by field_simp; ring
            linarith
          have hνw : 0 ≤ ν * w + n := by positivity
          have hLm := mul_le_mul_of_nonneg_left hL hνw
          have hY : (ν * w + n) * (q₁ * (P*M).trace / T) = q₁ * (M.trace - R) := by
            rw [← hPM, hρ]; field_simp; ring
          linarith only [hLm, hY, hlogq, hqR', hr0])
