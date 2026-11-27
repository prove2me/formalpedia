-- Prove2me | solution 1 for VBSDP.Duality.Supplement.theorem_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:34.655837+00:00
-- url     : https://prove2.me/submissions/3c4544c5-d50e-4982-879d-72382f190b94

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsSymmetricSearchDirection
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
    (hdir : IsSymmetricSearchDirection ν c F₀ F x Z δx δZ)
    (p q : ℝ) (hpq : IsPlaneSearchMinimizer ν c F₀ F x Z δx δZ p q) :
    VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
      VBSDP.Potential.phi ν F₀ F x Z - 0.24 := by
        classical
        letI := Matrix.instPartialOrder (n := Fin n) (𝕜 := ℝ)
        letI := Matrix.instStarOrderedRing (n := Fin n) (𝕜 := ℝ)
        letI := Matrix.instNonnegSpectrumClass (n := Fin n) (𝕜 := ℝ)
        let A := VBSDP.Duality.lmi F₀ F x
        let H : Matrix (Fin n) (Fin n) ℝ := ∑ i, δx i • F i
        have hA : A.PosDef := hxZ.1
        have hZ : Z.PosDef := hxZ.2.1
        have hdual : ∀ i, (F i * Z).trace = c i := hxZ.2.2
        have hH : H.IsHermitian := by
          change H.conjTranspose = H
          simp only [H, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_trivial,
            fun i => (hF i).eq]
        have hlmi (t : ℝ) : VBSDP.Duality.lmi F₀ F (x + t • δx) = A + t • H := by
          simp only [VBSDP.Duality.lmi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum, A, H]
          abel
        have horth : (H * δZ).trace = 0 := by
          simp only [H, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
            hdir.2.2, smul_zero, Finset.sum_const_zero]
        have hgap : (A * Z).trace = c ⬝ᵥ x + (F₀ * Z).trace := by
          simp only [A, VBSDP.Duality.lmi, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul,
            Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, hdual, dotProduct, smul_eq_mul]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hfeas (s t : ℝ) (ha : (A + s • H).PosDef) (hz : (Z + t • δZ).PosDef) :
            VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + s • δx) (Z + t • δZ) := by
          refine ⟨hlmi s ▸ ha, hz, ?_⟩
          intro i
          simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
            hdual, hdir.2.2, smul_zero, add_zero]
        have hbase : VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
            VBSDP.Potential.phi ν F₀ F x Z := by
          simpa using hpq.2 0 0 (by simpa using hxZ)
        obtain ⟨W, hW, hWZW, heq⟩ := hdir.2.1
        let ρ := ((n : ℝ) + ν * Real.sqrt n) / (A * Z).trace
        have heq' : W * δZ * W + H = -ρ • A + Z⁻¹ := by
          simpa only [ρ, hgap, H, A] using heq
        have hlogquad (u : ℝ) (hu : |u| ≤ (9 / 20 : ℝ)) :
            u - (147 / 200 : ℝ) * u ^ 2 ≤ Real.log (1 + u) := by
          have hpow (k : ℕ) (hk : 2 ≤ k) :
              (-u) ^ k ≤ (9 / 20 : ℝ) ^ (k - 2) * u ^ 2 := by
            calc
              (-u) ^ k ≤ |u| ^ k := by
                simpa only [abs_pow, abs_neg] using le_abs_self ((-u) ^ k)
              _ = |u| ^ (k - 2) * u ^ 2 := by
                rw [← sq_abs, ← pow_add, Nat.sub_add_cancel hk]
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (abs_nonneg u) hu _) (sq_nonneg u)
          have hp10 : |u| ^ 10 ≤ (9 / 20 : ℝ) ^ 8 * u ^ 2 := by
            calc
              _ = |u| ^ 8 * u ^ 2 := by rw [← sq_abs, ← pow_add]
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (abs_nonneg u) hu _) (sq_nonneg u)
          have hrem : |u| ^ 10 / (1 - |u|) ≤
              ((9 / 20 : ℝ) ^ 8 / (11 / 20)) * u ^ 2 := by
            calc
              _ ≤ |u| ^ 10 / (11 / 20) :=
                div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith only [hu])
              _ ≤ _ := by
                apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 11 / 20)).mpr
                nlinarith only [hp10]
          have ht := (abs_le.mp (Real.abs_log_sub_add_sum_range_le
            (x := -u) (by rw [abs_neg]; linarith only [hu]) 9)).1
          simp only [abs_neg, sub_neg_eq_add] at ht
          norm_num [Finset.sum_range_succ] at ht
          have h2 := hpow 2 (by omega)
          have h3 := hpow 3 (by omega)
          have h4 := hpow 4 (by omega)
          have h5 := hpow 5 (by omega)
          have h6 := hpow 6 (by omega)
          have h7 := hpow 7 (by omega)
          have h8 := hpow 8 (by omega)
          have h9 := hpow 9 (by omega)
          norm_num at h2 h3 h4 h5 h6 h7 h8 h9 hrem
          linear_combination ht + (1 / 2 : ℝ) * h2 + (1 / 3 : ℝ) * h3 +
            (1 / 4 : ℝ) * h4 + (1 / 5 : ℝ) * h5 + (1 / 6 : ℝ) * h6 +
            (1 / 7 : ℝ) * h7 + (1 / 8 : ℝ) * h8 + (1 / 9 : ℝ) * h9 + hrem +
            (427564007 / 197120000000 : ℝ) * (sq_nonneg u)
        have hspecsq (k : ℕ) (B : Matrix (Fin k) (Fin k) ℝ) (hB : B.IsHermitian) :
            (B * B).trace = ∑ i, (hB.eigenvalues i) ^ 2 := by
          let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) hB.eigenvectorUnitary
          have hsp : B = f (Matrix.diagonal hB.eigenvalues) := by
            simpa only [f, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hB.spectral_theorem
          have hftr (M : Matrix (Fin k) (Fin k) ℝ) : (f M).trace = M.trace := by
            simp only [f, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
              Unitary.coe_star_mul_self, Matrix.one_mul]
          calc
            _ = (f (Matrix.diagonal hB.eigenvalues) * f (Matrix.diagonal hB.eigenvalues)).trace := by rw [← hsp]
            _ = (f (Matrix.diagonal hB.eigenvalues * Matrix.diagonal hB.eigenvalues)).trace := by rw [map_mul]
            _ = _ := by rw [hftr, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]; simp only [sq]
        have hfrobsq (k : ℕ) (B : Matrix (Fin k) (Fin k) ℝ) (hB : B.IsHermitian) :
            (B * B).trace = ∑ i, ∑ j, (B i j) ^ 2 := by
          have hsym (i j : Fin k) : B j i = B i j := by
            simpa using congrFun (congrFun hB.eq i) j
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hsym]
          ring
        have hbarrier (k : ℕ) (B : Matrix (Fin k) (Fin k) ℝ) (hB : B.IsHermitian)
            (hb : (B * B).trace ≤ (9 / 20 : ℝ) ^ 2) :
            (1 + B).PosDef ∧
              B.trace - (147 / 200 : ℝ) * (B * B).trace ≤ Real.log (1 + B).det := by
          let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin k) (Fin k) ℝ) hB.eigenvectorUnitary
          have hsp : B = f (Matrix.diagonal hB.eigenvalues) := by
            simpa only [f, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using hB.spectral_theorem
          have habs (i : Fin k) : |hB.eigenvalues i| ≤ (9 / 20 : ℝ) := by
            have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) =>
              sq_nonneg (hB.eigenvalues j)) (Finset.mem_univ i)
            rw [← hspecsq k B hB] at hs
            nlinarith only [hs, hb, sq_abs (hB.eigenvalues i), abs_nonneg (hB.eigenvalues i)]
          have hp (i : Fin k) : 0 < 1 + hB.eigenvalues i := by
            have hh := (abs_le.mp (habs i)).1
            linarith only [hh]
          have hrep : 1 + B = f (Matrix.diagonal (fun i => 1 + hB.eigenvalues i)) := by
            have hd : Matrix.diagonal (fun i => 1 + hB.eigenvalues i) =
                (1 : Matrix (Fin k) (Fin k) ℝ) + Matrix.diagonal hB.eigenvalues := by
              rw [← Matrix.diagonal_one, ← Matrix.diagonal_add]
            rw [hd, map_add, map_one, ← hsp]
          have hfdet (M : Matrix (Fin k) (Fin k) ℝ) : (f M).det = M.det := by
            change (Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary M).det = M.det
            rw [Unitary.conjStarAlgAut_apply]
            calc
              _ = ((hB.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
                star (hB.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)).det * M.det := by
                  simp only [Matrix.det_mul]
                  ring
              _ = _ := by rw [← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one, one_mul]
          constructor
          · rw [hrep]
            change ((hB.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) *
              Matrix.diagonal (fun i => 1 + hB.eigenvalues i) *
              star (hB.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)).PosDef
            exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr (Matrix.PosDef.diagonal hp)
          · rw [hrep, hfdet, Matrix.det_diagonal, Real.log_prod (fun i _ => (hp i).ne')]
            have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
              hlogquad (hB.eigenvalues i) (habs i))
            rw [hB.trace_eq_sum_eigenvalues, hspecsq k B hB]
            simpa [Finset.sum_sub_distrib, ← Finset.mul_sum] using hs
        have hsqrt : ∃ R : (Matrix (Fin n) (Fin n) ℝ)ˣ,
            star (R : Matrix (Fin n) (Fin n) ℝ) = R ∧
            (R : Matrix (Fin n) (Fin n) ℝ) * R = W := by
          obtain ⟨R, hR⟩ := (CFC.isUnit_sqrt_iff W hW.posSemidef.nonneg).mpr hW.isUnit
          refine ⟨R, ?_, ?_⟩
          · rw [hR]
            exact (CFC.sqrt_nonneg W).isSelfAdjoint.star_eq
          · rw [hR]
            exact CFC.sqrt_mul_sqrt_self W hW.posSemidef.nonneg
        obtain ⟨R, hRstar, hR2⟩ := hsqrt
        let r : Matrix (Fin n) (Fin n) ℝ := R
        let ri : Matrix (Fin n) (Fin n) ℝ := ↑(R⁻¹)
        change star r = r at hRstar
        change r * r = W at hR2
        have hri : ri = r⁻¹ := Matrix.coe_units_inv R
        have hrr : r * ri = 1 := R.mul_inv
        have hir : ri * r = 1 := R.inv_mul
        have hRIstar : star ri = ri := by
          rw [hri, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
            ← Matrix.star_eq_conjTranspose, hRstar]
        have hRR (M : Matrix (Fin n) (Fin n) ℝ) : r * (ri * M) = M := by
          rw [← Matrix.mul_assoc, hrr, Matrix.one_mul]
        have hIR (M : Matrix (Fin n) (Fin n) ℝ) : ri * (r * M) = M := by
          rw [← Matrix.mul_assoc, hir, Matrix.one_mul]
        let X : Matrix (Fin n) (Fin n) ℝ := r * Z * r
        let D : Matrix (Fin n) (Fin n) ℝ := ri * H * ri
        let E : Matrix (Fin n) (Fin n) ℝ := r * δZ * r
        have hX : X.PosDef := by
          have ht := (Matrix.IsUnit.posDef_star_left_conjugate_iff R.isUnit).mpr hZ
          change (star r * Z * r).PosDef at ht
          simpa only [hRstar] using ht
        have hD : D.IsHermitian := by
          simpa only [← Matrix.star_eq_conjTranspose, hRIstar] using
            Matrix.isHermitian_mul_mul_conjTranspose ri hH
        have hE : E.IsHermitian := by
          simpa only [← Matrix.star_eq_conjTranspose, hRstar] using
            Matrix.isHermitian_mul_mul_conjTranspose r hdir.1
        have hXA : r * X * r = A := by
          calc
            _ = (r * r) * Z * (r * r) := by dsimp [X]; noncomm_ring
            _ = A := by rw [hR2]; exact hWZW
        have hXinv : X⁻¹ = ri * Z⁻¹ * ri := by
          simp only [X, Matrix.mul_inv_rev, ← hri, Matrix.mul_assoc]
        have hDE : D + E = X⁻¹ - ρ • X := by
          have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => ri * M * ri) heq'
          rw [← hXA, ← hR2] at hh
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc, hIR, hrr, hir, Matrix.mul_one] at hh
          rw [hXinv]
          simpa only [D, E, X, sub_eq_add_neg, neg_smul, add_comm, Matrix.mul_assoc] using hh
        have hDEorth : (D * E).trace = 0 := by
          have he : D * E = ri * (H * δZ) * r := by
            simp only [D, E, Matrix.mul_assoc, hIR]
          rw [he, Matrix.trace_mul_cycle, hrr, Matrix.one_mul, horth]
        have hXS : (X * X).trace = (A * Z).trace := by
          calc
            _ = ((r * Z) * r * X).trace := rfl
            _ = (r * X * (r * Z)).trace := (Matrix.trace_mul_cycle r X (r * Z)).symm
            _ = (A * Z).trace := by rw [← hXA]; congr 1; noncomm_ring
        let U := hX.isHermitian.eigenvectorUnitary
        let V := star U
        let f := Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) V
        let lam : Fin n → ℝ := hX.isHermitian.eigenvalues
        let L : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lam
        let J := f D
        let K := f E
        have hlam (i : Fin n) : 0 < lam i := hX.eigenvalues_pos i
        have hftr (M : Matrix (Fin n) (Fin n) ℝ) : (f M).trace = M.trace := by
          simp only [f, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
            Unitary.coe_star_mul_self, Matrix.one_mul]
        have hfdet (M : Matrix (Fin n) (Fin n) ℝ) : (f M).det = M.det := by
          change (Unitary.conjStarAlgAut ℝ _ V M).det = M.det
          rw [Unitary.conjStarAlgAut_apply]
          calc
            _ = ((V : Matrix (Fin n) (Fin n) ℝ) *
              star (V : Matrix (Fin n) (Fin n) ℝ)).det * M.det := by
                simp only [Matrix.det_mul]
                ring
            _ = _ := by rw [← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.det_one, one_mul]
        have hfpd (M : Matrix (Fin n) (Fin n) ℝ) : (f M).PosDef ↔ M.PosDef := by
          change ((V : Matrix (Fin n) (Fin n) ℝ) * M * star (V : Matrix (Fin n) (Fin n) ℝ)).PosDef ↔ _
          exact Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe (U := V))
        have hfX : f X = L := by
          simpa only [f, V, U, L, lam, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
            hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
        have hJ : J.IsHermitian := by
          change star (f D) = f D
          rw [← map_star]
          exact congrArg f hD.eq
        have hK : K.IsHermitian := by
          change star (f E) = f E
          rw [← map_star]
          exact congrArg f hE.eq
        have hJKorth : (J * K).trace = 0 := by
          change (f D * f E).trace = 0
          rw [← map_mul, hftr, hDEorth]
        have hfXi : f X⁻¹ = Matrix.diagonal (fun i => (lam i)⁻¹) := by
          have hh : L * f X⁻¹ = 1 := by
            rw [← hfX, ← map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hX.det_pos.ne'), map_one]
          have hd : Matrix.diagonal (fun i => (lam i)⁻¹) * L = 1 := by
            simp only [L, Matrix.diagonal_mul_diagonal]
            have he : (fun i => (lam i)⁻¹ * lam i) = (fun _ => (1 : ℝ)) := by
              funext i
              exact inv_mul_cancel₀ (hlam i).ne'
            rw [he, Matrix.diagonal_one]
          calc
            _ = 1 * f X⁻¹ := (Matrix.one_mul _).symm
            _ = _ := by rw [← hd, Matrix.mul_assoc, hh, Matrix.mul_one]
        have hJK : J + K = Matrix.diagonal (fun i => (lam i)⁻¹ - ρ * lam i) := by
          have hh := congrArg f hDE
          simpa [map_add, map_sub, map_smul, hfXi, hfX, ← Matrix.diagonal_smul,
            ← Matrix.diagonal_sub, J, K, L, Pi.smul_def] using hh
        have hS : (∑ i, lam i ^ 2) = (A * Z).trace := by
          rw [← hXS, hspecsq n X hX.isHermitian]
        have hnorm : (J * J).trace + (K * K).trace =
            ∑ i, ((lam i)⁻¹ - ρ * lam i) ^ 2 := by
          have hh := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => (M * M).trace) hJK
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add,
            Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal] at hh
          rw [Matrix.trace_mul_comm K J, hJKorth] at hh
          simpa only [sq, add_zero, zero_add] using hh
        have hscalar (z y N : ℝ) (hz : 1 ≤ z) (hy : 1 ≤ y)
            (hc : (N - 1) ^ 2 ≤ (z - 1) * (y - 1)) :
            3 / 4 * z ≤ z * y - N * (N - 1) := by
          by_contra h
          have hlt := lt_of_not_ge h
          have ht : y < N - z / 4 := by nlinarith only [hc, hlt]
          by_cases he : z = 1
          · subst z
            nlinarith only [hc, ht, hy]
          · have hzpos : 0 < z - 1 := sub_pos.mpr (lt_of_le_of_ne hz (Ne.symm he))
            have hp := mul_pos hzpos (sub_pos.mpr ht)
            nlinarith only [hc, hp, hz, sq_nonneg (z - 2 * N + 1)]
        letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
        obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
        let μ := lam k
        have hμ : 0 < μ := hlam k
        have hmin (i : Fin n) : μ ≤ lam i := hk i (Finset.mem_univ i)
        let S := ∑ i, lam i ^ 2
        let T := ∑ i, (lam i)⁻¹ ^ 2
        let d2 := (J * J).trace + (K * K).trace
        have hSpos : 0 < S := by
          exact Finset.sum_pos (fun i _ => sq_pos_of_pos (hlam i)) Finset.univ_nonempty
        have hSge : (n : ℝ) * μ ^ 2 ≤ S := by
          calc
            _ = ∑ _ : Fin n, μ ^ 2 := by simp
            _ ≤ _ := Finset.sum_le_sum fun i _ => by nlinarith only [hlam i, hmin i, hμ]
        have hTge : 1 ≤ μ ^ 2 * T := by
          have hs := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
            sq_nonneg ((lam i)⁻¹)) (Finset.mem_univ k)
          have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg μ)
          have he : μ ^ 2 * (lam k)⁻¹ ^ 2 = 1 := by dsimp [μ]; field_simp [(hlam k).ne']
          nlinarith only [hp, he]
        have hcs : ((n : ℝ) - 1) ^ 2 ≤
            (S / μ ^ 2 - 1) * (μ ^ 2 * T - 1) := by
          have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ.erase k)
            lam (fun i => (lam i)⁻¹)
          have hleft : (∑ i ∈ Finset.univ.erase k, lam i * (lam i)⁻¹) = (n : ℝ) - 1 := by
            simp only [mul_inv_cancel₀ (hlam _).ne', Finset.sum_const, nsmul_eq_mul, mul_one,
              Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            norm_num
          have hsum1 : (∑ i ∈ Finset.univ.erase k, lam i ^ 2) = S - μ ^ 2 := by
            rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
          have hsum2 : (∑ i ∈ Finset.univ.erase k, (lam i)⁻¹ ^ 2) = T - μ⁻¹ ^ 2 := by
            rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
          rw [hleft, hsum1, hsum2] at hh
          have he : (S / μ ^ 2 - 1) * (μ ^ 2 * T - 1) =
              (S - μ ^ 2) * (T - μ⁻¹ ^ 2) := by field_simp [hμ.ne'] <;> ring
          rw [he]
          exact hh
        have hz : 1 ≤ S / μ ^ 2 := by
          apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          calc
            _ ≤ (n : ℝ) * μ ^ 2 := mul_le_mul_of_nonneg_right hn1 (sq_nonneg μ)
            _ ≤ S := hSge
        have hscl := hscalar (S / μ ^ 2) (μ ^ 2 * T) n hz hTge hcs
        have hρ : ρ * S = n + ν * Real.sqrt n := by
          dsimp [ρ]
          rw [← hS, div_mul_cancel₀ _ hSpos.ne']
        have hd2 : d2 = T + ρ ^ 2 * S - 2 * ρ * n := by
          change (J * J).trace + (K * K).trace = _
          rw [hnorm]
          have ht (i : Fin n) : ((lam i)⁻¹ - ρ * lam i) ^ 2 =
              (lam i)⁻¹ ^ 2 + ρ ^ 2 * lam i ^ 2 - 2 * ρ := by
            field_simp [(hlam i).ne']
            <;> ring
          simp only [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          dsimp [S, T]
          rw [Finset.mul_sum]
          ring
        have hng : (n : ℝ) ≤ (ν * Real.sqrt n) ^ 2 := by
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have hs : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn0
          have hν0 : 0 ≤ ν := by linarith only [hν]
          have hh : Real.sqrt n ≤ ν * Real.sqrt n := by
            nlinarith only [mul_nonneg (sub_nonneg.mpr hν) (Real.sqrt_nonneg (n : ℝ))]
          have haux (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
            nlinarith only [ha, hab]
          calc
            (n : ℝ) = (Real.sqrt n) ^ 2 := hs.symm
            _ ≤ _ := haux _ _ (Real.sqrt_nonneg (n : ℝ)) hh
        have hdnum : (3 / 4 : ℝ) ≤ μ ^ 2 * d2 := by
          have hrel : d2 * S = T * S + (ν * Real.sqrt n) ^ 2 - (n : ℝ) ^ 2 := by
            calc
              _ = T * S + (ρ * S) ^ 2 - 2 * n * (ρ * S) := by rw [hd2]; ring
              _ = _ := by rw [hρ]; ring
          have hsimp : (3 / 4 : ℝ) * S ≤ μ ^ 2 * (S * T - (n : ℝ) * (n - 1)) := by
            have heL : μ ^ 2 * ((3 / 4 : ℝ) * (S / μ ^ 2)) = (3 / 4 : ℝ) * S := by
              field_simp [hμ.ne']
              <;> ring
            have heR : μ ^ 2 * (S / μ ^ 2 * (μ ^ 2 * T) - (n : ℝ) * (n - 1)) =
                μ ^ 2 * (S * T - (n : ℝ) * (n - 1)) := by
              field_simp [hμ.ne']
              <;> ring
            have hh := mul_le_mul_of_nonneg_left hscl (sq_nonneg μ)
            rwa [heL, heR] at hh
          have hh := mul_nonneg (sq_nonneg μ) (sub_nonneg.mpr hng)
          have hmr := congrArg (fun z : ℝ => μ ^ 2 * z) hrel
          have hbd : (3 / 4 : ℝ) * S ≤ (μ ^ 2 * d2) * S := by
            linear_combination hsimp + hh - hmr
          exact le_of_mul_le_mul_right hbd hSpos
        have hd2pos : 0 < d2 := by
          by_contra! hh
          have ht := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg μ) hh
          linarith only [ht, hdnum]
        let d := Real.sqrt d2
        have hdpos : 0 < d := Real.sqrt_pos.mpr hd2pos
        have hd : d ^ 2 = d2 := Real.sq_sqrt hd2pos.le
        have hγ : (173 / 200 : ℝ) ≤ μ * d := by
          have he : (μ * d) ^ 2 = μ ^ 2 * d2 := by rw [mul_pow, hd]
          have haux (a : ℝ) (ha : 0 ≤ a) (hb : (3 / 4 : ℝ) ≤ a ^ 2) :
              (173 / 200 : ℝ) ≤ a := by nlinarith only [ha, hb]
          exact haux (μ * d) (mul_nonneg hμ.le hdpos.le) (he.symm ▸ hdnum)
        let t : ℝ := (9 / 20 : ℝ) * μ / d
        have htpos : 0 < t := div_pos (mul_pos (by norm_num) hμ) hdpos
        have htnorm : (t ^ 2 / μ ^ 2) * d2 = (9 / 20 : ℝ) ^ 2 := by
          rw [← hd]
          dsimp [t]
          field_simp [hdpos.ne', hμ.ne']
          <;> ring
        let B (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
          fun i j => t * M i j / (Real.sqrt (lam i) * Real.sqrt (lam j))
        have hBherm (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
            (B M).IsHermitian := by
          have hsym (i j : Fin n) : M j i = M i j := by
            simpa using congrFun (congrFun hM.eq i) j
          apply Matrix.isHermitian_iff_isSymm.mpr
          change (B M).transpose = B M
          ext i j
          change t * M j i / (Real.sqrt (lam j) * Real.sqrt (lam i)) =
            t * M i j / (Real.sqrt (lam i) * Real.sqrt (lam j))
          rw [hsym, mul_comm (Real.sqrt (lam j)) (Real.sqrt (lam i))]
        have hnormnonneg (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
            0 ≤ (M * M).trace := by
          rw [hfrobsq n M hM]
          exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
        have hBbound (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) :
            (B M * B M).trace ≤ (t ^ 2 / μ ^ 2) * (M * M).trace := by
          rw [hfrobsq n (B M) (hBherm M hM), hfrobsq n M hM]
          simp only [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          have he : (B M i j) ^ 2 = t ^ 2 * (M i j) ^ 2 / (lam i * lam j) := by
            simp only [B, div_pow, mul_pow, Real.sq_sqrt (hlam i).le, Real.sq_sqrt (hlam j).le]
          rw [he]
          have hm : μ ^ 2 ≤ lam i * lam j := by
            have hh := mul_le_mul (hmin i) (hmin j) hμ.le (hlam i).le
            simpa only [pow_two] using hh
          calc
            _ ≤ t ^ 2 * (M i j) ^ 2 / μ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg t) (sq_nonneg (M i j))) (sq_pos_of_pos hμ) hm
            _ = _ := mul_div_right_comm _ _ _
        have hBsum : (B J * B J).trace + (B K * B K).trace ≤ (9 / 20 : ℝ) ^ 2 := by
          calc
            _ ≤ (t ^ 2 / μ ^ 2) * (J * J).trace +
                (t ^ 2 / μ ^ 2) * (K * K).trace := add_le_add (hBbound J hJ) (hBbound K hK)
            _ = (t ^ 2 / μ ^ 2) * d2 := by dsimp only [d2]; ring
            _ = _ := htnorm
        have hBJ := hbarrier n (B J) (hBherm J hJ)
          ((le_add_of_nonneg_right (hnormnonneg (B K) (hBherm K hK))).trans hBsum)
        have hBK := hbarrier n (B K) (hBherm K hK)
          ((le_add_of_nonneg_left (hnormnonneg (B J) (hBherm J hJ))).trans hBsum)
        let C : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => Real.sqrt (lam i))
        have hC : C.PosDef := Matrix.PosDef.diagonal fun i => Real.sqrt_pos.mpr (hlam i)
        have hCstar : star C = C := Matrix.isHermitian_diagonal _
        have hC2 : C * C = L := by
          dsimp only [C, L]
          rw [Matrix.diagonal_mul_diagonal]
          congr 1
          funext i
          exact Real.mul_self_sqrt (hlam i).le
        have hcong (M : Matrix (Fin n) (Fin n) ℝ) : C * (1 + B M) * C = L + t • M := by
          ext i j
          simp only [C, Matrix.mul_diagonal, Matrix.diagonal_mul]
          change Real.sqrt (lam i) * ((1 : Matrix (Fin n) (Fin n) ℝ) i j +
            t * M i j / (Real.sqrt (lam i) * Real.sqrt (lam j))) * Real.sqrt (lam j) =
            Matrix.diagonal lam i j + t * M i j
          rw [Matrix.one_apply, Matrix.diagonal_apply]
          have hi : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
          have hj : Real.sqrt (lam j) ≠ 0 := (Real.sqrt_pos.mpr (hlam j)).ne'
          split_ifs with hij
          · subst j
            field_simp [hi]
            nlinarith only [Real.sq_sqrt (hlam i).le]
          · field_simp [hi, hj]
            <;> ring
        have htrial (M : Matrix (Fin n) (Fin n) ℝ) (hb : (1 + B M).PosDef) :
            (L + t • M).PosDef ∧
            Real.log (L + t • M).det = Real.log L.det + Real.log (1 + B M).det := by
          have hp : (L + t • M).PosDef := by
            have hh := (Matrix.IsUnit.posDef_star_right_conjugate_iff hC.isUnit).mpr hb
            simpa only [hCstar, hcong] using hh
          refine ⟨hp, ?_⟩
          have hdet : (L + t • M).det = L.det * (1 + B M).det := by
            rw [← hcong M, ← hC2]
            simp only [Matrix.det_mul]
            ring
          rw [hdet, Real.log_mul (Matrix.PosDef.diagonal hlam).det_pos.ne' hb.det_pos.ne']
        have hTJ := htrial J hBJ.1
        have hTK := htrial K hBK.1
        have hBadd (M N : Matrix (Fin n) (Fin n) ℝ) : B (M + N) = B M + B N := by
          ext i j
          change t * (M i j + N i j) / (Real.sqrt (lam i) * Real.sqrt (lam j)) =
            t * M i j / (Real.sqrt (lam i) * Real.sqrt (lam j)) +
            t * N i j / (Real.sqrt (lam i) * Real.sqrt (lam j))
          ring
        have hBtrace : (B J).trace + (B K).trace = t * (T - ρ * n) := by
          rw [← Matrix.trace_add, ← hBadd, hJK]
          simp only [Matrix.trace, Matrix.diag, B, Matrix.diagonal_apply_eq,
            Real.mul_self_sqrt (hlam _).le]
          have he (i : Fin n) : t * ((lam i)⁻¹ - ρ * lam i) / lam i =
              t * ((lam i)⁻¹ ^ 2 - ρ) := by
            field_simp [(hlam i).ne']
            <;> ring
          simp_rw [he]
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, T]
          ring
        have hprodpos (M N : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) (hN : N.PosDef) :
            0 < (M * N).trace := by
          let C0 := CFC.sqrt M
          have hc0 : star C0 = C0 := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
          have hcu : IsUnit C0 := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
          have hp : (C0 * N * C0).PosDef := by
            have hh := (Matrix.IsUnit.posDef_star_right_conjugate_iff hcu).mpr hN
            simpa only [hc0] using hh
          have hh := hp.trace_pos
          change 0 < (CFC.sqrt M * N * CFC.sqrt M).trace at hh
          rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg] at hh
          exact hh
        have hprim (s : ℝ) : ri * (A + s • H) * ri = X + s • D := by
          rw [← hXA]
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_assoc, hIR, hrr, Matrix.mul_one, D]
        have hdualt (s : ℝ) : r * (Z + s • δZ) * r = X + s • E := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, X, E]
        have hpair (s u : ℝ) : (X + s • D) * (X + u • E) =
            ri * ((A + s • H) * (Z + u • δZ)) * r := by
          rw [← hprim s, ← hdualt u]
          simp only [Matrix.mul_assoc, hIR]
        have hpairtr (s u : ℝ) : ((A + s • H) * (Z + u • δZ)).trace =
            ((L + s • J) * (L + u • K)).trace := by
          calc
            _ = (ri * ((A + s • H) * (Z + u • δZ)) * r).trace :=
              (Matrix.trace_units_conj' R _).symm
            _ = ((X + s • D) * (X + u • E)).trace := by rw [hpair]
            _ = (f ((X + s • D) * (X + u • E))).trace := (hftr _).symm
            _ = _ := by simp only [map_mul, map_add, map_smul, hfX, J, K]
        have hpairdet (s u : ℝ) : ((A + s • H) * (Z + u • δZ)).det =
            ((L + s • J) * (L + u • K)).det := by
          calc
            _ = (ri * ((A + s • H) * (Z + u • δZ)) * r).det :=
              (Matrix.det_units_conj' R _).symm
            _ = ((X + s • D) * (X + u • E)).det := by rw [hpair]
            _ = (f ((X + s • D) * (X + u • E))).det := (hfdet _).symm
            _ = _ := by simp only [map_mul, map_add, map_smul, hfX, J, K]
        have hXJ : (X + t • D).PosDef := by
          apply (hfpd _).mp
          simpa only [map_add, map_smul, hfX, J] using hTJ.1
        have hXK : (X + t • E).PosDef := by
          apply (hfpd _).mp
          simpa only [map_add, map_smul, hfX, K] using hTK.1
        have hAt : (A + t • H).PosDef := by
          apply (Matrix.IsUnit.posDef_star_right_conjugate_iff (show IsUnit ri from (R⁻¹).isUnit)).mp
          simpa only [hRIstar, hprim] using hXJ
        have hZt : (Z + t • δZ).PosDef := by
          apply (Matrix.IsUnit.posDef_star_right_conjugate_iff (show IsUnit r from R.isUnit)).mp
          simpa only [hRstar, hdualt] using hXK
        have hφ (s u : ℝ) :
            VBSDP.Potential.phi ν F₀ F (x + s • δx) (Z + u • δZ) =
            ((n : ℝ) + ν * Real.sqrt n) * Real.log ((L + s • J) * (L + u • K)).trace -
              Real.log ((L + s • J) * (L + u • K)).det - n * Real.log n := by
          rw [VBSDP.Potential.phi, VBSDP.Potential.psi, hlmi s, hpairtr, hpairdet]
          ring
        have hLL : (L * L).trace = S := by
          simp only [L, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, S, sq]
        have hLdet : 0 < L.det := (Matrix.PosDef.diagonal hlam).det_pos
        have hφ0 : VBSDP.Potential.phi ν F₀ F x Z =
            ((n : ℝ) + ν * Real.sqrt n) * Real.log S -
              2 * Real.log L.det - n * Real.log n := by
          have hh := hφ 0 0
          simp only [zero_smul, add_zero, hLL, Matrix.det_mul,
            Real.log_mul hLdet.ne' hLdet.ne'] at hh
          nlinarith only [hh]
        let G := ((L + t • J) * (L + t • K)).trace
        have hGpos : 0 < G := hprodpos _ _ hTJ.1 hTK.1
        have hLG : (L * (J + K)).trace = (n : ℝ) - ρ * S := by
          rw [hJK]
          simp only [L, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
          have he (i : Fin n) : lam i * ((lam i)⁻¹ - ρ * lam i) = 1 - ρ * lam i ^ 2 := by
            field_simp [(hlam i).ne']
            <;> ring
          simp only [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.mul_sum,
            nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, mul_one, S]
        have hG : G = S + t * ((n : ℝ) - ρ * S) := by
          have hc : (L * K).trace + (J * L).trace = (n : ℝ) - ρ * S := by
            rw [Matrix.trace_mul_comm J L, ← Matrix.trace_add, ← Matrix.mul_add, add_comm K J]
            exact hLG
          dsimp [G]
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.trace_add, Matrix.trace_smul, hLL, hJKorth, smul_eq_mul, mul_zero, add_zero]
          linear_combination t * hc
        have hloggap : Real.log G - Real.log S ≤ (G - S) / S := by
          have hh := Real.log_le_sub_one_of_pos (div_pos hGpos hSpos)
          rw [Real.log_div hGpos.ne' hSpos.ne'] at hh
          convert hh using 1 <;> field_simp [hSpos.ne'] <;> ring
        have hap : 0 ≤ (n : ℝ) + ν * Real.sqrt n := by positivity
        have hlinlog : ((n : ℝ) + ν * Real.sqrt n) * (Real.log G - Real.log S) ≤
            ρ * t * ((n : ℝ) - ρ * S) := by
          calc
            _ ≤ ((n : ℝ) + ν * Real.sqrt n) * ((G - S) / S) :=
              mul_le_mul_of_nonneg_left hloggap hap
            _ = _ := by rw [← hρ, hG]; field_simp [hSpos.ne']; ring
        have hdetDelta :
            2 * Real.log L.det + t * (T - ρ * n) - (147 / 200 : ℝ) * (9 / 20 : ℝ) ^ 2 ≤
              Real.log (L + t • J).det + Real.log (L + t • K).det := by
          nlinarith only [hBJ.2, hBK.2, hTJ.2, hTK.2, hBtrace, hBsum]
        have hid : ρ * t * ((n : ℝ) - ρ * S) - t * (T - ρ * n) = -t * d2 := by
          rw [hd2]
          ring
        have hpotential :
            VBSDP.Potential.phi ν F₀ F (x + t • δx) (Z + t • δZ) ≤
            VBSDP.Potential.phi ν F₀ F x Z - t * d2 + (147 / 200 : ℝ) * (9 / 20 : ℝ) ^ 2 := by
          rw [hφ t t, hφ0, Matrix.det_mul, Real.log_mul hTJ.1.det_pos.ne' hTK.1.det_pos.ne']
          change ((n : ℝ) + ν * Real.sqrt n) * Real.log G - _ - _ ≤ _
          nlinarith only [hlinlog, hdetDelta, hid]
        have htd : t * d2 = (9 / 20 : ℝ) * (μ * d) := by
          rw [← hd]
          dsimp [t]
          field_simp [hdpos.ne']
          <;> ring
        have hdecnum : (0.24 : ℝ) ≤ t * d2 - (147 / 200 : ℝ) * (9 / 20 : ℝ) ^ 2 := by
          rw [htd]
          nlinarith only [hγ]
        have hbest := hpq.2 t t (hfeas t t hAt hZt)
        linarith only [hbest, hpotential, hdecnum]
