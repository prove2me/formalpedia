-- Prove2me | solution 1 for VBSDP.Duality.Supplement.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:27.504809+00:00
-- url     : https://prove2.me/submissions/6e2a85f1-7c1a-465a-a123-fdb051116892

import Mathlib
import Definitions.Def_VBSDP_Duality_Supplement_IsPrimalSearchDirection
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
    (hdir : IsPrimalSearchDirection ν c F₀ F x Z δx δZ)
    (p q : ℝ) (hpq : IsPlaneSearchMinimizer ν c F₀ F x Z δx δZ p q) :
    VBSDP.Potential.phi ν F₀ F (x + p • δx) (Z + q • δZ) ≤
      VBSDP.Potential.phi ν F₀ F x Z - 0.05 := by
        set_option maxHeartbeats 2000000 in
        open Matrix in
        · have hscal : ∀ u r : ℝ, |u| ≤ r → r < 1 →
              -Real.log (1 - u) ≤ u + (1/2 + r/3 + r^2/(1-r)) * u^2 := by
            intro u r hu hr
            have h := Real.abs_log_sub_add_sum_range_le (lt_of_le_of_lt hu hr) 3
            simp [Finset.sum_range_succ] at h
            have h1 := (abs_le.mp h).1
            have hua : 0 ≤ |u| := abs_nonneg u
            have h4 : |u|^4/(1-|u|) ≤ r^2/(1-r) * u^2 := by
              rw [div_mul_eq_mul_div]
              apply div_le_div₀ (by positivity) _ (by linarith) (by linarith)
              have : |u|^4 = u^2 * |u|^2 := by rw [← sq_abs u]; ring
              rw [this]; nlinarith [sq_abs u, mul_le_mul hu hu hua (by linarith), sq_nonneg u]
            have h3 : u^3 ≤ r * u^2 := by nlinarith [le_abs_self u, sq_nonneg u]
            have : r^2/(1-r)*u^2 = r^2/(1-r)*u^2 := rfl
            nlinarith
          have key1 : ∀ a b c : ℝ, 0 < a → c * ((a - b)/a - 1) = -(c*b/a) := by
            intro a b c ha; field_simp; try ring
          have key2 : ∀ a b c : ℝ, 0 < a → (a*a + b*a)*c/(a*a) = c + b*(c/a) := by
            intro a b c ha; field_simp; try ring
          have key3 : ∀ a : ℝ, 0 < a → (1 + 1/a) * (a*a) = a*a + a := by
            intro a ha; field_simp; try ring
          have hdecomp : ∀ (G D : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) (hD : D.IsHermitian),
            ∃ (C Cinv : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ), C * Cinv = 1 ∧ Cinv * C = 1 ∧
              G = Cᴴ * C ∧ D = Cᴴ * diagonal lam * C := by
            intro G D hG hD
            have hGh := hG.1
            set μ := hGh.eigenvalues with hμ
            set U : Matrix (Fin n) (Fin n) ℝ := (hGh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUdef
            have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hGh.eigenvectorUnitary.2
            have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hGh.eigenvectorUnitary.2
            have hspec : G = U * diagonal μ * star U := by
              have := hGh.spectral_theorem
              rw [Unitary.conjStarAlgAut_apply] at this
              simpa using this
            have hμpos : ∀ i, 0 < μ i := hG.eigenvalues_pos
            set B : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => Real.sqrt (μ i)) * star U with hB
            set Binv : Matrix (Fin n) (Fin n) ℝ := U * diagonal (fun i => 1 / Real.sqrt (μ i)) with hBinv
            have hdd : diagonal (fun i => Real.sqrt (μ i)) * diagonal (fun i => 1 / Real.sqrt (μ i)) = 1 := by
              rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
              have := Real.sqrt_pos.mpr (hμpos i); field_simp
            have hdd' : diagonal (fun i => 1 / Real.sqrt (μ i)) * diagonal (fun i => Real.sqrt (μ i)) = 1 := by
              rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
              have := Real.sqrt_pos.mpr (hμpos i); field_simp
            have hBBinv : B * Binv = 1 := by
              rw [hB, hBinv, Matrix.mul_assoc, ← Matrix.mul_assoc (star U), hU1, Matrix.one_mul, hdd]
            have hBinvB : Binv * B = 1 := by
              rw [hB, hBinv, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), hdd', Matrix.one_mul, hU2]
            have hGB : G = Bᴴ * B := by
              rw [hspec, hB]
              simp only [conjTranspose_mul, diagonal_conjTranspose, star_eq_conjTranspose, conjTranspose_conjTranspose]
              have : (star fun i => Real.sqrt (μ i)) = fun i => Real.sqrt (μ i) := by
                funext i; simp
              rw [this]
              rw [show U * diagonal (fun i => Real.sqrt (μ i)) * (diagonal (fun i => Real.sqrt (μ i)) * Uᴴ)
                  = U * (diagonal (fun i => Real.sqrt (μ i)) * diagonal (fun i => Real.sqrt (μ i))) * Uᴴ by
                    simp only [Matrix.mul_assoc]]
              rw [diagonal_mul_diagonal]
              congr 3; funext i; exact (Real.mul_self_sqrt (hμpos i).le).symm
            set A' := Binvᴴ * D * Binv with hA'
            have hA'h : A'.IsHermitian := isHermitian_conjTranspose_mul_mul Binv hD
            set lam := hA'h.eigenvalues
            set V : Matrix (Fin n) (Fin n) ℝ := (hA'h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hVdef
            have hV1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hA'h.eigenvectorUnitary.2
            have hV2 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hA'h.eigenvectorUnitary.2
            have hspecA : A' = V * diagonal lam * star V := by
              have := hA'h.spectral_theorem
              rw [Unitary.conjStarAlgAut_apply] at this
              simpa using this
            refine ⟨star V * B, Binv * V, lam, ?_, ?_, ?_, ?_⟩
            · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, hBBinv, Matrix.one_mul, hV1]
            · rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hV2, Matrix.one_mul, hBinvB]
            · rw [hGB]
              simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose]
              rw [star_eq_conjTranspose] at hV2
              calc Bᴴ * B = Bᴴ * (V * Vᴴ) * B := by rw [hV2, Matrix.mul_one]
                _ = _ := by simp only [Matrix.mul_assoc]
            · have h1 : (star V * B)ᴴ * diagonal lam * (star V * B) = Bᴴ * A' * B := by
                rw [hspecA]
                simp only [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
              rw [h1, hA']
              have h2 : Bᴴ * Binvᴴ = 1 := by rw [← conjTranspose_mul, hBinvB, conjTranspose_one]
              calc D = (Bᴴ * Binvᴴ) * D * (Binv * B) := by rw [h2, hBinvB, Matrix.one_mul, Matrix.mul_one]
                _ = _ := by simp only [Matrix.mul_assoc]
          have hphi : ∀ x' Z', VBSDP.Potential.phi ν F₀ F x' Z' =
              ((n:ℝ) + ν * Real.sqrt n) * Real.log (VBSDP.Duality.lmi F₀ F x' * Z').trace
                - Real.log (VBSDP.Duality.lmi F₀ F x' * Z').det - n * Real.log n := by
            intro x' Z'
            unfold VBSDP.Potential.phi VBSDP.Potential.psi; ring
          have hlmi : ∀ t : ℝ, VBSDP.Duality.lmi F₀ F (x + t • δx) =
              VBSDP.Duality.lmi F₀ F x + t • ∑ i, δx i • F i := by
            intro t
            unfold VBSDP.Duality.lmi
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib,
              Finset.smul_sum, smul_smul]
            abel
          set G := VBSDP.Duality.lmi F₀ F x with hGdef
          set D : Matrix (Fin n) (Fin n) ℝ := ∑ i, δx i • F i with hDdef
          have hD : D.IsHermitian := by
            unfold Matrix.IsHermitian
            rw [hDdef, Matrix.conjTranspose_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Matrix.conjTranspose_smul, (hF i).eq]; simp
          obtain ⟨C, Cinv, lam, hCC, hCC', hGC, hDC⟩ := hdecomp G D hxZ.1 hD
          have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
          have hZ : Z.PosDef := hxZ.2.1
          have hinj : Function.Injective C.mulVec := by
            intro v w h
            have := congrArg (Cinv.mulVec) h
            simpa [Matrix.mulVec_mulVec, hCC'] using this
          have hinjv : Function.Injective fun v : Fin n → ℝ => v ᵥ* C := by
            intro v w h
            have := congrArg (fun u => u ᵥ* Cinv) h
            simpa [Matrix.vecMul_vecMul, hCC] using this
          have hinjv' : Function.Injective fun v : Fin n → ℝ => v ᵥ* Cinv := by
            intro v w h
            have := congrArg (fun u => u ᵥ* C) h
            simpa [Matrix.vecMul_vecMul, hCC'] using this
          have hL : Cinvᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, hCC, conjTranspose_one]
          have hL2 : Cᴴ * Cinvᴴ = 1 := by rw [← conjTranspose_mul, hCC', conjTranspose_one]
          set W := C * Z * Cᴴ with hWdef
          have hW : W.PosDef := hZ.mul_mul_conjTranspose_same hinjv
          have htr : ∀ Y : Matrix (Fin n) (Fin n) ℝ, (G * Y).trace = (C * Y * Cᴴ).trace := by
            intro Y; rw [hGC, Matrix.mul_assoc, trace_mul_comm]
          have hdet : ∀ Y : Matrix (Fin n) (Fin n) ℝ, (G * Y).det = (C * Y * Cᴴ).det := by
            intro Y; rw [hGC]; simp only [det_mul]; ring
          set S := (G * Z).trace with hSdef
          have hSW : S = W.trace := htr Z
          have hSpos : 0 < S := hSW ▸ hW.trace_pos
          have hcx : c ⬝ᵥ x + (F₀ * Z).trace = S := by
            have : S = (F₀*Z).trace + ∑ i, x i * (F i * Z).trace := by
              simp [hSdef, hGdef, VBSDP.Duality.lmi, add_mul, Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc]
            rw [this]; simp [dotProduct, hxZ.2.2, mul_comm]; ring
          set N : ℝ := (n:ℝ) + ν * Real.sqrt n with hNdef
          set ρ : ℝ := N / S with hρdef
          have hs1 : 1 ≤ Real.sqrt n := by
            rw [Real.one_le_sqrt]; exact_mod_cast hn
          have hNpos : 0 < N := by positivity
          have hρpos : 0 < ρ := by positivity
          set M := C * δZ * Cᴴ with hMdef
          have hrel : M + diagonal lam = -ρ • W + 1 := by
            have E := hdir.2.1
            rw [hcx] at E
            have E2 := congrArg (fun X => Cinvᴴ * X * Cinv) E
            beta_reduce at E2
            rw [← hGdef, ← hDdef, ← hNdef, ← hρdef, hGC, hDC] at E2
            have hL' : ∀ X : Matrix (Fin n) (Fin n) ℝ, Cinvᴴ * (Cᴴ * X) = X := by
              intro X; rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
              hL', hCC, Matrix.mul_one] at E2
            rw [hMdef, hWdef]; simp only [Matrix.mul_assoc]
            rw [← E2]
          have hent : ∀ i, M i i + lam i = -ρ * W i i + 1 := by
            intro i
            have := congrFun (congrFun hrel i) i
            simpa [Matrix.add_apply, diagonal_apply_eq, one_apply_eq] using this
          have horth : ∑ i, lam i * M i i = 0 := by
            have h0 : (D * δZ).trace = 0 := by
              simp [hDdef, Finset.sum_mul, Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, hdir.2.2]
            rw [hDC, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm] at h0
            rw [← h0, hMdef]
            simp [Matrix.trace, Matrix.diagonal_mul, Matrix.mul_assoc]
          set σ := ∑ i, lam i ^ 2 with hσdef
          set T := ∑ i, lam i with hTdef
          have hkey : ρ * ∑ i, lam i * W i i = T - σ := by
            have : ∑ i, lam i * (M i i + lam i) = σ := by
              simp only [mul_add, Finset.sum_add_distrib, horth, zero_add, hσdef, sq]
            rw [Finset.mul_sum, hTdef, ← this, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have := hent i; linear_combination (lam i) * this
          have hlamle : ∀ i, |lam i| ≤ Real.sqrt σ := by
            intro i
            apply Real.abs_le_sqrt
            exact Finset.single_le_sum (f := fun i => lam i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
          have hσnn : 0 ≤ σ := Finset.sum_nonneg (fun j _ => sq_nonneg _)
          have hphi0 : VBSDP.Potential.phi ν F₀ F x Z = N * Real.log S - Real.log W.det - n * Real.log n := by
            rw [hphi, ← hGdef, hdet Z]
          have hnpos : (0:ℝ) < n := by exact_mod_cast hn
          set s := Real.sqrt (n:ℝ) with hsdef
          have hss : s * s = n := Real.mul_self_sqrt hnpos.le
          by_cases hσc : 4/25 ≤ σ
          · set a := Real.sqrt σ with ha
            have ha4 : 2/5 ≤ a := by rw [ha, Real.le_sqrt (by norm_num) hσnn]; linarith only [hσc]
            have hapos : 0 < a := by linarith only [ha4]
            have haa : a^2 = σ := Real.sq_sqrt hσnn
            set p0 := 1/(4*a) with hp0
            have hp0pos : 0 < p0 := by positivity
            have hu : ∀ i, |p0 * lam i| ≤ 1/4 := by
              intro i; rw [abs_mul, abs_of_pos hp0pos, hp0]
              have := hlamle i
              rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith only [this]
            have hd1 : ∀ i, 0 < 1 + p0 * lam i := by
              intro i; have := (abs_le.mp (hu i)).1; linarith only [this]
            have hG' : VBSDP.Duality.lmi F₀ F (x + p0 • δx) = Cᴴ * diagonal (fun i => 1 + p0 * lam i) * C := by
              rw [hlmi, hGC, hDC]
              have : diagonal (fun i => 1 + p0 * lam i) = 1 + p0 • diagonal lam := by
                ext i j; by_cases h : i = j
                · subst h; simp
                · simp [h, Matrix.one_apply_ne h, diagonal_apply_ne _ h]
              rw [this]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
            have hG'pd : (VBSDP.Duality.lmi F₀ F (x + p0 • δx)).PosDef := by
              rw [hG']; exact (PosDef.diagonal hd1).conjTranspose_mul_mul_same hinj
            have hfeas : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + p0 • δx) (Z + (0:ℝ) • δZ) := by
              rw [zero_smul, add_zero]; exact ⟨hG'pd, hZ, hxZ.2.2⟩
            have hmin := hpq.2 p0 0 hfeas
            rw [zero_smul, add_zero] at hmin
            have htr' : (VBSDP.Duality.lmi F₀ F (x + p0 • δx) * Z).trace = ∑ i, (1 + p0 * lam i) * W i i := by
              rw [hG', Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, hWdef]
              simp [Matrix.trace, Matrix.diagonal_mul, Matrix.mul_assoc]
            have hdet' : (VBSDP.Duality.lmi F₀ F (x + p0 • δx) * Z).det = (∏ i, (1 + p0 * lam i)) * W.det := by
              rw [hG', hWdef]; simp only [det_mul, det_diagonal]; ring
            set S' := ∑ i, (1 + p0 * lam i) * W i i with hS'def
            have hS'pos : 0 < S' := Finset.sum_pos (fun i _ => mul_pos (hd1 i) (hW.diag_pos)) Finset.univ_nonempty
            have hS'S : S' = S + p0 * ∑ i, lam i * W i i := by
              rw [hS'def, hSW, Matrix.trace]
              simp only [add_mul, one_mul, Finset.sum_add_distrib, Finset.mul_sum, diag_apply]
              congr 1; exact Finset.sum_congr rfl (fun i _ => by ring)
            have hWdetpos : 0 < W.det := hW.det_pos
            have hlogdet : Real.log ((∏ i, (1 + p0 * lam i)) * W.det) =
                ∑ i, Real.log (1 + p0 * lam i) + Real.log W.det := by
              rw [Real.log_mul (Finset.prod_pos (fun i _ => hd1 i)).ne' hWdetpos.ne',
                Real.log_prod (fun i _ => (hd1 i).ne')]
            have hlS := Real.log_le_sub_one_of_pos (div_pos hS'pos hSpos)
            rw [Real.log_div hS'pos.ne' hSpos.ne'] at hlS
            have hA : N * (Real.log S' - Real.log S) ≤ p0 * (T - σ) := by
              calc N * (Real.log S' - Real.log S) ≤ N * (S'/S - 1) := mul_le_mul_of_nonneg_left hlS hNpos.le
                _ = p0 * (ρ * ∑ i, lam i * W i i) := by rw [hS'S, hρdef]; field_simp; ring
                _ = p0 * (T - σ) := by rw [hkey]
            have hper : ∀ i, -Real.log (1 + p0 * lam i) ≤ -(p0 * lam i) + 2/3 * (p0 * lam i)^2 := by
              intro i
              have := hscal (-(p0 * lam i)) (1/4) (by rw [abs_neg]; exact hu i) (by norm_num)
              rw [sub_neg_eq_add] at this
              norm_num at this ⊢; linarith only [this]
            have hB : -∑ i, Real.log (1 + p0 * lam i) ≤ -(p0 * T) + 2/3 * (p0^2 * σ) := by
              rw [← Finset.sum_neg_distrib]
              calc _ ≤ ∑ i, (-(p0 * lam i) + 2/3 * (p0 * lam i)^2) := Finset.sum_le_sum (fun i _ => hper i)
                _ = _ := by
                  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_pow, ← Finset.mul_sum, hTdef, hσdef]
            have hp2 : p0^2 * σ = 1/16 := by rw [hp0, ← haa]; field_simp; try ring
            have hp1 : p0 * σ = a/4 := by rw [hp0, ← haa]; field_simp; try ring
            rw [hphi (x + p0 • δx) Z, htr', hdet', hlogdet] at hmin
            rw [hphi0]
            have h005 : (0.05:ℝ) = 1/20 := by norm_num
            rw [h005]
            linarith only [hmin, hA, hB, hp2, hp1, ha4]
          · push_neg at hσc
            have hsa : Real.sqrt σ < 2/5 := by
              rw [Real.sqrt_lt' (by norm_num)]; norm_num; linarith only [hσc]
            have hl : ∀ i, |lam i| ≤ 2/5 := fun i => (hlamle i).trans hsa.le
            have hd2 : ∀ i, 0 < 1 - lam i := fun i => by have := (abs_le.mp (hl i)).2; linarith only [this]
            set q0 := 1/ρ with hq0
            have hZ'W : C * (Z + q0 • δZ) * Cᴴ = diagonal (fun i => (1 - lam i)/ρ) := by
              have h1 : C * (Z + q0 • δZ) * Cᴴ = W + q0 • M := by
                rw [hWdef, hMdef]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
              rw [h1]
              have h2 : M = -ρ • W + 1 - diagonal lam := by rw [← hrel]; abel
              rw [h2]; ext i j
              by_cases h : i = j
              · subst h; simp [hq0]; field_simp; ring
              · simp [h, Matrix.one_apply_ne h, diagonal_apply_ne _ h, hq0]; field_simp; ring
            have hZ'eq : Z + q0 • δZ = Cinv * diagonal (fun i => (1 - lam i)/ρ) * Cinvᴴ := by
              calc Z + q0 • δZ = (Cinv * C) * (Z + q0 • δZ) * (Cᴴ * Cinvᴴ) := by
                    rw [hCC', hL2, Matrix.one_mul, Matrix.mul_one]
                _ = Cinv * (C * (Z + q0 • δZ) * Cᴴ) * Cinvᴴ := by simp only [Matrix.mul_assoc]
                _ = _ := by rw [hZ'W]
            have hZ'pd : (Z + q0 • δZ).PosDef := by
              rw [hZ'eq]
              exact (PosDef.diagonal (fun i => div_pos (hd2 i) hρpos)).mul_mul_conjTranspose_same hinjv'
            have hfeas : VBSDP.Potential.IsStrictlyFeasiblePair c F₀ F (x + (0:ℝ) • δx) (Z + q0 • δZ) := by
              rw [zero_smul, add_zero]
              refine ⟨hxZ.1, hZ'pd, fun i => ?_⟩
              rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, hdir.2.2 i, hxZ.2.2 i]; simp
            have hmin := hpq.2 0 q0 hfeas
            rw [zero_smul, add_zero] at hmin
            have hTlt : T < n := by
              have : ∑ i : Fin n, (1 - lam i) > 0 := Finset.sum_pos (fun i _ => hd2 i) Finset.univ_nonempty
              simp [Finset.sum_sub_distrib, ← hTdef] at this; linarith only [this]
            have htr'' : (G * (Z + q0 • δZ)).trace = (n - T)/ρ := by
              rw [htr, hZ'W, trace_diagonal, ← Finset.sum_div, Finset.sum_sub_distrib]; simp [hTdef]
            have hdet'' : (G * (Z + q0 • δZ)).det = ∏ i, ((1 - lam i)/ρ) := by
              rw [hdet, hZ'W, det_diagonal]
            have hlogtr : Real.log ((n - T)/ρ) = Real.log (n - T) - (Real.log N - Real.log S) := by
              rw [Real.log_div (sub_pos.mpr hTlt).ne' hρpos.ne', hρdef, Real.log_div hNpos.ne' hSpos.ne']
            have hlogdet : Real.log (∏ i, ((1 - lam i)/ρ)) = ∑ i, Real.log (1 - lam i) - n * (Real.log N - Real.log S) := by
              rw [Real.log_prod (fun i _ => (div_pos (hd2 i) hρpos).ne')]
              simp only [Real.log_div (hd2 _).ne' hρpos.ne', Finset.sum_sub_distrib]
              rw [hρdef, Real.log_div hNpos.ne' hSpos.ne']; simp [nsmul_eq_mul]; try ring
            rw [hphi x (Z + q0 • δZ), ← hGdef, htr'', hdet'', hlogtr, hlogdet] at hmin
            rw [hphi0]
            -- AM-GM
            have L3 : Real.log W.det ≤ n * Real.log S - n * Real.log n := by
              have hdetE : W.det = ∏ i, hW.1.eigenvalues i := by rw [hW.1.det_eq_prod_eigenvalues]; simp
              have htrE : S = ∑ i, hW.1.eigenvalues i := by rw [hSW, hW.1.trace_eq_sum_eigenvalues]; simp
              have hpos := hW.eigenvalues_pos
              rw [hdetE, Real.log_prod (fun i _ => (hpos i).ne')]
              have h : ∀ i, Real.log (hW.1.eigenvalues i * n / S) ≤ hW.1.eigenvalues i * n / S - 1 :=
                fun i => Real.log_le_sub_one_of_pos (div_pos (mul_pos (hpos i) hnpos) hSpos)
              have h2 : ∀ i, Real.log (hW.1.eigenvalues i * n / S) = Real.log (hW.1.eigenvalues i) + Real.log n - Real.log S := by
                intro i; rw [Real.log_div (mul_pos (hpos i) hnpos).ne' hSpos.ne', Real.log_mul (hpos i).ne' hnpos.ne']
              have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
              have e1 : ∑ i, Real.log (hW.1.eigenvalues i * n / S) = ∑ i, Real.log (hW.1.eigenvalues i) + n * Real.log n - n * Real.log S := by
                simp only [h2, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              have e2 : ∑ i, (hW.1.eigenvalues i * n / S - 1) = 0 := by
                rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul, ← htrE, mul_div_cancel_left₀ _ hSpos.ne']
                simp
              rw [e1, e2] at hsum
              linarith only [hsum]
            have Q1 : N * (Real.log (n - T) - Real.log n) ≤ -(N * T / n) := by
              have h := Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hTlt) hnpos)
              rw [Real.log_div (sub_pos.mpr hTlt).ne' hnpos.ne'] at h
              calc _ ≤ N * ((n - T)/n - 1) := mul_le_mul_of_nonneg_left h hNpos.le
                _ = _ := key1 _ _ _ hnpos
            have Q2 : N * T / n = T + ν * (T / s) := by
              have hspos : 0 < s := by linarith only [hs1]
              rw [hNdef, ← hss]; exact key2 s ν T hspos
            have hper : ∀ i, -Real.log (1 - lam i) ≤ lam i + 9/10 * lam i ^ 2 := by
              intro i
              have h := hscal (lam i) (2/5) (hl i) (by norm_num)
              have h9 : (1/2 + (2/5)/3 + (2/5)^2/(1-2/5) : ℝ) = 9/10 := by norm_num
              rw [h9] at h; exact h
            have L2 : -∑ i, Real.log (1 - lam i) ≤ T + 9/10 * σ := by
              rw [← Finset.sum_neg_distrib]
              calc _ ≤ ∑ i, (lam i + 9/10 * lam i ^ 2) := Finset.sum_le_sum (fun i _ => hper i)
                _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hTdef, hσdef]
            have Q3 : -(T / s) ≤ 2/5 := by
              have hspos : 0 < s := by linarith only [hs1]
              have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) lam
              simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
              rw [← hTdef, ← hσdef, ← hss] at hcs
              rw [← neg_div, div_le_iff₀ hspos]
              by_contra hc; push_neg at hc
              nlinarith only [hcs, hσc, hspos, hc, mul_pos hspos hspos]
            have Q4 : s * (Real.log N - Real.log n) ≥ Real.log 2 := by
              have hspos : 0 < s := by linarith only [hs1]
              have hs' : 0 < 1/s := one_div_pos.mpr hspos
              have e : (1 + 1/s) * (s*s) = s*s + s := key3 s hspos
              have h1 : 1 + 1/s ≤ N / n := by
                rw [le_div_iff₀ hnpos, hNdef, ← hss, e]; linarith only [mul_le_mul_of_nonneg_right hν hspos.le]
              have h2 : Real.log (1 + 1/s) ≤ Real.log N - Real.log n := by
                rw [← Real.log_div hNpos.ne' hnpos.ne']; exact Real.log_le_log (by linarith only [hs']) h1
              have h3 : (1:ℝ) + s * (1/s) ≤ (1 + 1/s) ^ s := one_add_mul_self_le_rpow_one_add (by linarith only [hs']) hs1
              have h4 : Real.log 2 ≤ s * Real.log (1 + 1/s) := by
                rw [← Real.log_rpow (by linarith only [hs'])]
                apply Real.log_le_log (by norm_num)
                have : (1:ℝ) + s * (1/s) = 2 := by rw [mul_one_div_cancel hspos.ne']; norm_num
                rw [this] at h3; exact h3
              linarith only [mul_le_mul_of_nonneg_left h2 hspos.le, h4]
            have hl2 := Real.log_two_gt_d9
            have hNn : N - n = ν * s := by rw [hNdef]; ring
            have e1 : ν * (-(T/s)) ≤ ν * (2/5) := mul_le_mul_of_nonneg_left Q3 (by linarith only [hν])
            have e2 : ν * (s * (Real.log N - Real.log n)) ≥ ν * Real.log 2 := mul_le_mul_of_nonneg_left Q4 (by linarith only [hν])
            have e3 : (ν - 1) * (Real.log 2 - 2/5) ≥ 0 := mul_nonneg (by linarith only [hν]) (by norm_num at hl2 ⊢; linarith only [hl2])
            have e4 : (N - n) * (Real.log N - Real.log n) = ν * (s * (Real.log N - Real.log n)) := by rw [hNn]; ring
            have h005 : (0.05:ℝ) = 1/20 := by norm_num
            rw [h005]
            linarith only [hmin, L3, Q1, Q2, L2, e1, e2, e3, e4, hl2, hσc]
