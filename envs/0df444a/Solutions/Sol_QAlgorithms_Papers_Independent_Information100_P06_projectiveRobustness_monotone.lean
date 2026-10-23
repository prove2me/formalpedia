-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P06.projectiveRobustness_monotone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:58:54.120201+00:00
-- url     : https://prove2.me/submissions/22df7eb0-674b-41a5-b3cb-e9ec7844e5f4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P06

lemma x8_pos {I J : Type} [Fintype I] [Fintype J]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hPhi : QAlgorithms.Entanglement.IsCompletelyPositive Phi)
    (Y : Matrix I I ℂ) (hY : Y.PosSemidef) : (Phi Y).PosSemidef := by
  have h1 : (Y.submatrix (Prod.snd : Fin 1 × I → I) Prod.snd).PosSemidef := hY.submatrix _
  have h2 := hPhi 1 _ h1
  have h3 : QAlgorithms.idTensorSuperop (R := Fin 1) Phi (Y.submatrix Prod.snd Prod.snd) =
      (Phi Y).submatrix (Prod.snd : Fin 1 × J → J) Prod.snd := by
    ext p q
    simp only [QAlgorithms.idTensorSuperop, Matrix.of_apply, Matrix.submatrix_apply]
    rfl
  rw [h3] at h2
  have h4 := h2.submatrix (fun j : J => ((0 : Fin 1), j))
  simpa [Matrix.submatrix_submatrix] using h4

lemma x8_below_map {I J : Type} [Fintype I] [Fintype J]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) (hPhi : QAlgorithms.Entanglement.IsCompletelyPositive Phi)
    (X Y : Matrix I I ℂ) (h : Below X Y) : Below (Phi X) (Phi Y) := by
  unfold Below at *
  rw [← map_sub]
  exact x8_pos Phi hPhi _ h

lemma x8_main {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (N : Choi A0 A1) (Nout : Choi B0 B1)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    projectiveRobustness G Nout ≤ projectiveRobustness F N := by
  unfold projectiveRobustness
  refine sInf_le_sInf ?_
  rintro g ⟨gamma, lam, rfl, M, hM, h1, h2⟩
  obtain ⟨t, ht, Mout, hMout, hSM⟩ := hfree M hM
  have k1 := x8_below_map _ S.successCP _ _ h1
  have k2 := x8_below_map _ S.successCP _ _ h2
  simp only [map_smul, houtput, hSM] at k1 k2
  unfold Below at k1 k2
  have hpc : (0 : ℂ) ≤ ((p⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.mpr (inv_nonneg.mpr hp.le)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  refine ⟨gamma, Real.toNNReal (lam * t / p), rfl, Mout, hMout, ?_, ?_⟩
  · unfold Below
    have e : ((Real.toNNReal (lam * t / p) : NNReal) : ℂ) • Mout - Nout =
        ((p⁻¹ : ℝ) : ℂ) • ((lam : ℂ) • (t : ℂ) • Mout - (p : ℂ) • Nout) := by
      have : ((Real.toNNReal (lam * t / p) : NNReal) : ℂ) = (lam : ℂ) * t / p := by
        rw [show ((Real.toNNReal (lam * t / p) : NNReal) : ℂ) =
          (((Real.toNNReal (lam * t / p) : NNReal) : ℝ) : ℂ) from rfl,
          Real.coe_toNNReal _ (by positivity)]
        push_cast; ring
      rw [this, smul_sub, smul_smul, smul_smul, smul_smul]
      congr 1
      · congr 1; push_cast; field_simp
      · rw [show ((p⁻¹ : ℝ) : ℂ) * (p : ℂ) = 1 by push_cast; field_simp, one_smul]
    rw [e]
    exact k1.smul hpc
  · unfold Below
    have e : ((gamma : NNReal) : ℂ) • Nout - ((Real.toNNReal (lam * t / p) : NNReal) : ℂ) • Mout =
        ((p⁻¹ : ℝ) : ℂ) • ((gamma : ℂ) • (p : ℂ) • Nout - (lam : ℂ) • (t : ℂ) • Mout) := by
      have : ((Real.toNNReal (lam * t / p) : NNReal) : ℂ) = (lam : ℂ) * t / p := by
        rw [show ((Real.toNNReal (lam * t / p) : NNReal) : ℂ) =
          (((Real.toNNReal (lam * t / p) : NNReal) : ℝ) : ℂ) from rfl,
          Real.coe_toNNReal _ (by positivity)]
        push_cast; ring
      rw [this, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      · congr 1; push_cast; field_simp
      · congr 1; push_cast; field_simp
    rw [e]
    exact k2.smul hpc

end QAlgorithms.Papers.Independent.Information100.P06

open QAlgorithms.Papers.Independent.Information100.P06 in
theorem solution
    {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (N : Choi A0 A1) (Nout : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    projectiveRobustness G Nout ≤ projectiveRobustness F N :=
  x8_main F G N Nout S hfree p hp houtput
