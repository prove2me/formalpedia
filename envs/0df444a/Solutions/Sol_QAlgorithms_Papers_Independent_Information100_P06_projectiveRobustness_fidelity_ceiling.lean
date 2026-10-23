-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P06.projectiveRobustness_fidelity_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:07:32.092964+00:00
-- url     : https://prove2.me/submissions/4920adfd-da06-4705-b539-7c3d9abd649d

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

lemma x8_psd_of_below {I : Type} [Fintype I] (X Y : Matrix I I ℂ) (hX : X.PosSemidef)
    (h : Below X Y) : Y.PosSemidef := by
  have := hX.add h
  simpa using this

lemma x8_below_trans {I : Type} [Fintype I] (X Y Z : Matrix I I ℂ)
    (h1 : Below X Y) (h2 : Below Y Z) : Below X Z := by
  unfold Below at *
  have := h1.add h2
  simpa using this

lemma x8_trace_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [Nonempty I]
    (X : Choi I O) (hX : IsChannelChoi X) : X.trace = 1 := by
  have h := hX.2
  have : X.trace = ∑ i, traceOutput X i i := by
    simp [Matrix.trace, traceOutput, Fintype.sum_prod_type]
  rw [this, h]
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma x8_ge_one {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [Nonempty I]
    (F : FreeSet I O) (N : Choi I O) (hN : IsChannelChoi N) :
    1 ≤ projectiveRobustness F N := by
  unfold projectiveRobustness
  refine le_sInf ?_
  rintro g ⟨gamma, lam, rfl, M, hM, h1, h2⟩
  have h3 := x8_below_trans _ _ _ h1 h2
  unfold Below at h3
  have h4 := h3.trace_nonneg
  have e : ((gamma : ℂ) • N - N).trace = ((gamma : ℂ) - 1) := by
    rw [Matrix.trace_sub, Matrix.trace_smul, x8_trace_one N hN, smul_eq_mul, mul_one]
  rw [e] at h4
  have h5 : (1 : ℝ) ≤ (gamma : ℝ) := by
    have := (Complex.nonneg_iff.mp h4).1
    simpa using this
  have : (1 : NNReal) ≤ gamma := by exact_mod_cast h5
  exact_mod_cast this

lemma x8_cs {I : Type} [Fintype I] (a b : I → ℂ) :
    Complex.normSq (∑ k, star (a k) * b k) ≤
      (∑ k, Complex.normSq (a k)) * (∑ k, Complex.normSq (b k)) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ I) (WithLp.toLp 2 b)
  have e1 : inner ℂ (WithLp.toLp 2 a : EuclideanSpace ℂ I) (WithLp.toLp 2 b) =
      ∑ k, star (a k) * b k := by
    simp [PiLp.inner_apply, mul_comm]
  have e2 : ∀ c : I → ℂ, ‖(WithLp.toLp 2 c : EuclideanSpace ℂ I)‖ ^ 2 = ∑ k, Complex.normSq (c k) := by
    intro c
    rw [EuclideanSpace.norm_sq_eq]
    simp [Complex.normSq_eq_norm_sq]
  rw [e1] at h
  rw [Complex.normSq_eq_norm_sq, ← e2, ← e2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma x8_tr_vv {I : Type} [Fintype I] (a b : I → ℂ) :
    (Matrix.vecMulVec a (star a) * Matrix.vecMulVec b (star b)).trace =
      ((Complex.normSq (∑ k, star (a k) * b k) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.diag, map_sum, map_mul,
    Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma x8_tr_v {I : Type} [Fintype I] (a : I → ℂ) :
    (Matrix.vecMulVec a (star a)).trace = ((∑ k, Complex.normSq (a k) : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.vecMulVec_apply, Complex.mul_conj]

lemma x8_trAB {I : Type} [Fintype I] (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re ∧ (A * B).trace.re ≤ A.trace.re * B.trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨n, w, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB
  have e1 : ((∑ i, Matrix.vecMulVec (v i) (star (v i))) *
      ∑ j, Matrix.vecMulVec (w j) (star (w j))).trace.re =
      ∑ j, ∑ i, Complex.normSq (∑ k, star (v i k) * w j k) := by
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, x8_tr_vv, Complex.re_sum,
      Complex.ofReal_re]
  have e2 : ∀ {r : ℕ} (u : Fin r → I → ℂ), (∑ i, Matrix.vecMulVec (u i) (star (u i))).trace.re =
      ∑ i, ∑ k, Complex.normSq (u i k) := by
    intro r u
    simp only [Matrix.trace_sum, x8_tr_v, Complex.re_sum, Complex.ofReal_re]
  rw [e1, e2, e2]
  refine ⟨Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _, ?_⟩
  rw [mul_comm, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => by
    rw [mul_comm]; exact x8_cs _ _


lemma x8_ep_le {I : Type} [Fintype I] (X Y Φ : Matrix I I ℂ) (hΦ : Φ.PosSemidef)
    (h : Below X Y) : QAlgorithms.effectProb X Φ ≤ QAlgorithms.effectProb Y Φ := by
  unfold QAlgorithms.effectProb
  have := (x8_trAB _ _ h hΦ).1
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma x8_ep_smul {I : Type} [Fintype I] (r : ℝ) (X Φ : Matrix I I ℂ) :
    QAlgorithms.effectProb ((r : ℂ) • X) Φ = r * QAlgorithms.effectProb X Φ := by
  unfold QAlgorithms.effectProb
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma x8_tr_re {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [Nonempty I]
    (X : Choi I O) (hX : IsChannelChoi X) : X.trace.re = 1 := by
  rw [x8_trace_one X hX]; simp

lemma x8_ep_mem {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [Nonempty I]
    (X Φ : Choi I O) (hX : IsChannelChoi X) (hΦ : IsChannelChoi Φ) :
    0 ≤ QAlgorithms.effectProb X Φ ∧ QAlgorithms.effectProb X Φ ≤ 1 := by
  have h := x8_trAB _ _ hX.1 hΦ.1
  rw [x8_tr_re X hX, x8_tr_re Φ hΦ, mul_one] at h
  exact h

lemma x8_nn (a : NNReal) : ((a : ℂ)) = (((a : ℝ)) : ℂ) := rfl

lemma x8_main {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (N : Choi A0 A1) (Nout Phi : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (hPhi : IsChannelChoi Phi)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    QAlgorithms.effectProb Nout Phi ≤
      fidelityCeiling (projectiveRobustness F N) (freeOverlap G Phi) := by
  set x := QAlgorithms.effectProb Nout Phi with hxdef
  obtain ⟨hx0, hx1⟩ := x8_ep_mem Nout Phi hNout hPhi
  set Fv := freeOverlap G Phi with hFv
  have hbdd : BddAbove {v : ℝ | ∃ M ∈ G.carrier, v = QAlgorithms.effectProb M Phi} :=
    ⟨1, by rintro _ ⟨M, hM, rfl⟩; exact (x8_ep_mem M Phi (G.channels M hM) hPhi).2⟩
  have hyF : ∀ M ∈ G.carrier, QAlgorithms.effectProb M Phi ≤ Fv :=
    fun M hM => le_csSup hbdd ⟨M, hM, rfl⟩
  have hF0 : 0 ≤ Fv := by
    obtain ⟨M, hM⟩ := G.nonempty
    exact le_trans (x8_ep_mem M Phi (G.channels M hM) hPhi).1 (hyF M hM)
  have key : ∀ (gamma lam : NNReal) (M : Choi A0 A1), M ∈ F.carrier →
      Below N ((lam : ℂ) • M) → Below ((lam : ℂ) • M) ((gamma : ℂ) • N) →
      x * (1 - Fv) ≤ (gamma : ℝ) * Fv * (1 - x) := by
    intro gamma lam M hM h1 h2
    obtain ⟨t, ht, Mout, hMout, hSM⟩ := hfree M hM
    have k1 := x8_below_map _ S.successCP _ _ h1
    have k2 := x8_below_map _ S.successCP _ _ h2
    simp only [map_smul, houtput, hSM] at k1 k2
    rw [smul_smul, x8_nn, ← Complex.ofReal_mul] at k1 k2
    rw [smul_smul, x8_nn, ← Complex.ofReal_mul] at k2
    set y := QAlgorithms.effectProb Mout Phi with hy
    obtain ⟨hy0, hy1⟩ := x8_ep_mem Mout Phi (G.channels Mout hMout) hPhi
    have hyF' : y ≤ Fv := hyF Mout hMout
    -- p x ≤ λ t y
    have e1 := x8_ep_le _ _ _ hPhi.1 k1
    rw [x8_ep_smul, x8_ep_smul] at e1
    -- λ t (1 - y) ≤ γ p (1 - x)
    have e2 := (x8_trAB _ _ k2 hPhi.1).2
    rw [x8_tr_re Phi hPhi, mul_one, Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_sub, Complex.sub_re] at e2
    have r1 : ∀ (r : ℝ) (X : Choi B0 B1), (((r : ℂ) • X) * Phi).trace.re =
        r * QAlgorithms.effectProb X Phi := fun r X => x8_ep_smul r X Phi
    have r2 : ∀ (r : ℝ) (X : Choi B0 B1), IsChannelChoi X → ((r : ℂ) • X).trace.re = r := by
      intro r X hX
      rw [Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, x8_tr_re X hX, mul_one]
    rw [r1, r1, r2 _ _ hNout, r2 _ _ (G.channels Mout hMout)] at e2
    set c := (lam : ℝ) * t with hc
    have hc0 : 0 ≤ c := mul_nonneg lam.2 ht
    have g0 : (0 : ℝ) ≤ gamma := gamma.2
    -- x (1 - y) ≤ γ y (1 - x)
    have s1 : p * (x * (1 - y)) ≤ p * ((gamma : ℝ) * y * (1 - x)) := by
      have a1 : p * x * (1 - y) ≤ c * y * (1 - y) := mul_le_mul_of_nonneg_right e1 (by linarith)
      have a2 : c * (1 - y) * y ≤ (gamma : ℝ) * p * (1 - x) * y :=
        mul_le_mul_of_nonneg_right (by linarith) hy0
      nlinarith
    have s2 : x * (1 - y) ≤ (gamma : ℝ) * y * (1 - x) := le_of_mul_le_mul_left s1 hp
    have s3 : 0 ≤ (gamma : ℝ) * (1 - x) + x := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hyF' s3]
  unfold fidelityCeiling
  split_ifs with h1 h2
  · exact hx1
  · exact hx1
  · set ω := projectiveRobustness F N with hω
    set w := ω.toReal with hw
    have hge : 1 ≤ w := by
      have := x8_ge_one F N hN
      rw [← hω] at this
      have := ENNReal.toReal_mono h1 this
      simpa using this
    have hlim : x * (1 - Fv) ≤ w * Fv * (1 - x) := by
      have hC : 0 ≤ Fv * (1 - x) := mul_nonneg hF0 (by linarith)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      set ε' := ε / (Fv * (1 - x) + 1) with hε'
      have hε'0 : 0 < ε' := div_pos hε (by linarith)
      have hlt : ω < ENNReal.ofReal (w + ε') := by
        rw [← ENNReal.ofReal_toReal h1, ← hw]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      rw [hω] at hlt
      unfold projectiveRobustness at hlt
      obtain ⟨g, ⟨gamma, lam, rfl, M, hM, a1, a2⟩, hg⟩ := sInf_lt_iff.mp hlt
      have hgam : (gamma : ℝ) < w + ε' := by
        have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ENNReal.ofReal_ne_top).mpr hg
        rwa [ENNReal.coe_toReal, ENNReal.toReal_ofReal (by linarith)] at this
      have k := key gamma lam M hM a1 a2
      have : (gamma : ℝ) * (Fv * (1 - x)) ≤ (w + ε') * (Fv * (1 - x)) :=
        mul_le_mul_of_nonneg_right hgam.le hC
      have hε'C : ε' * (Fv * (1 - x)) ≤ ε := by
        rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      nlinarith
    have hden : 0 < w * Fv + 1 - Fv := by nlinarith
    rw [le_div_iff₀ hden]
    nlinarith

end QAlgorithms.Papers.Independent.Information100.P06

open QAlgorithms.Papers.Independent.Information100.P06 in
theorem solution
    {A0 A1 B0 B1 : Type}
    [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]
    [DecidableEq A0] [DecidableEq B0]
    [Nonempty A0] [Nonempty A1] [Nonempty B0] [Nonempty B1]
    (F : FreeSet A0 A1) (G : FreeSet B0 B1)
    (N : Choi A0 A1) (Nout Phi : Choi B0 B1)
    (hN : IsChannelChoi N) (hNout : IsChannelChoi Nout)
    (hPhi : IsChannelChoi Phi)
    (S : Superinstrument A0 A1 B0 B1) (hfree : IsRNG F G S.success)
    (p : ℝ) (hp : 0 < p) (houtput : S.success N = (p : ℂ) • Nout) :
    QAlgorithms.effectProb Nout Phi ≤ fidelityCeiling (projectiveRobustness F N) (freeOverlap G Phi) :=
  x8_main F G N Nout Phi hN hNout hPhi S hfree p hp houtput
